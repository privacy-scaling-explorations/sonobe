/// This file implements the onchain (Ethereum's EVM) decider circuit. For non-ethereum use cases,
/// other more efficient approaches can be used.
/// More details can be found at the documentation page:
/// https://privacy-scaling-explorations.github.io/sonobe-docs/design/nova-decider-onchain.html
use ark_crypto_primitives::sponge::{
    constraints::CryptographicSpongeVar,
    poseidon::{constraints::PoseidonSpongeVar, PoseidonConfig, PoseidonSponge},
    Absorb, CryptographicSponge,
};
use ark_ec::{CurveGroup, Group};
use ark_ff::{BigInteger, PrimeField};
use ark_poly::Polynomial;
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    boolean::Boolean,
    eq::EqGadget,
    fields::{fp::FpVar, FieldVar},
    poly::{domain::Radix2DomainVar, evaluations::univariate::EvaluationsVar},
    prelude::CurveVar,
    ToConstraintFieldGadget,
};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, Namespace, SynthesisError};
use ark_std::{log2, Zero};
use core::{borrow::Borrow, marker::PhantomData};

use super::{
    circuits::{ChallengeGadget, CommittedInstanceVar},
    nifs::{nova::NIFS, NIFSTrait},
    CommittedInstance, Nova, Witness,
};
use crate::folding::circuits::{
    cyclefold::{CycleFoldCommittedInstance, CycleFoldWitness},
    nonnative::{affine::NonNativeAffineVar, uint::NonNativeUintVar},
    CF1, CF2,
};
use crate::folding::traits::{CommittedInstanceVarOps, Dummy, WitnessVarOps};
use crate::frontend::FCircuit;
use crate::transcript::{Transcript, TranscriptVar};
use crate::utils::vec::poly_from_vec;
use crate::Error;
use crate::{
    arith::{
        r1cs::{circuits::R1CSMatricesVar, R1CS},
        ArithGadget,
    },
    commitment::{pedersen::Params as PedersenParams, CommitmentScheme},
};

/// In-circuit representation of the Witness associated to the CommittedInstance.
#[derive(Debug, Clone)]
pub struct WitnessVar<C: CurveGroup> {
    pub E: Vec<FpVar<C::ScalarField>>,
    pub rE: FpVar<C::ScalarField>,
    pub W: Vec<FpVar<C::ScalarField>>,
    pub rW: FpVar<C::ScalarField>,
}

impl<C> AllocVar<Witness<C>, CF1<C>> for WitnessVar<C>
where
    C: CurveGroup,
{
    fn new_variable<T: Borrow<Witness<C>>>(
        cs: impl Into<Namespace<CF1<C>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|val| {
            let cs = cs.into();

            let E: Vec<FpVar<C::ScalarField>> =
                Vec::new_variable(cs.clone(), || Ok(val.borrow().E.clone()), mode)?;
            let rE =
                FpVar::<C::ScalarField>::new_variable(cs.clone(), || Ok(val.borrow().rE), mode)?;

            let W: Vec<FpVar<C::ScalarField>> =
                Vec::new_variable(cs.clone(), || Ok(val.borrow().W.clone()), mode)?;
            let rW =
                FpVar::<C::ScalarField>::new_variable(cs.clone(), || Ok(val.borrow().rW), mode)?;

            Ok(Self { E, rE, W, rW })
        })
    }
}

impl<C: CurveGroup> WitnessVarOps<C::ScalarField> for WitnessVar<C> {
    fn get_openings(&self) -> Vec<(&[FpVar<C::ScalarField>], FpVar<C::ScalarField>)> {
        vec![(&self.E, self.rE.clone()), (&self.W, self.rW.clone())]
    }
}

/// Circuit that implements the in-circuit checks needed for the onchain (Ethereum's EVM)
/// verification.
#[derive(Clone, Debug)]
pub struct DeciderEthCircuit<C1, GC1, C2, GC2, CS1, CS2, const H: bool = false>
where
    C1: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>>,
    C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>>,
    CS1: CommitmentScheme<C1, H>,
    CS2: CommitmentScheme<C2, H>,
{
    _c1: PhantomData<C1>,
    _gc1: PhantomData<GC1>,
    _c2: PhantomData<C2>,
    _gc2: PhantomData<GC2>,
    _cs1: PhantomData<CS1>,
    _cs2: PhantomData<CS2>,

    /// E vector's length of the Nova instance witness
    pub E_len: usize,
    /// E vector's length of the CycleFold instance witness
    pub cf_E_len: usize,
    /// R1CS of the Augmented Function circuit
    pub r1cs: R1CS<C1::ScalarField>,
    /// R1CS of the CycleFold circuit
    pub cf_r1cs: R1CS<C2::ScalarField>,
    /// CycleFold PedersenParams over C2
    pub cf_pedersen_params: PedersenParams<C2>,
    pub poseidon_config: PoseidonConfig<CF1<C1>>,
    /// public params hash
    pub pp_hash: Option<C1::ScalarField>,
    pub i: Option<CF1<C1>>,
    /// initial state
    pub z_0: Option<Vec<C1::ScalarField>>,
    /// current i-th state
    pub z_i: Option<Vec<C1::ScalarField>>,
    /// Nova instances
    pub u_i: Option<CommittedInstance<C1>>,
    pub w_i: Option<Witness<C1>>,
    pub U_i: Option<CommittedInstance<C1>>,
    pub W_i: Option<Witness<C1>>,
    pub U_i1: Option<CommittedInstance<C1>>,
    pub W_i1: Option<Witness<C1>>,
    pub cmT: Option<C1>,
    pub r: Option<C1::ScalarField>,
    /// CycleFold running instance
    pub cf_U_i: Option<CycleFoldCommittedInstance<C2>>,
    pub cf_W_i: Option<CycleFoldWitness<C2>>,

    /// KZG challenges
    pub kzg_c_W: Option<C1::ScalarField>,
    pub kzg_c_E: Option<C1::ScalarField>,
    pub eval_W: Option<C1::ScalarField>,
    pub eval_E: Option<C1::ScalarField>,
}
impl<C1, GC1, C2, GC2, CS1, CS2, const H: bool> DeciderEthCircuit<C1, GC1, C2, GC2, CS1, CS2, H>
where
    C1: CurveGroup,
    C2: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
    CS1: CommitmentScheme<C1, H>,
    // enforce that the CS2 is Pedersen commitment scheme, since we're at Ethereum's EVM decider
    CS2: CommitmentScheme<C2, H, ProverParams = PedersenParams<C2>>,
    <C1 as Group>::ScalarField: Absorb,
    <C1 as CurveGroup>::BaseField: PrimeField,
{
    /// returns an instance of the DeciderEthCircuit from the given Nova struct
    pub fn from_nova<FC: FCircuit<C1::ScalarField>>(
        nova: Nova<C1, GC1, C2, GC2, FC, CS1, CS2, H>,
    ) -> Result<Self, Error> {
        let mut transcript = PoseidonSponge::<C1::ScalarField>::new(&nova.poseidon_config);

        // compute the U_{i+1}, W_{i+1}
        let (W_i1, U_i1, cmT, r_bits) = NIFS::<C1, CS1, PoseidonSponge<C1::ScalarField>, H>::prove(
            &nova.cs_pp,
            &nova.r1cs.clone(),
            &mut transcript,
            nova.pp_hash,
            &nova.W_i,
            &nova.U_i,
            &nova.w_i,
            &nova.u_i,
        )?;
        let r_Fr = C1::ScalarField::from_bigint(BigInteger::from_bits_le(&r_bits))
            .ok_or(Error::OutOfBounds)?;

        // compute the KZG challenges used as inputs in the circuit
        let (kzg_challenge_W, kzg_challenge_E) =
            KZGChallengesGadget::<C1>::get_challenges_native(&mut transcript, U_i1.clone());

        // get KZG evals
        let mut W = W_i1.W.clone();
        W.extend(
            std::iter::repeat(C1::ScalarField::zero())
                .take(W_i1.W.len().next_power_of_two() - W_i1.W.len()),
        );
        let mut E = W_i1.E.clone();
        E.extend(
            std::iter::repeat(C1::ScalarField::zero())
                .take(W_i1.E.len().next_power_of_two() - W_i1.E.len()),
        );
        let p_W = poly_from_vec(W.to_vec())?;
        let eval_W = p_W.evaluate(&kzg_challenge_W);
        let p_E = poly_from_vec(E.to_vec())?;
        let eval_E = p_E.evaluate(&kzg_challenge_E);

        Ok(Self {
            _c1: PhantomData,
            _gc1: PhantomData,
            _c2: PhantomData,
            _gc2: PhantomData,
            _cs1: PhantomData,
            _cs2: PhantomData,

            E_len: nova.W_i.E.len(),
            cf_E_len: nova.cf_W_i.E.len(),
            r1cs: nova.r1cs,
            cf_r1cs: nova.cf_r1cs,
            cf_pedersen_params: nova.cf_cs_pp,
            poseidon_config: nova.poseidon_config,
            pp_hash: Some(nova.pp_hash),
            i: Some(nova.i),
            z_0: Some(nova.z_0),
            z_i: Some(nova.z_i),
            u_i: Some(nova.u_i),
            w_i: Some(nova.w_i),
            U_i: Some(nova.U_i),
            W_i: Some(nova.W_i),
            U_i1: Some(U_i1),
            W_i1: Some(W_i1),
            cmT: Some(cmT),
            r: Some(r_Fr),
            cf_U_i: Some(nova.cf_U_i),
            cf_W_i: Some(nova.cf_W_i),
            kzg_c_W: Some(kzg_challenge_W),
            kzg_c_E: Some(kzg_challenge_E),
            eval_W: Some(eval_W),
            eval_E: Some(eval_E),
        })
    }
}

impl<C1, GC1, C2, GC2, CS1, CS2> ConstraintSynthesizer<CF1<C1>>
    for DeciderEthCircuit<C1, GC1, C2, GC2, CS1, CS2>
where
    C1: CurveGroup,
    C2: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>>,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
    CS1: CommitmentScheme<C1>,
    CS2: CommitmentScheme<C2>,
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    <C2 as Group>::ScalarField: Absorb,
    C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
{
    fn generate_constraints(self, cs: ConstraintSystemRef<CF1<C1>>) -> Result<(), SynthesisError> {
        let r1cs =
            R1CSMatricesVar::<C1::ScalarField, FpVar<CF1<C1>>>::new_witness(cs.clone(), || {
                Ok(self.r1cs.clone())
            })?;

        let pp_hash = FpVar::<CF1<C1>>::new_input(cs.clone(), || {
            Ok(self.pp_hash.unwrap_or_else(CF1::<C1>::zero))
        })?;
        let i =
            FpVar::<CF1<C1>>::new_input(cs.clone(), || Ok(self.i.unwrap_or_else(CF1::<C1>::zero)))?;
        let z_0 = Vec::<FpVar<CF1<C1>>>::new_input(cs.clone(), || {
            Ok(self.z_0.unwrap_or(vec![CF1::<C1>::zero()]))
        })?;
        let z_i = Vec::<FpVar<CF1<C1>>>::new_input(cs.clone(), || {
            Ok(self.z_i.unwrap_or(vec![CF1::<C1>::zero()]))
        })?;

        let u_dummy_native = CommittedInstance::<C1>::dummy(&self.r1cs);
        let w_dummy_native = Witness::<C1>::dummy(&self.r1cs);

        let u_i = CommittedInstanceVar::<C1>::new_witness(cs.clone(), || {
            Ok(self.u_i.unwrap_or(u_dummy_native.clone()))
        })?;
        let U_i = CommittedInstanceVar::<C1>::new_witness(cs.clone(), || {
            Ok(self.U_i.unwrap_or(u_dummy_native.clone()))
        })?;
        // here (U_i1, W_i1) = NIFS.P( (U_i,W_i), (u_i,w_i))
        let U_i1 = CommittedInstanceVar::<C1>::new_input(cs.clone(), || {
            Ok(self.U_i1.unwrap_or(u_dummy_native.clone()))
        })?;
        let W_i1 = WitnessVar::<C1>::new_witness(cs.clone(), || {
            Ok(self.W_i1.unwrap_or(w_dummy_native.clone()))
        })?;

        // allocate the inputs for the check 5.1
        let kzg_c_W = FpVar::<CF1<C1>>::new_input(cs.clone(), || {
            Ok(self.kzg_c_W.unwrap_or_else(CF1::<C1>::zero))
        })?;
        let kzg_c_E = FpVar::<CF1<C1>>::new_input(cs.clone(), || {
            Ok(self.kzg_c_E.unwrap_or_else(CF1::<C1>::zero))
        })?;
        // allocate the inputs for the check 5.2
        let eval_W = FpVar::<CF1<C1>>::new_input(cs.clone(), || {
            Ok(self.eval_W.unwrap_or_else(CF1::<C1>::zero))
        })?;
        let eval_E = FpVar::<CF1<C1>>::new_input(cs.clone(), || {
            Ok(self.eval_E.unwrap_or_else(CF1::<C1>::zero))
        })?;

        // `sponge` is for digest computation.
        let sponge = PoseidonSpongeVar::<C1::ScalarField>::new(cs.clone(), &self.poseidon_config);
        // `transcript` is for challenge generation.
        let mut transcript = sponge.clone();

        // The following enumeration of the steps matches the one used at the documentation page
        // https://privacy-scaling-explorations.github.io/sonobe-docs/design/nova-decider-onchain.html

        // 2. u_i.cmE==cm(0), u_i.u==1
        // Here zero is the x & y coordinates of the zero point affine representation.
        let zero = NonNativeUintVar::new_constant(cs.clone(), C1::BaseField::zero())?;
        u_i.cmE.x.enforce_equal_unaligned(&zero)?;
        u_i.cmE.y.enforce_equal_unaligned(&zero)?;
        (u_i.u.is_one()?).enforce_equal(&Boolean::TRUE)?;

        // 3.a u_i.x[0] == H(i, z_0, z_i, U_i)
        let (u_i_x, U_i_vec) = U_i.clone().hash(&sponge, &pp_hash, &i, &z_0, &z_i)?;
        (u_i.x[0]).enforce_equal(&u_i_x)?;

        // 4. check RelaxedR1CS of U_{i+1}
        r1cs.enforce_relation(&W_i1, &U_i1)?;

        #[cfg(feature = "light-test")]
        log::warn!("[WARNING]: Running with the 'light-test' feature, skipping the big part of the DeciderEthCircuit.\n           Only for testing purposes.");

        // The following two checks (and their respective allocations) are disabled for normal
        // tests since they take several millions of constraints and would take several minutes
        // (and RAM) to run the test. It is active by default, and not active only when
        // 'light-test' feature is used.
        #[cfg(not(feature = "light-test"))]
        {
            // imports here instead of at the top of the file, so we avoid having multiple
            // `#[cfg(not(test))]`
            use crate::commitment::pedersen::PedersenGadget;
            use crate::folding::{
                circuits::cyclefold::{
                    CycleFoldCommittedInstanceVar, CycleFoldConfig, CycleFoldWitnessVar,
                },
                nova::NovaCycleFoldConfig,
            };
            use ark_r1cs_std::ToBitsGadget;

            let cf_u_dummy_native =
                CycleFoldCommittedInstance::<C2>::dummy(NovaCycleFoldConfig::<C1>::IO_LEN);
            let w_dummy_native = CycleFoldWitness::<C2>::dummy(&self.cf_r1cs);
            let cf_U_i = CycleFoldCommittedInstanceVar::<C2, GC2>::new_witness(cs.clone(), || {
                Ok(self.cf_U_i.unwrap_or_else(|| cf_u_dummy_native.clone()))
            })?;
            let cf_W_i = CycleFoldWitnessVar::<C2>::new_witness(cs.clone(), || {
                Ok(self.cf_W_i.unwrap_or(w_dummy_native.clone()))
            })?;

            // 3.b u_i.x[1] == H(cf_U_i)
            let (cf_u_i_x, _) = cf_U_i.clone().hash(&sponge, pp_hash.clone())?;
            (u_i.x[1]).enforce_equal(&cf_u_i_x)?;

            // 7. check Pedersen commitments of cf_U_i.{cmE, cmW}
            let H = GC2::new_constant(cs.clone(), self.cf_pedersen_params.h)?;
            let G = Vec::<GC2>::new_constant(cs.clone(), self.cf_pedersen_params.generators)?;
            let cf_W_i_E_bits: Result<Vec<Vec<Boolean<CF1<C1>>>>, SynthesisError> =
                cf_W_i.E.iter().map(|E_i| E_i.to_bits_le()).collect();
            let cf_W_i_W_bits: Result<Vec<Vec<Boolean<CF1<C1>>>>, SynthesisError> =
                cf_W_i.W.iter().map(|W_i| W_i.to_bits_le()).collect();

            let computed_cmE = PedersenGadget::<C2, GC2>::commit(
                H.clone(),
                G.clone(),
                cf_W_i_E_bits?,
                cf_W_i.rE.to_bits_le()?,
            )?;
            cf_U_i.cmE.enforce_equal(&computed_cmE)?;
            let computed_cmW =
                PedersenGadget::<C2, GC2>::commit(H, G, cf_W_i_W_bits?, cf_W_i.rW.to_bits_le()?)?;
            cf_U_i.cmW.enforce_equal(&computed_cmW)?;

            let cf_r1cs = R1CSMatricesVar::<C1::BaseField, NonNativeUintVar<CF1<C1>>>::new_witness(
                cs.clone(),
                || Ok(self.cf_r1cs.clone()),
            )?;

            // 6. check RelaxedR1CS of cf_U_i (CycleFold instance)
            cf_r1cs.enforce_relation(&cf_W_i, &cf_U_i)?;
        }

        // 1.1.a, 5.1. compute NIFS.V and KZG challenges.
        // We need to ensure the order of challenge generation is the same as
        // the native counterpart, so we first compute the challenges here and
        // do the actual checks later.
        let cmT =
            NonNativeAffineVar::new_input(cs.clone(), || Ok(self.cmT.unwrap_or_else(C1::zero)))?;
        // 1.1.a
        let r_bits = ChallengeGadget::<C1, CommittedInstance<C1>>::get_challenge_gadget(
            &mut transcript,
            pp_hash,
            U_i_vec,
            u_i.clone(),
            Some(cmT),
        )?;
        // 5.1.
        let (incircuit_c_W, incircuit_c_E) =
            KZGChallengesGadget::<C1>::get_challenges_gadget(&mut transcript, U_i1.clone())?;
        incircuit_c_W.enforce_equal(&kzg_c_W)?;
        incircuit_c_E.enforce_equal(&kzg_c_E)?;

        // 5.2. check eval_W==p_W(c_W) and eval_E==p_E(c_E)
        let incircuit_eval_W = evaluate_gadget::<CF1<C1>>(W_i1.W, incircuit_c_W)?;
        let incircuit_eval_E = evaluate_gadget::<CF1<C1>>(W_i1.E, incircuit_c_E)?;
        incircuit_eval_W.enforce_equal(&eval_W)?;
        incircuit_eval_E.enforce_equal(&eval_E)?;

        // 1.1.b check that the NIFS.V challenge matches the one from the public input (so we avoid
        //   the verifier computing it)
        let r_Fr = Boolean::le_bits_to_fp_var(&r_bits)?;
        // check that the in-circuit computed r is equal to the inputted r
        let r =
            FpVar::<CF1<C1>>::new_input(cs.clone(), || Ok(self.r.unwrap_or_else(CF1::<C1>::zero)))?;
        r_Fr.enforce_equal(&r)?;

        Ok(())
    }
}

/// Interpolates the polynomial from the given vector, and then returns it's evaluation at the
/// given point.
#[allow(unused)] // unused while check 7 is disabled
pub fn evaluate_gadget<F: PrimeField>(
    mut v: Vec<FpVar<F>>,
    point: FpVar<F>,
) -> Result<FpVar<F>, SynthesisError> {
    v.resize(v.len().next_power_of_two(), FpVar::zero());
    let n = v.len() as u64;
    let gen = F::get_root_of_unity(n).unwrap();
    let domain = Radix2DomainVar::new(gen, log2(v.len()) as u64, FpVar::one()).unwrap();

    let evaluations_var = EvaluationsVar::from_vec_and_domain(v, domain, true);
    evaluations_var.interpolate_and_evaluate(&point)
}

/// Gadget that computes the KZG challenges, also offers the rust native implementation compatible
/// with the gadget.
pub struct KZGChallengesGadget<C: CurveGroup> {
    _c: PhantomData<C>,
}
#[allow(clippy::type_complexity)]
impl<C> KZGChallengesGadget<C>
where
    C: CurveGroup,
    C::ScalarField: PrimeField,
    <C as CurveGroup>::BaseField: PrimeField,
    C::ScalarField: Absorb,
{
    pub fn get_challenges_native<T: Transcript<C::ScalarField>>(
        transcript: &mut T,
        U_i: CommittedInstance<C>,
    ) -> (C::ScalarField, C::ScalarField) {
        // compute the KZG challenges, which are computed in-circuit and checked that it matches
        // the inputted one
        transcript.absorb_nonnative(&U_i.cmW);
        let challenge_W = transcript.get_challenge();
        transcript.absorb_nonnative(&U_i.cmE);
        let challenge_E = transcript.get_challenge();

        (challenge_W, challenge_E)
    }
    // compatible with the native get_challenges_native
    pub fn get_challenges_gadget<S: CryptographicSponge, T: TranscriptVar<CF1<C>, S>>(
        transcript: &mut T,
        U_i: CommittedInstanceVar<C>,
    ) -> Result<(FpVar<C::ScalarField>, FpVar<C::ScalarField>), SynthesisError> {
        transcript.absorb(&U_i.cmW.to_constraint_field()?)?;
        let challenge_W = transcript.get_challenge()?;

        transcript.absorb(&U_i.cmE.to_constraint_field()?)?;
        let challenge_E = transcript.get_challenge()?;

        Ok((challenge_W, challenge_E))
    }
}

#[cfg(test)]
pub mod tests {
    use ark_pallas::{constraints::GVar, Fr, Projective};
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::UniformRand;
    use ark_vesta::{constraints::GVar as GVar2, Projective as Projective2};

    use super::*;
    use crate::commitment::pedersen::Pedersen;
    use crate::folding::nova::PreprocessorParam;
    use crate::frontend::utils::CubicFCircuit;
    use crate::transcript::poseidon::poseidon_canonical_config;
    use crate::FoldingScheme;

    #[test]
    fn test_decider_eth_circuit() {
        let mut rng = ark_std::test_rng();
        let poseidon_config = poseidon_canonical_config::<Fr>();

        let F_circuit = CubicFCircuit::<Fr>::new(()).unwrap();
        let z_0 = vec![Fr::from(3_u32)];

        type N = Nova<
            Projective,
            GVar,
            Projective2,
            GVar2,
            CubicFCircuit<Fr>,
            Pedersen<Projective>,
            Pedersen<Projective2>,
            false,
        >;

        let prep_param = PreprocessorParam::<
            Projective,
            Projective2,
            CubicFCircuit<Fr>,
            Pedersen<Projective>,
            Pedersen<Projective2>,
            false,
        >::new(poseidon_config, F_circuit);
        let nova_params = N::preprocess(&mut rng, &prep_param).unwrap();

        // generate a Nova instance and do a step of it
        let mut nova = N::init(&nova_params, F_circuit, z_0.clone()).unwrap();
        nova.prove_step(&mut rng, vec![], None).unwrap();
        let ivc_proof = nova.ivc_proof();
        N::verify(nova_params.1, ivc_proof).unwrap();

        // load the DeciderEthCircuit from the Nova instance
        let decider_eth_circuit = DeciderEthCircuit::<
            Projective,
            GVar,
            Projective2,
            GVar2,
            Pedersen<Projective>,
            Pedersen<Projective2>,
        >::from_nova(nova)
        .unwrap();

        let cs = ConstraintSystem::<Fr>::new_ref();

        // generate the constraints and check that are satisfied by the inputs
        decider_eth_circuit
            .generate_constraints(cs.clone())
            .unwrap();
        assert!(cs.is_satisfied().unwrap());
    }

    // checks that the gadget and native implementations of the challenge computation match
    #[test]
    fn test_kzg_challenge_gadget() {
        let mut rng = ark_std::test_rng();
        let poseidon_config = poseidon_canonical_config::<Fr>();
        let mut transcript = PoseidonSponge::<Fr>::new(&poseidon_config);

        let U_i = CommittedInstance::<Projective> {
            cmE: Projective::rand(&mut rng),
            u: Fr::rand(&mut rng),
            cmW: Projective::rand(&mut rng),
            x: vec![Fr::rand(&mut rng); 1],
        };

        // compute the challenge natively
        let (challenge_W, challenge_E) =
            KZGChallengesGadget::<Projective>::get_challenges_native(&mut transcript, U_i.clone());

        let cs = ConstraintSystem::<Fr>::new_ref();
        let U_iVar =
            CommittedInstanceVar::<Projective>::new_witness(cs.clone(), || Ok(U_i.clone()))
                .unwrap();
        let mut transcript_var = PoseidonSpongeVar::<Fr>::new(cs.clone(), &poseidon_config);

        let (challenge_W_Var, challenge_E_Var) =
            KZGChallengesGadget::<Projective>::get_challenges_gadget(&mut transcript_var, U_iVar)
                .unwrap();
        assert!(cs.is_satisfied().unwrap());

        // check that the natively computed and in-circuit computed hashes match
        use ark_r1cs_std::R1CSVar;
        assert_eq!(challenge_W_Var.value().unwrap(), challenge_W);
        assert_eq!(challenge_E_Var.value().unwrap(), challenge_E);
    }

    #[test]
    fn test_polynomial_interpolation() {
        let mut rng = ark_std::test_rng();
        let n = 12;
        let l = 1 << n;

        let v: Vec<Fr> = std::iter::repeat_with(|| Fr::rand(&mut rng))
            .take(l)
            .collect();
        let challenge = Fr::rand(&mut rng);

        use ark_poly::Polynomial;
        let polynomial = poly_from_vec(v.to_vec()).unwrap();
        let eval = polynomial.evaluate(&challenge);

        let cs = ConstraintSystem::<Fr>::new_ref();
        let vVar = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(v)).unwrap();
        let challengeVar = FpVar::<Fr>::new_witness(cs.clone(), || Ok(challenge)).unwrap();

        let evalVar = evaluate_gadget::<Fr>(vVar, challengeVar).unwrap();

        use ark_r1cs_std::R1CSVar;
        assert_eq!(evalVar.value().unwrap(), eval);
        assert!(cs.is_satisfied().unwrap());
    }
}
