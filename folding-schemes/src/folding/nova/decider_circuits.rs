/// This file implements the offchain decider circuit. For ethereum use cases, use the
/// DeciderEthCircuit.
/// More details can be found at the documentation page:
/// https://privacy-scaling-explorations.github.io/sonobe-docs/design/nova-decider-offchain.html
use ark_crypto_primitives::sponge::{
    constraints::CryptographicSpongeVar,
    poseidon::{constraints::PoseidonSpongeVar, PoseidonConfig, PoseidonSponge},
    Absorb, CryptographicSponge,
};
use ark_ec::{CurveGroup, Group};
use ark_ff::{BigInteger, PrimeField};
use ark_poly::Polynomial;
use ark_r1cs_std::{
    alloc::AllocVar,
    boolean::Boolean,
    eq::EqGadget,
    fields::{fp::FpVar, FieldVar},
    groups::GroupOpsBounds,
    prelude::CurveVar,
    ToConstraintFieldGadget,
};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_std::Zero;
use core::marker::PhantomData;

use super::{
    circuits::{ChallengeGadget, CommittedInstanceVar},
    decider_eth_circuit::{
        evaluate_gadget, KZGChallengesGadget, R1CSVar, RelaxedR1CSGadget, WitnessVar,
    },
    nifs::NIFS,
    traits::NIFSTrait,
    CommittedInstance, Nova, Witness,
};
use crate::arith::r1cs::R1CS;
use crate::commitment::CommitmentScheme;
use crate::folding::circuits::{
    cyclefold::{
        CycleFoldCommittedInstance, CycleFoldCommittedInstanceVar, CycleFoldConfig,
        CycleFoldWitness,
    },
    nonnative::{affine::NonNativeAffineVar, uint::NonNativeUintVar},
    CF1, CF2,
};
use crate::folding::nova::NovaCycleFoldConfig;
use crate::folding::traits::{CommittedInstanceVarOps, Dummy};
use crate::frontend::FCircuit;
use crate::utils::vec::poly_from_vec;
use crate::Error;

/// Circuit that implements part of the in-circuit checks needed for the offchain verification over
/// the Curve2's BaseField (=Curve1's ScalarField).
#[derive(Clone, Debug)]
pub struct DeciderCircuit1<C1, C2, GC2>
where
    C1: CurveGroup,
    C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>>,
{
    _c1: PhantomData<C1>,
    _c2: PhantomData<C2>,
    _gc2: PhantomData<GC2>,

    /// E vector's length of the Nova instance witness
    pub E_len: usize,
    /// E vector's length of the CycleFold instance witness
    pub cf_E_len: usize,
    /// R1CS of the Augmented Function circuit
    pub r1cs: R1CS<C1::ScalarField>,
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

    /// Commitment Scheme challenges
    pub cs_c_W: Option<C1::ScalarField>,
    pub cs_c_E: Option<C1::ScalarField>,
    /// Evaluations of the committed polynomials at the challenge
    pub eval_W: Option<C1::ScalarField>,
    pub eval_E: Option<C1::ScalarField>,
}
impl<C1, C2, GC2> DeciderCircuit1<C1, C2, GC2>
where
    C1: CurveGroup,
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
    for<'b> &'b GC2: GroupOpsBounds<'b, C2, GC2>,
{
    pub fn from_nova<GC1, CS1, CS2, const H: bool, FC: FCircuit<C1::ScalarField>>(
        nova: Nova<C1, GC1, C2, GC2, FC, CS1, CS2, H>,
    ) -> Result<Self, Error>
    where
        C2: CurveGroup,
        GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
        GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
        CS1: CommitmentScheme<C1, H>,
        CS2: CommitmentScheme<C2, H>,
    {
        let mut transcript = PoseidonSponge::<C1::ScalarField>::new(&nova.poseidon_config);
        // pp_hash is absorbed to transcript at the ChallengeGadget::get_challenge_native call

        // compute the U_{i+1}, W_{i+1}
        let (T, cmT) = NIFS::<C1, CS1, H>::compute_cmT(
            &nova.cs_pp,
            &nova.r1cs.clone(),
            &nova.w_i.clone(),
            &nova.u_i.clone(),
            &nova.W_i.clone(),
            &nova.U_i.clone(),
        )?;
        let r_bits = NIFS::<C1, CS1, H>::get_challenge(
            &mut transcript,
            nova.pp_hash,
            &nova.U_i,
            &nova.u_i,
            &cmT,
        );
        let r_Fr = C1::ScalarField::from_bigint(BigInteger::from_bits_le(&r_bits))
            .ok_or(Error::OutOfBounds)?;
        let (W_i1, U_i1) =
            NIFS::<C1, CS1, H>::prove(r_Fr, &nova.W_i, &nova.U_i, &nova.w_i, &nova.u_i, &T, &cmT)?;

        // compute the commitment scheme challenges used as inputs in the circuit
        let (cs_challenge_W, cs_challenge_E) =
            KZGChallengesGadget::<C1>::get_challenges_native(&mut transcript, U_i1.clone());

        // get evals of the committed polys at the challenges
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
        let eval_W = p_W.evaluate(&cs_challenge_W);
        let p_E = poly_from_vec(E.to_vec())?;
        let eval_E = p_E.evaluate(&cs_challenge_E);

        Ok(Self {
            _c1: PhantomData,
            _c2: PhantomData,
            _gc2: PhantomData,

            E_len: nova.W_i.E.len(),
            cf_E_len: nova.cf_W_i.E.len(),
            r1cs: nova.r1cs,
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
            cs_c_W: Some(cs_challenge_W),
            cs_c_E: Some(cs_challenge_E),
            eval_W: Some(eval_W),
            eval_E: Some(eval_E),
        })
    }
}

impl<C1, C2, GC2> ConstraintSynthesizer<CF1<C1>> for DeciderCircuit1<C1, C2, GC2>
where
    C1: CurveGroup,
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    C2: CurveGroup,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C2 as Group>::ScalarField: Absorb,
    C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
    for<'b> &'b GC2: GroupOpsBounds<'b, C2, GC2>,
{
    fn generate_constraints(self, cs: ConstraintSystemRef<CF1<C1>>) -> Result<(), SynthesisError> {
        let r1cs =
            R1CSVar::<C1::ScalarField, CF1<C1>, FpVar<CF1<C1>>>::new_witness(cs.clone(), || {
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

        // allocate the inputs for the check 6
        let cs_c_W = FpVar::<CF1<C1>>::new_input(cs.clone(), || {
            Ok(self.cs_c_W.unwrap_or_else(CF1::<C1>::zero))
        })?;
        let cs_c_E = FpVar::<CF1<C1>>::new_input(cs.clone(), || {
            Ok(self.cs_c_E.unwrap_or_else(CF1::<C1>::zero))
        })?;
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
        // notice that the `pp_hash` is absorbed inside the ChallengeGadget::get_challenge_gadget call

        // 2. u_i.cmE==cm(0), u_i.u==1
        // Here zero is the x & y coordinates of the zero point affine representation.
        let zero = NonNativeUintVar::new_constant(cs.clone(), C1::BaseField::zero())?;
        u_i.cmE.x.enforce_equal_unaligned(&zero)?;
        u_i.cmE.y.enforce_equal_unaligned(&zero)?;
        (u_i.u.is_one()?).enforce_equal(&Boolean::TRUE)?;

        // 3.a u_i.x[0] == H(i, z_0, z_i, U_i)
        let (u_i_x, U_i_vec) = U_i.clone().hash(&sponge, &pp_hash, &i, &z_0, &z_i)?;
        (u_i.x[0]).enforce_equal(&u_i_x)?;

        // 3.b u_i.x[1] == H(cf_U_i)
        let cf_u_dummy_native =
            CycleFoldCommittedInstance::<C2>::dummy(NovaCycleFoldConfig::<C1>::IO_LEN);
        let cf_U_i = CycleFoldCommittedInstanceVar::<C2, GC2>::new_input(cs.clone(), || {
            Ok(self.cf_U_i.unwrap_or_else(|| cf_u_dummy_native.clone()))
        })?;
        let (cf_u_i_x, _) = cf_U_i.clone().hash(&sponge, pp_hash.clone())?;
        (u_i.x[1]).enforce_equal(&cf_u_i_x)?;

        // 4. check RelaxedR1CS of U_{i+1}
        let z_U1: Vec<FpVar<CF1<C1>>> =
            [vec![U_i1.u.clone()], U_i1.x.to_vec(), W_i1.W.to_vec()].concat();
        RelaxedR1CSGadget::check_native(r1cs, W_i1.E.clone(), U_i1.u.clone(), z_U1)?;

        // 1.1.a, 5.1 compute NIFS.V and Commitment Scheme challenges.
        // We need to ensure the order of challenge generation is the same as
        // the native counterpart, so we first compute the challenges here and
        // do the actual checks later.
        let cmT =
            NonNativeAffineVar::new_input(cs.clone(), || Ok(self.cmT.unwrap_or_else(C1::zero)))?;
        let r_bits = ChallengeGadget::<C1, CommittedInstance<C1>>::get_challenge_gadget(
            &mut transcript,
            pp_hash,
            U_i_vec,
            u_i.clone(),
            Some(cmT.clone()),
        )?;
        // 5.1.
        let (incircuit_c_W, incircuit_c_E) =
            KZGChallengesGadget::<C1>::get_challenges_gadget(&mut transcript, U_i1.clone())?;
        incircuit_c_W.enforce_equal(&cs_c_W)?;
        incircuit_c_E.enforce_equal(&cs_c_E)?;

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

/// Circuit that implements part of the in-circuit checks needed for the offchain verification over
/// the Curve1's BaseField (=Curve2's ScalarField).
#[derive(Clone, Debug)]
pub struct DeciderCircuit2<C1, GC1, C2>
where
    C1: CurveGroup,
    C2: CurveGroup,
{
    _c1: PhantomData<C1>,
    _gc1: PhantomData<GC1>,
    _c2: PhantomData<C2>,

    /// E vector's length of the CycleFold instance witness
    pub cf_E_len: usize,
    /// R1CS of the CycleFold circuit
    pub cf_r1cs: R1CS<C2::ScalarField>,
    pub poseidon_config: PoseidonConfig<CF1<C2>>,
    /// public params hash
    pub pp_hash: Option<C2::ScalarField>,

    /// CycleFold running instance. Notice that here we use Nova's CommittedInstance (instead of
    /// CycleFoldCommittedInstance), since we are over C2::Fr, so that the CycleFold instances can
    /// be computed natively
    pub cf_U_i: Option<CommittedInstance<C2>>,
    pub cf_W_i: Option<CycleFoldWitness<C2>>,
    /// Commitment Scheme challenges
    pub cs_c_W: Option<C2::ScalarField>,
    pub cs_c_E: Option<C2::ScalarField>,
    /// Evaluations of the committed polynomials at the challenge
    pub eval_W: Option<C2::ScalarField>,
    pub eval_E: Option<C2::ScalarField>,
}
impl<C1, GC1, C2> DeciderCircuit2<C1, GC1, C2>
where
    C1: CurveGroup,
    C2: CurveGroup,
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C2 as Group>::ScalarField: Absorb,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
{
    pub fn from_nova<GC2, CS1, CS2, const H: bool, FC: FCircuit<C1::ScalarField>>(
        nova: Nova<C1, GC1, C2, GC2, FC, CS1, CS2, H>,
    ) -> Result<Self, Error>
    where
        GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
        CS1: CommitmentScheme<C1, H>,
        CS2: CommitmentScheme<C2, H>,
    {
        // compute the Commitment Scheme challenges of the CycleFold instance commitments, used as
        // inputs in the circuit
        let poseidon_config =
            crate::transcript::poseidon::poseidon_canonical_config::<C2::ScalarField>();
        let mut transcript = PoseidonSponge::<C2::ScalarField>::new(&poseidon_config);
        let pp_hash_Fq =
            C2::ScalarField::from_le_bytes_mod_order(&nova.pp_hash.into_bigint().to_bytes_le());
        transcript.absorb(&pp_hash_Fq);

        let (cs_challenge_W, cs_challenge_E) =
            KZGChallengesGadget::<C2>::get_challenges_native(&mut transcript, nova.cf_U_i.clone());

        // get evals of the committed polynomials at the challenge
        let mut W = nova.cf_W_i.W.clone();
        W.extend(
            std::iter::repeat(C2::ScalarField::zero())
                .take(nova.cf_W_i.W.len().next_power_of_two() - nova.cf_W_i.W.len()),
        );
        let mut E = nova.cf_W_i.E.clone();
        E.extend(
            std::iter::repeat(C2::ScalarField::zero())
                .take(nova.cf_W_i.E.len().next_power_of_two() - nova.cf_W_i.E.len()),
        );
        let p_W = poly_from_vec(W.to_vec())?;
        let eval_W = p_W.evaluate(&cs_challenge_W);
        let p_E = poly_from_vec(E.to_vec())?;
        let eval_E = p_E.evaluate(&cs_challenge_E);

        Ok(Self {
            _c1: PhantomData,
            _gc1: PhantomData,
            _c2: PhantomData,

            cf_E_len: nova.cf_W_i.E.len(),
            cf_r1cs: nova.cf_r1cs,
            poseidon_config,
            pp_hash: Some(pp_hash_Fq),

            cf_U_i: Some(nova.cf_U_i),
            cf_W_i: Some(nova.cf_W_i),

            // CycleFold instance commitments challenges
            cs_c_W: Some(cs_challenge_W),
            cs_c_E: Some(cs_challenge_E),
            eval_W: Some(eval_W),
            eval_E: Some(eval_E),
        })
    }
}

impl<C1, GC1, C2> ConstraintSynthesizer<CF1<C2>> for DeciderCircuit2<C1, GC1, C2>
where
    C1: CurveGroup,
    C2: CurveGroup,
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    <C2 as Group>::ScalarField: Absorb,
    C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    for<'a> &'a GC1: GroupOpsBounds<'a, C1, GC1>,
{
    fn generate_constraints(self, cs: ConstraintSystemRef<CF1<C2>>) -> Result<(), SynthesisError> {
        let pp_hash = FpVar::<CF1<C2>>::new_input(cs.clone(), || {
            Ok(self.pp_hash.unwrap_or_else(CF1::<C2>::zero))
        })?;

        let cf_u_dummy_native = CommittedInstance::<C2>::dummy(&self.cf_r1cs);
        let w_dummy_native = Witness::<C2>::dummy(&self.cf_r1cs);
        let cf_U_i = CommittedInstanceVar::<C2>::new_input(cs.clone(), || {
            Ok(self.cf_U_i.unwrap_or_else(|| cf_u_dummy_native.clone()))
        })?;
        let cf_W_i = WitnessVar::<C2>::new_witness(cs.clone(), || {
            Ok(self.cf_W_i.unwrap_or(w_dummy_native.clone()))
        })?;

        let cf_r1cs =
            R1CSVar::<C2::ScalarField, CF1<C2>, FpVar<CF1<C2>>>::new_witness(cs.clone(), || {
                Ok(self.cf_r1cs.clone())
            })?;

        // 6. check RelaxedR1CS of cf_U_i
        let cf_z_U = [vec![cf_U_i.u.clone()], cf_U_i.x.to_vec(), cf_W_i.W.to_vec()].concat();
        RelaxedR1CSGadget::check_native(cf_r1cs, cf_W_i.E.clone(), cf_U_i.u.clone(), cf_z_U)?;

        // `transcript` is for challenge generation.
        let mut transcript =
            PoseidonSpongeVar::<C2::ScalarField>::new(cs.clone(), &self.poseidon_config);
        transcript.absorb(&pp_hash)?;

        // allocate the inputs for the check 7.1
        let cs_c_W = FpVar::<CF1<C2>>::new_input(cs.clone(), || {
            Ok(self.cs_c_W.unwrap_or_else(CF1::<C2>::zero))
        })?;
        let cs_c_E = FpVar::<CF1<C2>>::new_input(cs.clone(), || {
            Ok(self.cs_c_E.unwrap_or_else(CF1::<C2>::zero))
        })?;
        // allocate the inputs for the check 7.2
        let eval_W = FpVar::<CF1<C2>>::new_input(cs.clone(), || {
            Ok(self.eval_W.unwrap_or_else(CF1::<C2>::zero))
        })?;
        let eval_E = FpVar::<CF1<C2>>::new_input(cs.clone(), || {
            Ok(self.eval_E.unwrap_or_else(CF1::<C2>::zero))
        })?;

        // 7.1. check the commitment scheme challenges correct computation
        let (incircuit_c_W, incircuit_c_E) =
            KZGChallengesGadget::<C2>::get_challenges_gadget(&mut transcript, cf_U_i.clone())?;
        incircuit_c_W.enforce_equal(&cs_c_W)?;
        incircuit_c_E.enforce_equal(&cs_c_E)?;

        // 7.2. check eval_W==p_W(c_W) and eval_E==p_E(c_E)
        let incircuit_eval_W = evaluate_gadget::<CF1<C2>>(cf_W_i.W, incircuit_c_W)?;
        let incircuit_eval_E = evaluate_gadget::<CF1<C2>>(cf_W_i.E, incircuit_c_E)?;
        incircuit_eval_W.enforce_equal(&eval_W)?;
        incircuit_eval_E.enforce_equal(&eval_E)?;

        Ok(())
    }
}

#[cfg(test)]
pub mod tests {
    use ark_pallas::{constraints::GVar, Fq, Fr, Projective};
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::One;
    use ark_vesta::{constraints::GVar as GVar2, Projective as Projective2};

    use super::*;
    use crate::commitment::pedersen::Pedersen;
    use crate::folding::nova::PreprocessorParam;
    use crate::frontend::utils::CubicFCircuit;
    use crate::transcript::poseidon::poseidon_canonical_config;
    use crate::FoldingScheme;

    #[test]
    fn test_decider_circuits() {
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
        let ivc_v = nova.clone();
        let (running_instance, incoming_instance, cyclefold_instance) = ivc_v.instances();
        N::verify(
            nova_params.1, // verifier_params
            z_0,
            ivc_v.z_i,
            Fr::one(),
            running_instance,
            incoming_instance,
            cyclefold_instance,
        )
        .unwrap();

        // load the DeciderCircuit 1 & 2 from the Nova instance
        let decider_circuit1 =
            DeciderCircuit1::<Projective, Projective2, GVar2>::from_nova(nova.clone()).unwrap();
        let decider_circuit2 =
            DeciderCircuit2::<Projective, GVar, Projective2>::from_nova(nova).unwrap();

        // generate the constraints of both circuits and check that are satisfied by the inputs
        let cs1 = ConstraintSystem::<Fr>::new_ref();
        decider_circuit1.generate_constraints(cs1.clone()).unwrap();
        assert!(cs1.is_satisfied().unwrap());
        let cs2 = ConstraintSystem::<Fq>::new_ref();
        decider_circuit2.generate_constraints(cs2.clone()).unwrap();
        assert!(cs2.is_satisfied().unwrap());
    }
}
