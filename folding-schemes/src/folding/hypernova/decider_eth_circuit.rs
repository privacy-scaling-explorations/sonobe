/// This file implements the onchain (Ethereum's EVM) decider circuit. For non-ethereum use cases,
/// other more efficient approaches can be used.
use ark_crypto_primitives::sponge::{
    constraints::CryptographicSpongeVar,
    poseidon::{constraints::PoseidonSpongeVar, PoseidonConfig, PoseidonSponge},
    Absorb, CryptographicSponge,
};
use ark_ec::{CurveGroup, Group};
use ark_ff::PrimeField;
use ark_poly::Polynomial;
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    boolean::Boolean,
    eq::EqGadget,
    fields::fp::FpVar,
    groups::GroupOpsBounds,
    prelude::CurveVar,
    ToConstraintFieldGadget,
};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, Namespace, SynthesisError};
use ark_std::Zero;
use core::{borrow::Borrow, marker::PhantomData};

use super::{
    circuits::{CCCSVar, LCCCSVar, NIMFSGadget, ProofVar as NIMFSProofVar},
    nimfs::{NIMFSProof, NIMFS},
    HyperNova, Witness, CCCS, LCCCS,
};
use crate::folding::circuits::{
    cyclefold::{CycleFoldCommittedInstance, CycleFoldWitness},
    CF1, CF2,
};
use crate::frontend::FCircuit;
use crate::transcript::{Transcript, TranscriptVar};
use crate::utils::{
    gadgets::{eval_mle, MatrixGadget, SparseMatrixVar},
    vec::poly_from_vec,
};
use crate::Error;
use crate::{
    arith::{ccs::CCS, r1cs::R1CS},
    folding::traits::{CommittedInstanceVarOps, Dummy, WitnessVarOps},
};
use crate::{
    commitment::{pedersen::Params as PedersenParams, CommitmentScheme},
    folding::nova::decider_eth_circuit::evaluate_gadget,
};

/// In-circuit representation of the Witness associated to the CommittedInstance.
#[derive(Debug, Clone)]
pub struct WitnessVar<F: PrimeField> {
    pub w: Vec<FpVar<F>>,
    pub r_w: FpVar<F>,
}

impl<F: PrimeField> AllocVar<Witness<F>, F> for WitnessVar<F> {
    fn new_variable<T: Borrow<Witness<F>>>(
        cs: impl Into<Namespace<F>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|val| {
            let cs = cs.into();

            let w: Vec<FpVar<F>> =
                Vec::new_variable(cs.clone(), || Ok(val.borrow().w.clone()), mode)?;
            let r_w = FpVar::<F>::new_variable(cs.clone(), || Ok(val.borrow().r_w), mode)?;

            Ok(Self { w, r_w })
        })
    }
}

impl<F: PrimeField> WitnessVarOps<F> for WitnessVar<F> {
    fn get_openings(&self) -> Vec<(&[FpVar<F>], FpVar<F>)> {
        vec![(&self.w, self.r_w.clone())]
    }
}

/// CCSMatricesVar contains the matrices 'M' of the CCS without the rest of CCS parameters.
#[derive(Debug, Clone)]
pub struct CCSMatricesVar<F: PrimeField> {
    // we only need native representation, so the constraint field==F
    pub M: Vec<SparseMatrixVar<F, F, FpVar<F>>>,
}

impl<F> AllocVar<CCS<F>, F> for CCSMatricesVar<F>
where
    F: PrimeField,
{
    fn new_variable<T: Borrow<CCS<F>>>(
        cs: impl Into<Namespace<F>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        _mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|val| {
            let cs = cs.into();

            let M: Vec<SparseMatrixVar<F, F, FpVar<F>>> = val
                .borrow()
                .M
                .iter()
                .map(|M| SparseMatrixVar::<F, F, FpVar<F>>::new_constant(cs.clone(), M.clone()))
                .collect::<Result<_, SynthesisError>>()?;

            Ok(Self { M })
        })
    }
}

/// Gadget to check the LCCCS relation both over the native constraint field and over the
/// non-native constraint field.
#[derive(Debug, Clone)]
pub struct LCCCSCheckerGadget {}
impl LCCCSCheckerGadget {
    /// performs in-circuit the RelaxedR1CS check for native variables (Az∘Bz==uCz+E)
    pub fn check<F: PrimeField>(
        s: usize,
        ccs_mat: CCSMatricesVar<F>,
        z: Vec<FpVar<F>>,
        // LCCCS values
        r_x: Vec<FpVar<F>>,
        v: Vec<FpVar<F>>,
    ) -> Result<(), SynthesisError> {
        let computed_v: Vec<FpVar<F>> = ccs_mat
            .M
            .iter()
            .map(|M_j| {
                let Mz = M_j.mul_vector(&z)?;
                Ok(eval_mle(s, Mz, r_x.clone()))
            })
            .collect::<Result<Vec<FpVar<F>>, SynthesisError>>()?;

        (computed_v).enforce_equal(&v)?;
        Ok(())
    }
}

/// Circuit that implements the in-circuit checks needed for the HyperNova's onchain (Ethereum's
/// EVM) verification.
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

    /// E vector's length of the CycleFold instance witness
    pub cf_E_len: usize,
    /// CCS of the Augmented Function circuit
    pub ccs: CCS<C1::ScalarField>,
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
    pub U_i: Option<LCCCS<C1>>,
    pub W_i: Option<Witness<C1::ScalarField>>,
    pub u_i: Option<CCCS<C1>>,
    pub w_i: Option<Witness<C1::ScalarField>>,
    pub U_i1: Option<LCCCS<C1>>,
    pub W_i1: Option<Witness<C1::ScalarField>>,
    pub nimfs_proof: Option<NIMFSProof<C1>>,
    // rho is the 'random' value used for the fold of the last 2 instances
    pub rho: Option<C1::ScalarField>,
    /// CycleFold running instance
    pub cf_U_i: Option<CycleFoldCommittedInstance<C2>>,
    pub cf_W_i: Option<CycleFoldWitness<C2>>,

    /// KZG challenge & eval
    pub kzg_challenge: Option<C1::ScalarField>,
    pub eval_W: Option<C1::ScalarField>,
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
    /// returns an instance of the DeciderEthCircuit from the given HyperNova struct
    pub fn from_hypernova<FC: FCircuit<C1::ScalarField>, const MU: usize, const NU: usize>(
        hn: HyperNova<C1, GC1, C2, GC2, FC, CS1, CS2, MU, NU, H>,
    ) -> Result<Self, Error> {
        // compute the U_{i+1}, W_{i+1}, by folding the last running & incoming instances
        let mut transcript = PoseidonSponge::<C1::ScalarField>::new(&hn.poseidon_config);
        transcript.absorb(&hn.pp_hash);
        let (nimfs_proof, U_i1, W_i1, rho) = NIMFS::<C1, PoseidonSponge<C1::ScalarField>>::prove(
            &mut transcript,
            &hn.ccs,
            &[hn.U_i.clone()],
            &[hn.u_i.clone()],
            &[hn.W_i.clone()],
            &[hn.w_i.clone()],
        )?;

        // compute the KZG challenges used as inputs in the circuit
        let kzg_challenge =
            KZGChallengeGadget::<C1>::get_challenge_native(&mut transcript, U_i1.clone())?;

        // get KZG evals
        let mut W = W_i1.w.clone();
        W.extend(
            std::iter::repeat(C1::ScalarField::zero())
                .take(W_i1.w.len().next_power_of_two() - W_i1.w.len()),
        );
        let p_W = poly_from_vec(W.to_vec())?;
        let eval_W = p_W.evaluate(&kzg_challenge);

        Ok(Self {
            _c1: PhantomData,
            _gc1: PhantomData,
            _c2: PhantomData,
            _gc2: PhantomData,
            _cs1: PhantomData,
            _cs2: PhantomData,

            cf_E_len: hn.cf_W_i.E.len(),
            ccs: hn.ccs,
            cf_r1cs: hn.cf_r1cs,
            cf_pedersen_params: hn.cf_cs_pp,
            poseidon_config: hn.poseidon_config,
            pp_hash: Some(hn.pp_hash),
            i: Some(hn.i),
            z_0: Some(hn.z_0),
            z_i: Some(hn.z_i),
            U_i: Some(hn.U_i),
            W_i: Some(hn.W_i),
            u_i: Some(hn.u_i),
            w_i: Some(hn.w_i),
            U_i1: Some(U_i1),
            W_i1: Some(W_i1),
            nimfs_proof: Some(nimfs_proof),
            rho: Some(rho),
            cf_U_i: Some(hn.cf_U_i),
            cf_W_i: Some(hn.cf_W_i),
            kzg_challenge: Some(kzg_challenge),
            eval_W: Some(eval_W),
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
    C1::ScalarField: PrimeField,
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    <C2 as Group>::ScalarField: Absorb,
    C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    for<'b> &'b GC2: GroupOpsBounds<'b, C2, GC2>,
{
    fn generate_constraints(self, cs: ConstraintSystemRef<CF1<C1>>) -> Result<(), SynthesisError> {
        let ccs_matrices =
            CCSMatricesVar::<C1::ScalarField>::new_witness(cs.clone(), || Ok(self.ccs.clone()))?;

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

        let U_dummy_native = LCCCS::<C1>::dummy(&self.ccs);
        let u_dummy_native = CCCS::<C1>::dummy(&self.ccs);
        let w_dummy_native = Witness::<C1::ScalarField>::new(
            vec![C1::ScalarField::zero(); self.ccs.n - 3 /* (3=2+1, since u_i.x.len=2) */],
        );

        let U_i = LCCCSVar::<C1>::new_witness(cs.clone(), || {
            Ok(self.U_i.unwrap_or(U_dummy_native.clone()))
        })?;
        let u_i = CCCSVar::<C1>::new_witness(cs.clone(), || {
            Ok(self.u_i.unwrap_or(u_dummy_native.clone()))
        })?;
        // here (U_i1, W_i1) = NIFS.P( (U_i,W_i), (u_i,w_i))
        let U_i1 = LCCCSVar::<C1>::new_input(cs.clone(), || {
            Ok(self.U_i1.unwrap_or(U_dummy_native.clone()))
        })?;
        let W_i1 = WitnessVar::<C1::ScalarField>::new_witness(cs.clone(), || {
            Ok(self.W_i1.unwrap_or(w_dummy_native.clone()))
        })?;
        let nimfs_proof_dummy = NIMFSProof::<C1>::dummy((&self.ccs, 1, 1)); // mu=1 & nu=1 because the last fold is 2-to-1
        let nimfs_proof = NIMFSProofVar::<C1>::new_witness(cs.clone(), || {
            Ok(self.nimfs_proof.unwrap_or(nimfs_proof_dummy))
        })?;

        // allocate the inputs for the check 6
        let kzg_challenge = FpVar::<CF1<C1>>::new_input(cs.clone(), || {
            Ok(self.kzg_challenge.unwrap_or_else(CF1::<C1>::zero))
        })?;
        let eval_W = FpVar::<CF1<C1>>::new_input(cs.clone(), || {
            Ok(self.eval_W.unwrap_or_else(CF1::<C1>::zero))
        })?;

        // `sponge` is for digest computation.
        let sponge = PoseidonSpongeVar::<C1::ScalarField>::new(cs.clone(), &self.poseidon_config);
        // `transcript` is for challenge generation.
        let mut transcript = sponge.clone();
        transcript.absorb(&pp_hash)?;

        // NOTE: we use the same enumeration as in Nova's DeciderEthCircuit described at
        // https://privacy-scaling-explorations.github.io/sonobe-docs/design/nova-decider-onchain.html
        // in order to make it easier to reason about.

        // 1. check LCCCS relation of U_{i+1}
        let z_U1: Vec<FpVar<CF1<C1>>> =
            [vec![U_i1.u.clone()], U_i1.x.to_vec(), W_i1.w.to_vec()].concat();
        LCCCSCheckerGadget::check(
            self.ccs.s,
            ccs_matrices,
            z_U1,
            U_i1.r_x.clone(),
            U_i1.v.clone(),
        )?;

        // 3.a u_i.x[0] == H(i, z_0, z_i, U_i)
        let (u_i_x, _) = U_i.clone().hash(&sponge, &pp_hash, &i, &z_0, &z_i)?;
        (u_i.x[0]).enforce_equal(&u_i_x)?;

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
            use crate::folding::circuits::nonnative::uint::NonNativeUintVar;
            use crate::folding::nova::decider_eth_circuit::{R1CSVar, RelaxedR1CSGadget};
            use crate::folding::{
                circuits::cyclefold::{
                    CycleFoldCommittedInstanceVar, CycleFoldConfig, CycleFoldWitnessVar,
                },
                nova::NovaCycleFoldConfig,
            };
            use ark_r1cs_std::ToBitsGadget;

            let cf_u_dummy_native =
                CycleFoldCommittedInstance::<C2>::dummy(NovaCycleFoldConfig::<C1>::IO_LEN);
            let cf_w_dummy_native = CycleFoldWitness::<C2>::dummy(&self.cf_r1cs);
            let cf_U_i = CycleFoldCommittedInstanceVar::<C2, GC2>::new_witness(cs.clone(), || {
                Ok(self.cf_U_i.unwrap_or_else(|| cf_u_dummy_native.clone()))
            })?;
            let cf_W_i = CycleFoldWitnessVar::<C2>::new_witness(cs.clone(), || {
                Ok(self.cf_W_i.unwrap_or(cf_w_dummy_native.clone()))
            })?;

            // 3.b u_i.x[1] == H(cf_U_i)
            let (cf_u_i_x, _) = cf_U_i.clone().hash(&sponge, pp_hash.clone())?;
            (u_i.x[1]).enforce_equal(&cf_u_i_x)?;

            // 4. check Pedersen commitments of cf_U_i.{cmE, cmW}
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

            let cf_r1cs =
                R1CSVar::<C1::BaseField, CF1<C1>, NonNativeUintVar<CF1<C1>>>::new_witness(
                    cs.clone(),
                    || Ok(self.cf_r1cs.clone()),
                )?;

            // 5. check RelaxedR1CS of cf_U_i
            let cf_z_U = [vec![cf_U_i.u.clone()], cf_U_i.x.to_vec(), cf_W_i.W.to_vec()].concat();
            RelaxedR1CSGadget::check_nonnative(cf_r1cs, cf_W_i.E, cf_U_i.u.clone(), cf_z_U)?;
        }

        // The following steps are in non-increasing order because the `computed_U_i1` is computed
        // at step 8, and later used at step 6. Notice that in Nova, we compute U_i1 outside of the
        // circuit, in the smart contract, but here we're computing it in-circuit, and we reuse the
        // `rho_bits` computed along the way of computing `computed_U_i1` for the later `rho_powers`
        // check (6.b).

        // 8.a verify the NIMFS.V of the final fold, and check that the obtained rho_powers from the
        // transcript match the one from the public input (so we avoid the onchain logic of the
        // verifier computing it).
        // Notice that the NIMFSGadget performs all the logic except of checking the fold of the
        // instances C parameter, which would require non-native arithmetic, henceforth we perform
        // that check outside the circuit.
        let (computed_U_i1, rho_bits) = NIMFSGadget::<C1>::verify(
            cs.clone(),
            &self.ccs.clone(),
            &mut transcript,
            &[U_i],
            &[u_i],
            nimfs_proof,
            Boolean::TRUE, // enabled
        )?;

        // 6.a check KZG challenges
        // Notice that this step is done after the NIMFS.V, to follow the transcript absorbs order
        // done outside the circuit, where to compute the challenge it needs first to compute the
        // U_{i+1} through the NIMFS.V
        let incircuit_challenge =
            KZGChallengeGadget::<C1>::get_challenge_gadget(&mut transcript, U_i1.clone())?;
        incircuit_challenge.enforce_equal(&kzg_challenge)?;

        // 6.b check that the obtained U_{i+1} from the NIMFS.V matches the U_{i+1} from the input,
        // except for the C parameter, which to compute its folding would require non-native logic
        // in-circuit, and we defer it to outside the circuit.
        computed_U_i1.u.enforce_equal(&U_i1.u)?;
        computed_U_i1.r_x.enforce_equal(&U_i1.r_x)?;
        computed_U_i1.v.enforce_equal(&U_i1.v)?;

        // 7. check eval_W==p_W(c_W)
        let incircuit_eval_W = evaluate_gadget::<CF1<C1>>(W_i1.w, incircuit_challenge)?;
        incircuit_eval_W.enforce_equal(&eval_W)?;

        // 8.b check that the in-circuit computed r is equal to the inputted r.

        let rho = Boolean::le_bits_to_fp_var(&rho_bits)?;
        let external_rho =
            FpVar::<CF1<C1>>::new_input(cs.clone(), || Ok(self.rho.unwrap_or(CF1::<C1>::zero())))?;
        rho.enforce_equal(&external_rho)?;

        Ok(())
    }
}

/// Gadget that computes the KZG challenges, also offers the rust native implementation compatible
/// with the gadget.
pub struct KZGChallengeGadget<C: CurveGroup> {
    _c: PhantomData<C>,
}
#[allow(clippy::type_complexity)]
impl<C> KZGChallengeGadget<C>
where
    C: CurveGroup,
    C::ScalarField: PrimeField,
    <C as CurveGroup>::BaseField: PrimeField,
    C::ScalarField: Absorb,
{
    pub fn get_challenge_native<T: Transcript<C::ScalarField>>(
        transcript: &mut T,
        U_i: LCCCS<C>,
    ) -> Result<C::ScalarField, Error> {
        // compute the KZG challenges, which are computed in-circuit and checked that it matches
        // the inputted one
        transcript.absorb_nonnative(&U_i.C);
        Ok(transcript.get_challenge())
    }
    // compatible with the native get_challenge_native
    pub fn get_challenge_gadget<S: CryptographicSponge, T: TranscriptVar<CF1<C>, S>>(
        transcript: &mut T,
        U_i: LCCCSVar<C>,
    ) -> Result<FpVar<C::ScalarField>, SynthesisError> {
        transcript.absorb(&U_i.C.to_constraint_field()?)?;
        transcript.get_challenge()
    }
}

#[cfg(test)]
pub mod tests {
    use ark_bn254::{constraints::GVar, Fr, G1Projective as Projective};
    use ark_grumpkin::{constraints::GVar as GVar2, Projective as Projective2};
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::One;
    use ark_std::{test_rng, UniformRand};

    use super::*;
    use crate::commitment::pedersen::Pedersen;
    use crate::folding::nova::PreprocessorParam;
    use crate::frontend::utils::CubicFCircuit;
    use crate::transcript::poseidon::poseidon_canonical_config;
    use crate::FoldingScheme;

    #[test]
    fn test_lcccs_checker_gadget() {
        let mut rng = test_rng();
        let n_rows = 2_u32.pow(5) as usize;
        let n_cols = 2_u32.pow(5) as usize;
        let r1cs = R1CS::<Fr>::rand(&mut rng, n_rows, n_cols);
        let ccs = CCS::from(r1cs);
        let z: Vec<Fr> = (0..n_cols).map(|_| Fr::rand(&mut rng)).collect();

        let (pedersen_params, _) =
            Pedersen::<Projective>::setup(&mut rng, ccs.n - ccs.l - 1).unwrap();

        let (lcccs, _) = ccs
            .to_lcccs::<_, Projective, Pedersen<Projective>, false>(&mut rng, &pedersen_params, &z)
            .unwrap();

        let cs = ConstraintSystem::<Fr>::new_ref();

        // CCS's (sparse) matrices are constants in the circuit
        let ccs_mat = CCSMatricesVar::<Fr>::new_constant(cs.clone(), ccs.clone()).unwrap();
        let zVar = Vec::<FpVar<Fr>>::new_input(cs.clone(), || Ok(z)).unwrap();
        let r_xVar = Vec::<FpVar<Fr>>::new_input(cs.clone(), || Ok(lcccs.r_x)).unwrap();
        let vVar = Vec::<FpVar<Fr>>::new_input(cs.clone(), || Ok(lcccs.v)).unwrap();

        LCCCSCheckerGadget::check(ccs.s, ccs_mat, zVar, r_xVar, vVar).unwrap();

        assert!(cs.is_satisfied().unwrap());
    }

    #[test]
    fn test_decider_circuit() {
        let mut rng = ark_std::test_rng();
        let poseidon_config = poseidon_canonical_config::<Fr>();

        let F_circuit = CubicFCircuit::<Fr>::new(()).unwrap();
        let z_0 = vec![Fr::from(3_u32)];

        const MU: usize = 1;
        const NU: usize = 1;

        type HN = HyperNova<
            Projective,
            GVar,
            Projective2,
            GVar2,
            CubicFCircuit<Fr>,
            Pedersen<Projective>,
            Pedersen<Projective2>,
            MU,
            NU,
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
        let hn_params = HN::preprocess(&mut rng, &prep_param).unwrap();

        // generate a Nova instance and do a step of it
        let mut hypernova = HN::init(&hn_params, F_circuit, z_0.clone()).unwrap();
        hypernova
            .prove_step(&mut rng, vec![], Some((vec![], vec![])))
            .unwrap();

        let ivc_v = hypernova.clone();
        let (running_instance, incoming_instance, cyclefold_instance) = ivc_v.instances();
        HN::verify(
            hn_params.1, // HN's verifier_params
            z_0,
            ivc_v.z_i,
            Fr::one(),
            running_instance,
            incoming_instance,
            cyclefold_instance,
        )
        .unwrap();

        // load the DeciderEthCircuit from the generated Nova instance
        let decider_circuit = DeciderEthCircuit::<
            Projective,
            GVar,
            Projective2,
            GVar2,
            Pedersen<Projective>,
            Pedersen<Projective2>,
        >::from_hypernova(hypernova)
        .unwrap();

        let cs = ConstraintSystem::<Fr>::new_ref();

        // generate the constraints and check that are satisfied by the inputs
        decider_circuit.generate_constraints(cs.clone()).unwrap();
        assert!(cs.is_satisfied().unwrap());
        dbg!(cs.num_constraints());
    }
}
