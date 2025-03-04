/// This module defines the traits related to the NIFS (Non-Interactive Folding Scheme).
/// - NIFSTrait, which implements the NIFS interface
/// - NIFSGadget, which implements the NIFS in-circuit
///
/// Both traits implemented by the various Nova variants schemes; ie.
/// - [Nova](https://eprint.iacr.org/2021/370.pdf)
/// - [Ova](https://hackmd.io/V4838nnlRKal9ZiTHiGYzw)
/// - [Mova](https://eprint.iacr.org/2024/1220.pdf)
use ark_crypto_primitives::sponge::{constraints::AbsorbGadget, Absorb, CryptographicSponge};
use ark_r1cs_std::{alloc::AllocVar, boolean::Boolean, fields::fp::FpVar};
use ark_relations::r1cs::SynthesisError;
use ark_std::fmt::Debug;
use ark_std::rand::RngCore;

use crate::arith::r1cs::R1CS;
use crate::commitment::CommitmentScheme;
use crate::folding::circuits::CF1;
use crate::folding::traits::{CommittedInstanceOps, CommittedInstanceVarOps};
use crate::transcript::{Transcript, TranscriptVar};
use crate::{Curve, Error};

pub mod mova;
pub mod nova;
pub mod nova_circuits;
pub mod ova;
pub mod ova_circuits;
pub mod pointvsline;

/// Defines the NIFS (Non-Interactive Folding Scheme) trait, initially defined in
/// [Nova](https://eprint.iacr.org/2021/370.pdf), and it's variants
/// [Ova](https://hackmd.io/V4838nnlRKal9ZiTHiGYzw) and
/// [Mova](https://eprint.iacr.org/2024/1220.pdf).
/// `H` specifies whether the NIFS will use a blinding factor.
pub trait NIFSTrait<
    C: Curve,
    CS: CommitmentScheme<C, H>,
    T: Transcript<C::ScalarField>,
    const H: bool = false,
>
{
    type CommittedInstance: Debug + Clone + Absorb; // + CommittedInstanceOps<C>;
    type Witness: Debug + Clone;
    type ProverAux: Debug + Clone; // Prover's aux params. eg. in Nova is T
    type Proof: Debug + Clone; // proof. eg. in Nova is cmT

    fn new_witness(w: Vec<C::ScalarField>, e_len: usize, rng: impl RngCore) -> Self::Witness;

    fn new_instance(
        rng: impl RngCore,
        params: &CS::ProverParams,
        w: &Self::Witness,
        x: Vec<C::ScalarField>,
        aux: Vec<C::ScalarField>, // t_or_e in Ova, empty for Nova
    ) -> Result<Self::CommittedInstance, Error>;

    fn fold_witness(
        r: C::ScalarField,
        W: &Self::Witness, // running witness
        w: &Self::Witness, // incoming witness
        aux: &Self::ProverAux,
    ) -> Result<Self::Witness, Error>;

    /// NIFS.P. Returns a tuple containing the folded Witness, the folded CommittedInstance, and
    /// the used challenge `r` as a vector of bits, so that it can be reused in other methods.
    #[allow(clippy::type_complexity)]
    #[allow(clippy::too_many_arguments)]
    fn prove(
        cs_prover_params: &CS::ProverParams,
        r1cs: &R1CS<C::ScalarField>,
        transcript: &mut T,
        W_i: &Self::Witness,           // running witness
        U_i: &Self::CommittedInstance, // running committed instance
        w_i: &Self::Witness,           // incoming witness
        u_i: &Self::CommittedInstance, // incoming committed instance
    ) -> Result<
        (
            Self::Witness,
            Self::CommittedInstance,
            Self::Proof,
            Vec<bool>,
        ),
        Error,
    >;

    /// NIFS.V. Returns the folded CommittedInstance and the used challenge `r` as a vector of
    /// bits, so that it can be reused in other methods.
    fn verify(
        transcript: &mut T,
        U_i: &Self::CommittedInstance,
        u_i: &Self::CommittedInstance,
        proof: &Self::Proof,
    ) -> Result<(Self::CommittedInstance, Vec<bool>), Error>;
}

/// Defines the NIFS (Non-Interactive Folding Scheme) Gadget trait, which specifies the in-circuit
/// logic of the NIFS.Verify defined in [Nova](https://eprint.iacr.org/2021/370.pdf) and it's
/// variants [Ova](https://hackmd.io/V4838nnlRKal9ZiTHiGYzw) and
/// [Mova](https://eprint.iacr.org/2024/1220.pdf).
pub trait NIFSGadgetTrait<C: Curve, S: CryptographicSponge, T: TranscriptVar<CF1<C>, S>> {
    type CommittedInstance: Debug + Clone + Absorb + CommittedInstanceOps<C>;
    type CommittedInstanceVar: Debug
        + Clone
        + AbsorbGadget<C::ScalarField>
        + AllocVar<Self::CommittedInstance, CF1<C>>
        + CommittedInstanceVarOps<C>;
    type Proof: Debug + Clone;
    type ProofVar: Debug + Clone + AllocVar<Self::Proof, CF1<C>>;

    /// Implements the constraints for NIFS.V for u and x, since cm(E) and cm(W) are delegated to
    /// the CycleFold circuit.
    #[allow(clippy::type_complexity)]
    fn verify(
        transcript: &mut T,
        U_i: Self::CommittedInstanceVar,
        // U_i_vec is passed to reuse the already computed U_i_vec from previous methods
        U_i_vec: Vec<FpVar<CF1<C>>>,
        u_i: Self::CommittedInstanceVar,
        proof: Option<Self::ProofVar>,
    ) -> Result<(Self::CommittedInstanceVar, Vec<Boolean<CF1<C>>>), SynthesisError>;
}

/// These tests are the generic tests so that in the tests of Nova, Mova, Ova, we just need to
/// instantiate these tests to test both the NIFSTrait and NIFSGadgetTrait implementations for each
/// of the schemes.
#[cfg(test)]
pub mod tests {
    use ark_crypto_primitives::sponge::{
        constraints::AbsorbGadget,
        poseidon::{constraints::PoseidonSpongeVar, PoseidonSponge},
        Absorb,
    };
    use ark_pallas::{Fr, Projective};
    use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar, R1CSVar};
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::{cmp::max, test_rng, UniformRand};

    use super::NIFSTrait;
    use super::*;
    use crate::arith::{
        r1cs::tests::{get_test_r1cs, get_test_z},
        Arith,
    };
    use crate::commitment::pedersen::Pedersen;
    use crate::folding::traits::{CommittedInstanceOps, CommittedInstanceVarOps};
    use crate::transcript::poseidon::poseidon_canonical_config;

    /// Test method used to test the different implementations of the NIFSTrait (ie. Nova, Mova,
    /// Ova). Runs a loop using the NIFS trait, and returns the last Witness and CommittedInstance
    /// so that their relation can be checked.
    pub(crate) fn test_nifs_opt<
        N: NIFSTrait<Projective, Pedersen<Projective>, PoseidonSponge<Fr>>,
    >() -> Result<(N::Witness, N::CommittedInstance), Error> {
        let r1cs: R1CS<Fr> = get_test_r1cs();

        let mut rng = ark_std::test_rng();
        let (pedersen_params, _) =
            Pedersen::<Projective>::setup(&mut rng, max(r1cs.n_constraints(), r1cs.n_witnesses()))?;

        let poseidon_config = poseidon_canonical_config::<Fr>();
        let pp_hash = Fr::rand(&mut rng);
        let mut transcript_p = PoseidonSponge::<Fr>::new_with_pp_hash(&poseidon_config, pp_hash);
        let mut transcript_v = transcript_p.clone();

        // prepare the running instance
        let z = get_test_z(3);
        let (w, x) = r1cs.split_z(&z);
        let mut W_i = N::new_witness(w.clone(), r1cs.n_constraints(), test_rng());
        let mut U_i = N::new_instance(&mut rng, &pedersen_params, &W_i, x, vec![])?;

        let num_iters = 10;
        for i in 0..num_iters {
            // prepare the incoming instance
            let incoming_instance_z = get_test_z(i + 4);
            let (w, x) = r1cs.split_z(&incoming_instance_z);
            let w_i = N::new_witness(w.clone(), r1cs.n_constraints(), test_rng());
            let u_i = N::new_instance(&mut rng, &pedersen_params, &w_i, x, vec![])?;

            // NIFS.P
            let (folded_witness, _, proof, _) = N::prove(
                &pedersen_params,
                &r1cs,
                &mut transcript_p,
                &W_i,
                &U_i,
                &w_i,
                &u_i,
            )?;

            // NIFS.V
            let (folded_committed_instance, _) = N::verify(&mut transcript_v, &U_i, &u_i, &proof)?;

            // set running_instance for next loop iteration
            W_i = folded_witness;
            U_i = folded_committed_instance;
        }

        Ok((W_i, U_i))
    }

    /// Test method used to test the different implementations of the NIFSGadgetTrait (ie. Nova,
    /// Mova, Ova). It returns the last Witness and CommittedInstance so that it can be checked at
    /// the parent test that their values match.
    pub(crate) fn test_nifs_gadget_opt<N, NG>(
        ci: Vec<NG::CommittedInstance>,
        proof: NG::Proof,
    ) -> Result<(NG::CommittedInstance, NG::CommittedInstanceVar), Error>
    where
        N: NIFSTrait<Projective, Pedersen<Projective>, PoseidonSponge<Fr>>,
        NG: NIFSGadgetTrait<
            Projective,
            PoseidonSponge<Fr>,
            PoseidonSpongeVar<Fr>,
            CommittedInstance = N::CommittedInstance, // constrain that N::CI==NG::CI
            Proof = N::Proof,                         // constrain that N::Proof==NG::Proof
        >,
    {
        let mut rng = ark_std::test_rng();

        let (U_i, u_i) = (ci[0].clone(), ci[1].clone());
        let pp_hash = Fr::rand(&mut rng);
        let poseidon_config = poseidon_canonical_config::<Fr>();
        let mut transcript = PoseidonSponge::<Fr>::new_with_pp_hash(&poseidon_config, pp_hash);
        let (ci3, _) = N::verify(&mut transcript, &U_i, &u_i, &proof)?;

        let cs = ConstraintSystem::<Fr>::new_ref();

        let pp_hashVar = FpVar::<Fr>::new_witness(cs.clone(), || Ok(pp_hash))?;
        let mut transcriptVar =
            PoseidonSpongeVar::<Fr>::new_with_pp_hash(&poseidon_config, &pp_hashVar)?;
        let ci1Var = NG::CommittedInstanceVar::new_witness(cs.clone(), || Ok(U_i.clone()))?;
        let ci2Var = NG::CommittedInstanceVar::new_witness(cs.clone(), || Ok(u_i.clone()))?;
        let proofVar = NG::ProofVar::new_witness(cs.clone(), || Ok(proof))?;

        let ci1Var_vec = ci1Var.to_sponge_field_elements()?;
        let (out, _) = NG::verify(
            &mut transcriptVar,
            ci1Var.clone(),
            ci1Var_vec,
            ci2Var.clone(),
            Some(proofVar.clone()),
        )?;
        assert!(cs.is_satisfied()?);

        // return the NIFS.V and the NIFSGadget.V obtained values, so that they are checked at the
        // parent test
        Ok((ci3, out))
    }

    /// test that checks the native CommittedInstance.to_sponge_{bytes,field_elements}
    /// vs the R1CS constraints version
    pub(crate) fn test_committed_instance_to_sponge_preimage_opt<N, NG>(
        ci: N::CommittedInstance,
    ) -> Result<(), Error>
    where
        N: NIFSTrait<Projective, Pedersen<Projective>, PoseidonSponge<Fr>>,
        NG: NIFSGadgetTrait<
            Projective,
            PoseidonSponge<Fr>,
            PoseidonSpongeVar<Fr>,
            CommittedInstance = N::CommittedInstance, // constrain that N::CI==NG::CI
        >,
    {
        let bytes = ci.to_sponge_bytes_as_vec();
        let field_elements = ci.to_sponge_field_elements_as_vec();

        let cs = ConstraintSystem::<Fr>::new_ref();

        let ciVar = NG::CommittedInstanceVar::new_witness(cs.clone(), || Ok(ci.clone()))?;
        let bytes_var = ciVar.to_sponge_bytes()?;
        let field_elements_var = ciVar.to_sponge_field_elements()?;

        assert!(cs.is_satisfied()?);

        // check that the natively computed and in-circuit computed hashes match
        assert_eq!(bytes_var.value()?, bytes);
        assert_eq!(field_elements_var.value()?, field_elements);
        Ok(())
    }

    pub(crate) fn test_committed_instance_hash_opt<N, NG>(
        ci: NG::CommittedInstance,
    ) -> Result<(), Error>
    where
        N: NIFSTrait<Projective, Pedersen<Projective>, PoseidonSponge<Fr>>,
        NG: NIFSGadgetTrait<
            Projective,
            PoseidonSponge<Fr>,
            PoseidonSpongeVar<Fr>,
            CommittedInstance = N::CommittedInstance, // constrain that N::CI==NG::CI
        >,
        N::CommittedInstance: CommittedInstanceOps<Projective>,
    {
        let poseidon_config = poseidon_canonical_config::<Fr>();
        let pp_hash = Fr::from(42u32); // only for test
        let sponge = PoseidonSponge::<Fr>::new_with_pp_hash(&poseidon_config, pp_hash);

        let i = Fr::from(3_u32);
        let z_0 = vec![Fr::from(3_u32)];
        let z_i = vec![Fr::from(3_u32)];

        // compute the CommittedInstance hash natively
        let h = ci.hash(&sponge, i, &z_0, &z_i);

        let cs = ConstraintSystem::<Fr>::new_ref();

        let pp_hashVar = FpVar::<Fr>::new_witness(cs.clone(), || Ok(pp_hash))?;
        let iVar = FpVar::<Fr>::new_witness(cs.clone(), || Ok(i))?;
        let z_0Var = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(z_0.clone()))?;
        let z_iVar = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(z_i.clone()))?;
        let ciVar = NG::CommittedInstanceVar::new_witness(cs.clone(), || Ok(ci.clone()))?;

        let sponge = PoseidonSpongeVar::<Fr>::new_with_pp_hash(&poseidon_config, &pp_hashVar)?;

        // compute the CommittedInstance hash in-circuit
        let (hVar, _) = ciVar.hash(&sponge, &iVar, &z_0Var, &z_iVar)?;
        assert!(cs.is_satisfied()?);

        // check that the natively computed and in-circuit computed hashes match
        assert_eq!(hVar.value()?, h);
        Ok(())
    }
}
