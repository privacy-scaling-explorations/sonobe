/// This module defines the NIFSTrait, which is set to implement the NIFS (Non-Interactive Folding
/// Scheme) by the various schemes (Nova, Mova, Ova).
use ark_crypto_primitives::sponge::Absorb;
use ark_ec::CurveGroup;
use ark_std::fmt::Debug;
use ark_std::rand::RngCore;

use crate::arith::r1cs::R1CS;
use crate::commitment::CommitmentScheme;
use crate::transcript::Transcript;
use crate::Error;

pub mod mova;
pub mod nova;
pub mod ova;
pub mod pointvsline;

/// Defines the NIFS (Non-Interactive Folding Scheme) trait, initially defined in
/// [Nova](https://eprint.iacr.org/2021/370.pdf), and it's variants
/// [Ova](https://hackmd.io/V4838nnlRKal9ZiTHiGYzw) and
/// [Mova](https://eprint.iacr.org/2024/1220.pdf).
/// `H` specifies whether the NIFS will use a blinding factor.
pub trait NIFSTrait<
    C: CurveGroup,
    CS: CommitmentScheme<C, H>,
    T: Transcript<C::ScalarField>,
    const H: bool = false,
>
{
    type CommittedInstance: Debug + Clone + Absorb;
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
        pp_hash: C::ScalarField,
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
        pp_hash: C::ScalarField,
        U_i: &Self::CommittedInstance,
        u_i: &Self::CommittedInstance,
        proof: &Self::Proof,
    ) -> Result<(Self::CommittedInstance, Vec<bool>), Error>;
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::transcript::poseidon::poseidon_canonical_config;
    use ark_crypto_primitives::sponge::{poseidon::PoseidonSponge, CryptographicSponge};
    use ark_pallas::{Fr, Projective};
    use ark_std::{test_rng, UniformRand};

    use super::NIFSTrait;
    use crate::arith::r1cs::tests::{get_test_r1cs, get_test_z};
    use crate::commitment::pedersen::Pedersen;

    /// Test method used to test the different implementations of the NIFSTrait (ie. Nova, Mova,
    /// Ova). Runs a loop using the NIFS trait, and returns the last Witness and CommittedInstance
    /// so that their relation can be checked.
    pub(crate) fn test_nifs_opt<
        N: NIFSTrait<Projective, Pedersen<Projective>, PoseidonSponge<Fr>>,
    >() -> (N::Witness, N::CommittedInstance) {
        let r1cs = get_test_r1cs();
        let z = get_test_z(3);
        let (w, x) = r1cs.split_z(&z);

        let mut rng = ark_std::test_rng();
        let (pedersen_params, _) = Pedersen::<Projective>::setup(&mut rng, r1cs.A.n_cols).unwrap();

        let poseidon_config = poseidon_canonical_config::<Fr>();
        let mut transcript_p = PoseidonSponge::<Fr>::new(&poseidon_config);
        let mut transcript_v = PoseidonSponge::<Fr>::new(&poseidon_config);
        let pp_hash = Fr::rand(&mut rng);

        // prepare the running instance
        let mut W_i = N::new_witness(w.clone(), r1cs.A.n_rows, test_rng());
        let mut U_i = N::new_instance(&mut rng, &pedersen_params, &W_i, x, vec![]).unwrap();

        let num_iters = 10;
        for i in 0..num_iters {
            // prepare the incoming instance
            let incoming_instance_z = get_test_z(i + 4);
            let (w, x) = r1cs.split_z(&incoming_instance_z);
            let w_i = N::new_witness(w.clone(), r1cs.A.n_rows, test_rng());
            let u_i = N::new_instance(&mut rng, &pedersen_params, &w_i, x, vec![]).unwrap();

            // NIFS.P
            let (folded_witness, _, proof, _) = N::prove(
                &pedersen_params,
                &r1cs,
                &mut transcript_p,
                pp_hash,
                &W_i,
                &U_i,
                &w_i,
                &u_i,
            )
            .unwrap();

            // NIFS.V
            let (folded_committed_instance, _) =
                N::verify(&mut transcript_v, pp_hash, &U_i, &u_i, &proof).unwrap();

            // set running_instance for next loop iteration
            W_i = folded_witness;
            U_i = folded_committed_instance;
        }

        (W_i, U_i)
    }
}
