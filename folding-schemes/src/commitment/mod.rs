//! Vector commitment schemes implementation.
//!
//! This module provides trait definitions and implementations for various vector commitment schemes,
//! supporting both hiding and non-hiding variants. Implementations include:
//!
//! * Pedersen commitments ([`pedersen`])
//! * Inner Product Arguments ([`ipa`])
//! * Kate-Zaverucha-Goldberg commitments ([`kzg`])
//!
//! # Usage
//!
//! Each commitment scheme implements the [`CommitmentScheme`] trait, providing a uniform interface for:
//!
//! * Parameter setup
//! * Committing to vectors
//! * Generating proofs
//! * Verifying proofs
//!
//! # Features
//!
//! * Configurable hiding/non-hiding modes via const generic parameter
//! * Support for transcript-based and standalone proof generation
//! * Homomorphic properties for commitment combinations

use ark_ec::CurveGroup;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::fmt::Debug;
use ark_std::rand::RngCore;

use crate::transcript::Transcript;
use crate::Error;

pub mod ipa;
pub mod kzg;
pub mod pedersen;

/// Defines the interface for vector commitment schemes.
///
/// # Type Parameters
///
/// * `C` - The curve group used for commitments
/// * `H` - Boolean indicating if the scheme is hiding (`true`) or non-hiding (`false`)
///
/// Each implementation provides associated types for parameters, proofs, and challenges,
/// along with methods for setup, commitment, proving, and verification.
pub trait CommitmentScheme<C: CurveGroup, const H: bool = false>: Clone + Debug {
    /// Parameters used by the prover
    type ProverParams: Clone + Debug + CanonicalSerialize + CanonicalDeserialize;
    /// Parameters used by the verifier
    type VerifierParams: Clone + Debug + CanonicalSerialize + CanonicalDeserialize;
    /// Proof type for opening commitments
    type Proof: Clone + Debug + CanonicalSerialize + CanonicalDeserialize;
    /// Challenge type used by the prover
    type ProverChallenge: Clone + Debug;
    /// Challenge type used by the verifier
    type Challenge: Clone + Debug;

    /// Returns whether this instantiation is hiding
    fn is_hiding() -> bool {
        H
    }

    /// Generates parameters for the commitment scheme
    ///
    /// # Arguments
    ///
    /// * `rng` - Random number generator
    /// * `len` - Maximum length of vectors to be committed
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// * Parameter generation fails
    /// * The requested length is invalid
    fn setup(
        rng: impl RngCore,
        len: usize,
    ) -> Result<(Self::ProverParams, Self::VerifierParams), Error>;

    /// Commits to a vector using the given parameters
    ///
    /// # Arguments
    ///
    /// * `params` - Prover parameters
    /// * `v` - Vector to commit to
    /// * `blind` - Blinding factor (must be zero for non-hiding schemes)
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// * Vector length exceeds parameter size
    /// * Non-zero blinding used in non-hiding mode
    /// * Commitment computation fails
    fn commit(
        params: &Self::ProverParams,
        v: &[C::ScalarField],
        blind: &C::ScalarField,
    ) -> Result<C, Error>;

    /// Generates a proof for a commitment using a transcript
    ///
    /// # Arguments
    ///
    /// * `params` - Prover parameters
    /// * `transcript` - Transcript for Fiat-Shamir
    /// * `cm` - Commitment to prove
    /// * `v` - Committed vector
    /// * `blind` - Blinding factor used in commitment
    /// * `rng` - Optional RNG for randomized proofs
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// * Proof generation fails
    /// * Parameters are invalid
    /// * Vector/commitment mismatch
    fn prove(
        params: &Self::ProverParams,
        transcript: &mut impl Transcript<C::ScalarField>,
        cm: &C,
        v: &[C::ScalarField],
        blind: &C::ScalarField,
        rng: Option<&mut dyn RngCore>,
    ) -> Result<Self::Proof, Error>;

    /// Generates a proof using a pre-computed challenge
    ///
    /// Similar to [`prove`](Self::prove) but uses a provided challenge instead of a transcript.
    ///
    /// # Errors
    ///
    /// Returns an error if proof generation fails
    fn prove_with_challenge(
        params: &Self::ProverParams,
        challenge: Self::ProverChallenge,
        v: &[C::ScalarField],
        blind: &C::ScalarField,
        rng: Option<&mut dyn RngCore>,
    ) -> Result<Self::Proof, Error>;

    /// Verifies a proof using a transcript
    ///
    /// # Arguments
    ///
    /// * `params` - Verifier parameters
    /// * `transcript` - Transcript for Fiat-Shamir
    /// * `cm` - Commitment to verify
    /// * `proof` - Proof to check
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// * The proof is invalid
    /// * Parameters are invalid
    /// * Verification computation fails
    fn verify(
        params: &Self::VerifierParams,
        transcript: &mut impl Transcript<C::ScalarField>,
        cm: &C,
        proof: &Self::Proof,
    ) -> Result<(), Error>;

    /// Verifies a proof using a pre-computed challenge
    ///
    /// Similar to [`verify`](Self::verify) but uses a provided challenge instead of a transcript.
    ///
    /// # Errors
    ///
    /// Returns an error if verification fails
    fn verify_with_challenge(
        params: &Self::VerifierParams,
        challenge: Self::Challenge,
        cm: &C,
        proof: &Self::Proof,
    ) -> Result<(), Error>;
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bn254::{Bn254, Fr, G1Projective as G1};
    use ark_crypto_primitives::sponge::{
        poseidon::{PoseidonConfig, PoseidonSponge},
        Absorb, CryptographicSponge,
    };
    use ark_poly_commit::kzg10::VerifierKey;
    use ark_std::Zero;
    use ark_std::{test_rng, UniformRand};

    use super::ipa::IPA;
    use super::kzg::{ProverKey, KZG};
    use super::pedersen::Pedersen;
    use crate::transcript::poseidon::poseidon_canonical_config;

    #[test]
    fn test_homomorphic_property_using_Commitment_trait() -> Result<(), Error> {
        let mut rng = &mut test_rng();
        let poseidon_config = poseidon_canonical_config::<Fr>();
        let n: usize = 128;

        // set random vector for the test
        let v_1: Vec<Fr> = std::iter::repeat_with(|| Fr::rand(rng)).take(n).collect();
        let v_2: Vec<Fr> = std::iter::repeat_with(|| Fr::rand(rng)).take(n).collect();
        // set a random challenge for the random linear combination
        let r = Fr::rand(rng);

        // setup params for Pedersen & KZG
        let (pedersen_params, _) = Pedersen::<G1>::setup(&mut rng, n)?;
        let (kzg_pk, kzg_vk): (ProverKey<G1>, VerifierKey<Bn254>) = KZG::<Bn254>::setup(rng, n)?;

        // test with Pedersen
        test_homomorphic_property_using_Commitment_trait_opt::<G1, Pedersen<G1>>(
            &poseidon_config,
            &pedersen_params,
            &pedersen_params,
            r,
            &v_1,
            &v_2,
        )?;
        // test with IPA
        test_homomorphic_property_using_Commitment_trait_opt::<G1, IPA<G1>>(
            &poseidon_config,
            &pedersen_params,
            &pedersen_params,
            r,
            &v_1,
            &v_2,
        )?;
        // test with KZG
        test_homomorphic_property_using_Commitment_trait_opt::<G1, KZG<Bn254>>(
            &poseidon_config,
            &kzg_pk,
            &kzg_vk,
            r,
            &v_1,
            &v_2,
        )?;
        Ok(())
    }

    fn test_homomorphic_property_using_Commitment_trait_opt<
        C: CurveGroup,
        CS: CommitmentScheme<C>,
    >(
        poseidon_config: &PoseidonConfig<C::ScalarField>,
        prover_params: &CS::ProverParams,
        verifier_params: &CS::VerifierParams,
        r: C::ScalarField,
        v_1: &[C::ScalarField],
        v_2: &[C::ScalarField],
    ) -> Result<(), Error>
    where
        C::ScalarField: Absorb,
    {
        // compute the commitment of the two vectors using the given CommitmentScheme
        let cm_1 = CS::commit(prover_params, v_1, &C::ScalarField::zero())?;
        let cm_2 = CS::commit(prover_params, v_2, &C::ScalarField::zero())?;

        // random linear combination of the commitments and their witnesses (vectors v_i)
        let cm_3 = cm_1 + cm_2.mul(r);
        let v_3: Vec<C::ScalarField> = v_1.iter().zip(v_2).map(|(a, b)| *a + (r * b)).collect();

        // compute the proof of the cm_3
        let transcript_p = &mut PoseidonSponge::<C::ScalarField>::new(poseidon_config);
        let proof = CS::prove(
            prover_params,
            transcript_p,
            &cm_3,
            &v_3,
            &C::ScalarField::zero(),
            None,
        )?;

        // verify the opening proof
        let transcript_v = &mut PoseidonSponge::<C::ScalarField>::new(poseidon_config);
        CS::verify(verifier_params, transcript_v, &cm_3, &proof)?;
        Ok(())
    }
}
