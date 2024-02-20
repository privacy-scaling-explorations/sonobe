use ark_ec::CurveGroup;
use ark_std::fmt::Debug;
use ark_std::rand::RngCore;

use crate::transcript::Transcript;
use crate::Error;

pub mod ipa;
pub mod kzg;
pub mod pedersen;

/// CommitmentProver defines the vector commitment scheme prover trait.
pub trait CommitmentProver<C: CurveGroup, const BLIND: bool = false>: Clone + Debug {
    type Params: Clone + Debug;
    type Proof: Clone + Debug;

    fn commit(
        params: &Self::Params,
        v: &[C::ScalarField],
        blind: &C::ScalarField,
    ) -> Result<C, Error>;
    fn prove(
        params: &Self::Params,
        transcript: &mut impl Transcript<C>,
        cm: &C,
        v: &[C::ScalarField],
        blind: &C::ScalarField,
        rng: Option<&mut dyn RngCore>,
    ) -> Result<Self::Proof, Error>;
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bn254::{Bn254, Fr, G1Projective as G1};
    use ark_crypto_primitives::sponge::{poseidon::PoseidonConfig, Absorb};
    use ark_poly::univariate::DensePolynomial;
    use ark_poly_commit::kzg10::{
        Commitment as KZG10Commitment, Proof as KZG10Proof, VerifierKey, KZG10,
    };
    use ark_std::Zero;
    use ark_std::{test_rng, UniformRand};

    use super::kzg::{KZGProver, KZGSetup, ProverKey};
    use super::pedersen::Pedersen;
    use crate::transcript::{
        poseidon::{poseidon_test_config, PoseidonTranscript},
        Transcript,
    };

    // Computes the commitment of the two vectors using the given CommitmentProver, then computes
    // their random linear combination, and returns it together with the proof of it.
    fn commit_rlc_and_prove<C: CurveGroup, CP: CommitmentProver<C>>(
        poseidon_config: &PoseidonConfig<C::ScalarField>,
        params: &CP::Params,
        r: C::ScalarField,
        v_1: &[C::ScalarField],
        v_2: &[C::ScalarField],
    ) -> Result<(C, CP::Proof), Error>
    where
        <C as ark_ec::Group>::ScalarField: Absorb,
    {
        let cm_1 = CP::commit(params, v_1, &C::ScalarField::zero())?;
        let cm_2 = CP::commit(params, v_2, &C::ScalarField::zero())?;

        // random linear combination of the commitment and the witness (vector v)
        let cm_3 = cm_1 + cm_2.mul(r);
        let v_3: Vec<C::ScalarField> = v_1.iter().zip(v_2).map(|(a, b)| *a + (r * b)).collect();

        let transcript = &mut PoseidonTranscript::<C>::new(poseidon_config);
        let proof = CP::prove(
            params,
            transcript,
            &cm_3,
            &v_3,
            &C::ScalarField::zero(),
            None,
        )
        .unwrap();

        Ok((cm_3, proof))
    }

    #[test]
    fn test_homomorphic_property_using_CommitmentProver_trait() {
        let rng = &mut test_rng();
        let poseidon_config = poseidon_test_config::<Fr>();
        let n: usize = 100;

        // set random vector for the test
        let v_1: Vec<Fr> = std::iter::repeat_with(|| Fr::rand(rng)).take(n).collect();
        let v_2: Vec<Fr> = std::iter::repeat_with(|| Fr::rand(rng)).take(n).collect();
        // set a random challenge for the random linear combination
        let r = Fr::rand(rng);

        // setup params for Pedersen & KZG
        let pedersen_params = Pedersen::<G1>::new_params(rng, n);
        let (kzg_pk, kzg_vk): (ProverKey<G1>, VerifierKey<Bn254>) =
            KZGSetup::<Bn254>::setup(rng, n);

        // Pedersen commit the two vectors and return their random linear combination and proof
        let (pedersen_cm, pedersen_proof) = commit_rlc_and_prove::<G1, Pedersen<G1>>(
            &poseidon_config,
            &pedersen_params,
            r,
            &v_1,
            &v_2,
        )
        .unwrap();

        // KZG commit the two vectors and return their random linear combination and proof
        let (kzg_cm, kzg_proof) =
            commit_rlc_and_prove::<G1, KZGProver<G1>>(&poseidon_config, &kzg_pk, r, &v_1, &v_2)
                .unwrap();

        // verify Pedersen
        let transcript_v = &mut PoseidonTranscript::<G1>::new(&poseidon_config);
        Pedersen::<G1>::verify(&pedersen_params, transcript_v, pedersen_cm, pedersen_proof)
            .unwrap();

        // verify KZG
        let transcript_v = &mut PoseidonTranscript::<G1>::new(&poseidon_config);
        transcript_v.absorb_point(&kzg_cm).unwrap();
        let challenge = transcript_v.get_challenge();
        // verify the KZG proof using arkworks method
        assert!(KZG10::<Bn254, DensePolynomial<Fr>>::check(
            &kzg_vk,
            &KZG10Commitment(kzg_cm.into_affine()),
            challenge,
            kzg_proof.0, // eval
            &KZG10Proof::<Bn254> {
                w: kzg_proof.1.into_affine(), // proof
                random_v: None,
            },
        )
        .unwrap());
    }
}
