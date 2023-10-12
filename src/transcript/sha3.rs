use std::marker::PhantomData;
use sha3::{Shake256, digest::*};
use ark_ec::CurveGroup;
use ark_ff::{BigInteger, PrimeField};

use crate::transcript::Transcript;

/// SHA3Transcript implements the Transcript trait using the Keccak hash
pub struct SHA3Transcript<C: CurveGroup> {
    sponge: Shake256,
    phantom: PhantomData<C>,
}

#[derive(Debug)]
pub struct SHA3Config {}

impl<C: CurveGroup> Transcript<C> for SHA3Transcript<C> {
    type TranscriptConfig = SHA3Config;
    fn new(config: &Self::TranscriptConfig) -> Self {
        let _ = config;
        let sponge = Shake256::default();
        Self {
            sponge,
            phantom: PhantomData,
        }
    }

    fn absorb(&mut self, v: &C::ScalarField) {
        self.sponge.update(&(v.into_bigint().to_bytes_le()));
    }
    fn absorb_vec(&mut self, v: &[C::ScalarField]) {
        for _v in v {
            self.sponge.update(&(_v.into_bigint().to_bytes_le()));
        }
    }
    fn absorb_point(&mut self, p: &C) {
        let mut serialized = vec![];
        p.serialize_compressed(&mut serialized).unwrap();
        self.sponge.update(&(serialized))
    }
    fn get_challenge(&mut self) -> C::ScalarField {
        let output = self.sponge.clone().finalize_boxed(200);
        C::ScalarField::from_le_bytes_mod_order(&[output[0]])
    }
    fn get_challenge_nbits(&mut self, nbits: usize) -> Vec<bool> {
        // TODO
        // should call finalize() then slice the output to n bit challenge
        vec![]
    }
    fn get_challenges(&mut self, n: usize) -> Vec<C::ScalarField> {
        let output = self.sponge.clone().finalize_boxed(n);

        let c = output
            .iter()
            .map(|c| C::ScalarField::from_le_bytes_mod_order(&[*c]))
            .collect();
        c
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use ark_pallas::{
        // constraints::GVar,
        Fr, Projective
    };
    use ark_std::UniformRand;

    /// WARNING the method poseidon_test_config is for tests only
    #[cfg(test)]
    pub fn sha3_test_config<F: PrimeField>() -> SHA3Config {
        SHA3Config {}
    }

    #[test]
    fn test_transcript_get_challenges_len() {
        let mut rng = ark_std::test_rng();

        const n: usize = 10;
        let config = sha3_test_config::<Fr>();

        // init transcript
        let mut transcript = SHA3Transcript::<Projective>::new(&config);
        let v: Vec<Fr> = vec![Fr::rand(&mut rng); n];
        let challenges = transcript.get_challenges(v.len());
        assert_eq!(challenges.len(), n);
    }

    #[test]
    fn test_transcript_get_challenge() {
        let config = sha3_test_config::<Fr>();
        // init transcript
        let mut transcript = SHA3Transcript::<Projective>::new(&config);
        transcript.absorb(&Fr::from(42_u32));
        let c = transcript.get_challenge();
        let c_2 = transcript.get_challenge();
        assert_eq!(c, c_2);
    }
}
