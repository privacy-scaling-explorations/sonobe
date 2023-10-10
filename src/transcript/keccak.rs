use std::marker::PhantomData;
use tiny_keccak::{Keccak, Hasher};
use ark_ec::CurveGroup;
use ark_ff::{BigInteger, PrimeField};

use crate::transcript::Transcript;

/// KecccakTranscript implements the Transcript trait using the Keccak hash
pub struct KeccakTranscript<C: CurveGroup> {
    sponge: Keccak,
    phantom: PhantomData<C>,
}

#[derive(Debug)]
pub struct KeccakConfig {}

impl<C: CurveGroup> Transcript<C> for KeccakTranscript<C> {
    type TranscriptConfig = KeccakConfig;
    fn new(config: &Self::TranscriptConfig) -> Self {
        let _ = config;
        let sponge = Keccak::v256();
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
        let mut output = [0u8; 32];
        self.sponge.clone().finalize(&mut output);
        C::ScalarField::from_le_bytes_mod_order(&[output[0]])
    }
    fn get_challenge_nbits(&mut self, nbits: usize) -> Vec<bool> {
        // TODO
        vec![]
    }
    fn get_challenges(&mut self, n: usize) -> Vec<C::ScalarField> {
        let mut output = [0u8; 32];
        self.sponge.clone().finalize(&mut output);

        let c: Vec<C::ScalarField> = output
            .iter()
            .map(|c| C::ScalarField::from_le_bytes_mod_order(&[*c]))
            .collect();
        c[..n].to_vec()
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
    pub fn keccak_test_config<F: PrimeField>() -> KeccakConfig {
        KeccakConfig {}
    }

    #[test]
    fn test_transcript_get_challenges_len() {
        let mut rng = ark_std::test_rng();

        const n: usize = 10;
        let config = keccak_test_config::<Fr>();

        // init transcript
        let mut transcript = KeccakTranscript::<Projective>::new(&config);
        let v: Vec<Fr> = vec![Fr::rand(&mut rng); n];
        let challenges = transcript.get_challenges(v.len());
        assert_eq!(challenges.len(), n);
    }

    #[test]
    fn test_transcript_get_challenge() {
        let config = keccak_test_config::<Fr>();
        // init transcript
        let mut transcript = KeccakTranscript::<Projective>::new(&config);
        transcript.absorb(&Fr::from(42_u32));
        let c = transcript.get_challenge();
        let c_2 = transcript.get_challenge();
        assert_eq!(c, c_2);
    }
}
