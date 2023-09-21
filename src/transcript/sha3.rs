use std::marker::PhantomData;
use sha3::{Shake256, digest::*};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{BigInteger, Field, PrimeField};

use crate::transcript::Transcript;

/// KecccakTranscript implements the Transcript trait using the Keccak hash
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
        self.sponge.update(&prepare_point(p))
    }

    fn get_challenge(&mut self) -> C::ScalarField {
        let output = self.sponge.clone().finalize_boxed(200);
        self.sponge.update(&[output[0]]);
        C::ScalarField::from_le_bytes_mod_order(&[output[0]])
    }
    fn get_challenge_nbits(&mut self, nbits: usize) -> Vec<bool> {
        // TODO
        // should call finalize() then slice the output to n bit challenge
        vec![]
    }
    fn get_challenges(&mut self, n: usize) -> Vec<C::ScalarField> {
        let output = self.sponge.clone().finalize_boxed(n);
        self.sponge.update(&[output[0]]);

        let c = output
            .iter()
            .map(|c| C::ScalarField::from_le_bytes_mod_order(&[*c]))
            .collect();
        c
    }
}

// Returns the point coordinates in Fr, so it can be absrobed by the transcript. It does not work
// over bytes in order to have a logic that can be reproduced in-circuit.
fn prepare_point<C: CurveGroup>(p: &C) -> Vec<u8> {
    let binding = p.into_affine();
    let p_coords = &binding.xy().unwrap();
    let x_bi = p_coords
        .0
        .to_base_prime_field_elements()
        .next()
        .expect("a")
        .into_bigint()
        .to_bytes_le();
    let mut y_bi = p_coords
        .1
        .to_base_prime_field_elements()
        .next()
        .expect("a")
        .into_bigint()
        .to_bytes_le();

    y_bi.extend(x_bi);
    y_bi
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
    fn test_transcript_and_transcriptvar_get_challenge() {
        // use 'native' transcript
        let config = sha3_test_config::<Fr>();
        let mut tr = SHA3Transcript::<Projective>::new(&config);
        tr.absorb(&Fr::from(42_u32));
        let c = tr.get_challenge();
        
        // TODO
        // assert_eq!();
    }

    #[test]
    fn test_transcript_get_challenge() {
        let mut rng = ark_std::test_rng();

        const n: usize = 10;
        let config = sha3_test_config::<Fr>();

        // init transcript
        let mut transcript = SHA3Transcript::<Projective>::new(&config);
        let v: Vec<Fr> = vec![Fr::rand(&mut rng); n];
        let challenges = transcript.get_challenges(v.len());
        assert_eq!(challenges.len(), n);
    }
}
