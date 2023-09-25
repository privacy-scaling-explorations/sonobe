use std::marker::PhantomData;
use tiny_keccak::{Keccak, Hasher};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{BigInteger, Field, PrimeField};

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
        self.sponge.update(&prepare_point(p))
    }
    fn get_challenge(&mut self) -> C::ScalarField {
        let mut output = [0u8; 32];
        self.sponge.clone().finalize(&mut output);
        self.sponge.update(&[output[0]]);
        C::ScalarField::from_le_bytes_mod_order(&[output[0]])
    }
    fn get_challenge_nbits(&mut self, nbits: usize) -> Vec<bool> {
        // TODO
        vec![]
    }
    fn get_challenges(&mut self, n: usize) -> Vec<C::ScalarField> {
        let mut output = [0u8; 32];
        self.sponge.clone().finalize(&mut output);
        self.sponge.update(&[output[0]]);

        let c: Vec<C::ScalarField> = output
            .iter()
            .map(|c| C::ScalarField::from_le_bytes_mod_order(&[*c]))
            .collect();
        c[..n].to_vec()
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
    pub fn keccak_test_config<F: PrimeField>() -> KeccakConfig {
        KeccakConfig {}
    }

    #[test]
    fn test_transcript_get_challenge() {
        let mut rng = ark_std::test_rng();

        const n: usize = 10;
        let config = keccak_test_config::<Fr>();

        // init transcript
        let mut transcript = KeccakTranscript::<Projective>::new(&config);
        let v: Vec<Fr> = vec![Fr::rand(&mut rng); n];
        let challenges = transcript.get_challenges(v.len());
        assert_eq!(challenges.len(), n);
    }
}
