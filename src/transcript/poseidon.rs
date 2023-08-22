use ark_crypto_primitives::sponge::{
    constraints::CryptographicSpongeVar,
    poseidon::{constraints::PoseidonSpongeVar, PoseidonConfig, PoseidonSponge},
    Absorb, CryptographicSponge,
};
use ark_ec::{AffineRepr, CurveGroup, Group};
use ark_ff::{BigInteger, Field, PrimeField};
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};

use crate::transcript::Transcript;

/// PoseidonTranscript implements the Transcript trait using the Poseidon hash
pub struct PoseidonTranscript<C: CurveGroup>
where
    <C as Group>::ScalarField: Absorb,
{
    sponge: PoseidonSponge<C::ScalarField>,
}

impl<C: CurveGroup> Transcript<C> for PoseidonTranscript<C>
where
    <C as Group>::ScalarField: Absorb,
{
    type TranscriptConfig = PoseidonConfig<C::ScalarField>;

    fn new(poseidon_config: &Self::TranscriptConfig) -> Self {
        let sponge = PoseidonSponge::<C::ScalarField>::new(poseidon_config);
        Self { sponge }
    }
    fn absorb(&mut self, v: &C::ScalarField) {
        self.sponge.absorb(&v);
    }
    fn absorb_vec(&mut self, v: &[C::ScalarField]) {
        self.sponge.absorb(&v);
    }
    fn absorb_point(&mut self, p: &C) {
        self.sponge.absorb(&prepare_point(p));
    }
    fn get_challenge(&mut self) -> C::ScalarField {
        let c = self.sponge.squeeze_field_elements(1);
        self.sponge.absorb(&c[0]);
        c[0]
    }
    fn get_challenges(&mut self, n: usize) -> Vec<C::ScalarField> {
        let c = self.sponge.squeeze_field_elements(n);
        self.sponge.absorb(&c);
        c
    }
}

// Returns the point coordinates in Fr, so it can be absrobed by the transcript. It does not work
// over bytes in order to have a logic that can be reproduced in-circuit.
fn prepare_point<C: CurveGroup>(p: &C) -> Vec<C::ScalarField> {
    let binding = p.into_affine();
    let p_coords = &binding.xy().unwrap();
    let x_bi = p_coords
        .0
        .to_base_prime_field_elements()
        .next()
        .expect("a")
        .into_bigint();
    let y_bi = p_coords
        .1
        .to_base_prime_field_elements()
        .next()
        .expect("a")
        .into_bigint();
    vec![
        C::ScalarField::from_le_bytes_mod_order(x_bi.to_bytes_le().as_ref()),
        C::ScalarField::from_le_bytes_mod_order(y_bi.to_bytes_le().as_ref()),
    ]
}

/// PoseidonTranscriptVar implements the gadget compatible with PoseidonTranscript
pub struct PoseidonTranscriptVar<F: PrimeField> {
    sponge: PoseidonSpongeVar<F>,
}
impl<F: PrimeField> PoseidonTranscriptVar<F> {
    pub fn new(cs: ConstraintSystemRef<F>, poseidon_config: &PoseidonConfig<F>) -> Self {
        let sponge = PoseidonSpongeVar::<F>::new(cs, poseidon_config);
        Self { sponge }
    }
    pub fn absorb(&mut self, v: FpVar<F>) -> Result<(), SynthesisError> {
        self.sponge.absorb(&v)
    }
    pub fn absorb_vec(&mut self, v: &[FpVar<F>]) -> Result<(), SynthesisError> {
        self.sponge.absorb(&v)
    }
    pub fn get_challenge(&mut self) -> Result<FpVar<F>, SynthesisError> {
        let c = self.sponge.squeeze_field_elements(1)?;
        self.sponge.absorb(&c[0])?;
        Ok(c[0].clone())
    }
    pub fn get_challenges(&mut self, n: usize) -> Result<Vec<FpVar<F>>, SynthesisError> {
        let c = self.sponge.squeeze_field_elements(n)?;
        self.sponge.absorb(&c)?;
        Ok(c)
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use ark_bls12_377::{Fr, G1Projective};
    use ark_crypto_primitives::sponge::poseidon::find_poseidon_ark_and_mds;
    use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar, R1CSVar};
    use ark_relations::r1cs::ConstraintSystem;

    /// WARNING the method poseidon_test_config is for tests only
    #[cfg(test)]
    pub fn poseidon_test_config<F: PrimeField>() -> PoseidonConfig<F> {
        let full_rounds = 8;
        let partial_rounds = 31;
        let alpha = 5;
        let rate = 2;

        let (ark, mds) = find_poseidon_ark_and_mds::<F>(
            F::MODULUS_BIT_SIZE as u64,
            rate,
            full_rounds,
            partial_rounds,
            0,
        );

        PoseidonConfig::new(
            full_rounds as usize,
            partial_rounds as usize,
            alpha,
            mds,
            ark,
            rate,
            1,
        )
    }

    #[test]
    fn test_transcript_and_transcriptvar() {
        // use 'native' transcript
        let config = poseidon_test_config::<Fr>();
        let mut tr = PoseidonTranscript::<G1Projective>::new(&config);
        tr.absorb(&Fr::from(42_u32));
        let c = tr.get_challenge();

        // use 'gadget' transcript
        let cs = ConstraintSystem::<Fr>::new_ref();
        let mut tr_var = PoseidonTranscriptVar::<Fr>::new(cs.clone(), &config);
        let v = FpVar::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(42_u32))).unwrap();
        tr_var.absorb(v).unwrap();
        let c_var = tr_var.get_challenge().unwrap();

        // assert that native & gadget transcripts return the same challenge
        assert_eq!(c, c_var.value().unwrap());
    }
}
