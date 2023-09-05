use ark_crypto_primitives::sponge::{
    constraints::CryptographicSpongeVar,
    poseidon::{constraints::PoseidonSpongeVar, PoseidonConfig, PoseidonSponge},
    Absorb, CryptographicSponge,
};
use ark_ec::{AffineRepr, CurveGroup, Group};
use ark_ff::{BigInteger, Field, PrimeField};
use ark_r1cs_std::{boolean::Boolean, fields::fp::FpVar};
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
    fn get_challenge_nbits(&mut self, nbits: usize) -> Vec<bool> {
        self.sponge.squeeze_bits(nbits)
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

    /// returns the bit representation of the challenge, we use its output in-circuit for the
    /// `GC.scalar_mul_le` method.
    pub fn get_challenge_nbits(&mut self, nbits: usize) -> Result<Vec<Boolean<F>>, SynthesisError> {
        self.sponge.squeeze_bits(nbits)
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
    use ark_crypto_primitives::sponge::poseidon::find_poseidon_ark_and_mds;
    use ark_pallas::{constraints::GVar, Fq, Fr, Projective};
    use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar, groups::CurveVar, R1CSVar};
    use ark_relations::r1cs::ConstraintSystem;
    use ark_vesta::Projective as E2Projective;
    use std::ops::Mul;

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
    fn test_transcript_and_transcriptvar_get_challenge() {
        // use 'native' transcript
        let config = poseidon_test_config::<Fr>();
        let mut tr = PoseidonTranscript::<Projective>::new(&config);
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

    #[test]
    fn test_transcript_and_transcriptvar_nbits() {
        let nbits = crate::constants::N_BITS_CHALLENGE;

        // use 'native' transcript
        let config = poseidon_test_config::<Fq>();
        let mut tr = PoseidonTranscript::<E2Projective>::new(&config);
        tr.absorb(&Fq::from(42_u32));

        // get challenge from native transcript
        let c_bits = tr.get_challenge_nbits(nbits);

        // use 'gadget' transcript
        let cs = ConstraintSystem::<Fq>::new_ref();
        let mut tr_var = PoseidonTranscriptVar::<Fq>::new(cs.clone(), &config);
        let v = FpVar::<Fq>::new_witness(cs.clone(), || Ok(Fq::from(42_u32))).unwrap();
        tr_var.absorb(v).unwrap();

        // get challenge from circuit transcript
        let c_var = tr_var.get_challenge_nbits(nbits).unwrap();

        let P = Projective::generator();
        let PVar = GVar::new_witness(cs.clone(), || Ok(P)).unwrap();

        // multiply point P by the challenge in different formats, to ensure that we get the same
        // result natively and in-circuit

        // native c*P
        let c_Fr = Fr::from_bigint(BigInteger::from_bits_le(&c_bits)).unwrap();
        let cP_native = P.mul(c_Fr);

        // native c*P using mul_bits_be (notice the .rev to convert the LE to BE)
        let cP_native_bits = P.mul_bits_be(c_bits.into_iter().rev());

        // in-circuit c*P using scalar_mul_le
        let cPVar = PVar.scalar_mul_le(c_var.iter()).unwrap();

        // check that they are equal
        assert_eq!(
            cP_native.into_affine(),
            cPVar.value().unwrap().into_affine()
        );
        assert_eq!(
            cP_native_bits.into_affine(),
            cPVar.value().unwrap().into_affine()
        );
    }
}
