use ark_crypto_primitives::sponge::{
    constraints::CryptographicSpongeVar,
    poseidon::{constraints::PoseidonSpongeVar, PoseidonConfig, PoseidonSponge},
    Absorb, CryptographicSponge,
};
use ark_ec::{CurveGroup, Group};
use ark_ff::{BigInteger, PrimeField};
use ark_r1cs_std::{boolean::Boolean, fields::fp::FpVar, ToConstraintFieldGadget};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};

use crate::{
    folding::circuits::nonnative::affine::{
        nonnative_affine_to_field_elements, NonNativeAffineVar,
    },
    Error,
};

use super::{Transcript, TranscriptVar};

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
    fn absorb_point(&mut self, p: &C) -> Result<(), Error> {
        let (x, y) = nonnative_affine_to_field_elements(*p)?;
        self.sponge.absorb(&[x, y].concat());
        Ok(())
    }
    fn get_challenge(&mut self) -> C::ScalarField {
        let c = self.sponge.squeeze_field_elements(1);
        self.sponge.absorb(&c[0]);
        c[0]
    }
    fn get_challenge_nbits(&mut self, nbits: usize) -> Vec<bool> {
        let bits = self.sponge.squeeze_bits(nbits);
        self.sponge.absorb(&C::ScalarField::from(
            <C::ScalarField as PrimeField>::BigInt::from_bits_le(&bits),
        ));
        bits
    }
    fn get_challenges(&mut self, n: usize) -> Vec<C::ScalarField> {
        let c = self.sponge.squeeze_field_elements(n);
        self.sponge.absorb(&c);
        c
    }
}

/// PoseidonTranscriptVar implements the gadget compatible with PoseidonTranscript
pub struct PoseidonTranscriptVar<F: PrimeField> {
    sponge: PoseidonSpongeVar<F>,
}
impl<F: PrimeField> TranscriptVar<F> for PoseidonTranscriptVar<F> {
    type TranscriptVarConfig = PoseidonConfig<F>;

    fn new(cs: ConstraintSystemRef<F>, poseidon_config: &Self::TranscriptVarConfig) -> Self {
        let sponge = PoseidonSpongeVar::<F>::new(cs, poseidon_config);
        Self { sponge }
    }
    fn absorb(&mut self, v: &FpVar<F>) -> Result<(), SynthesisError> {
        self.sponge.absorb(v)
    }
    fn absorb_vec(&mut self, v: &[FpVar<F>]) -> Result<(), SynthesisError> {
        self.sponge.absorb(&v)
    }
    fn absorb_point<C: CurveGroup<ScalarField = F>>(
        &mut self,
        v: &NonNativeAffineVar<C>,
    ) -> Result<(), SynthesisError> {
        self.sponge.absorb(&v.to_constraint_field()?)
    }
    fn get_challenge(&mut self) -> Result<FpVar<F>, SynthesisError> {
        let c = self.sponge.squeeze_field_elements(1)?;
        self.sponge.absorb(&c[0])?;
        Ok(c[0].clone())
    }

    /// returns the bit representation of the challenge, we use its output in-circuit for the
    /// `GC.scalar_mul_le` method.
    fn get_challenge_nbits(&mut self, nbits: usize) -> Result<Vec<Boolean<F>>, SynthesisError> {
        let bits = self.sponge.squeeze_bits(nbits)?;
        self.sponge.absorb(&Boolean::le_bits_to_fp_var(&bits)?)?;
        Ok(bits)
    }
    fn get_challenges(&mut self, n: usize) -> Result<Vec<FpVar<F>>, SynthesisError> {
        let c = self.sponge.squeeze_field_elements(n)?;
        self.sponge.absorb(&c)?;
        Ok(c)
    }
}

/// WARNING the method poseidon_test_config is for tests only
pub fn poseidon_test_config<F: PrimeField>() -> PoseidonConfig<F> {
    let full_rounds = 8;
    let partial_rounds = 31;
    let alpha = 5;
    let rate = 2;

    let (ark, mds) = ark_crypto_primitives::sponge::poseidon::find_poseidon_ark_and_mds::<F>(
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

#[cfg(test)]
pub mod tests {
    use super::*;
    use ark_ff::UniformRand;
    use ark_pallas::{constraints::GVar, Fq, Fr, Projective};
    use ark_r1cs_std::{alloc::AllocVar, groups::CurveVar, R1CSVar};
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::test_rng;
    use ark_vesta::Projective as E2Projective;
    use std::ops::Mul;

    #[test]
    fn test_transcript_and_transcriptvar_absorb_point() {
        // use 'native' transcript
        let config = poseidon_test_config::<Fr>();
        let mut tr = PoseidonTranscript::<Projective>::new(&config);
        let rng = &mut test_rng();

        let p = Projective::rand(rng);
        tr.absorb_point(&p).unwrap();
        let c = tr.get_challenge();

        // use 'gadget' transcript
        let cs = ConstraintSystem::<Fr>::new_ref();
        let mut tr_var = PoseidonTranscriptVar::<Fr>::new(cs.clone(), &config);
        let p_var = NonNativeAffineVar::<Projective>::new_witness(
            ConstraintSystem::<Fr>::new_ref(),
            || Ok(p),
        )
        .unwrap();
        tr_var.absorb_point(&p_var).unwrap();
        let c_var = tr_var.get_challenge().unwrap();

        // assert that native & gadget transcripts return the same challenge
        assert_eq!(c, c_var.value().unwrap());
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
        tr_var.absorb(&v).unwrap();
        let c_var = tr_var.get_challenge().unwrap();

        // assert that native & gadget transcripts return the same challenge
        assert_eq!(c, c_var.value().unwrap());
    }

    #[test]
    fn test_transcript_and_transcriptvar_nbits() {
        let nbits = crate::constants::N_BITS_RO;

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
        tr_var.absorb(&v).unwrap();

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
