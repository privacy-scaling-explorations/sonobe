use ark_crypto_primitives::sponge::{
    constraints::CryptographicSpongeVar,
    poseidon::{constraints::PoseidonSpongeVar, PoseidonConfig, PoseidonSponge},
    Absorb, CryptographicSponge,
};
use ark_ff::PrimeField;
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};

use crate::Transcript;

/// PoseidonTranscript implements the Transcript trait using the Poseidon hash
pub struct PoseidonTranscript<F: PrimeField + Absorb> {
    sponge: PoseidonSponge<F>,
}
impl<F: PrimeField + Absorb> Transcript<F> for PoseidonTranscript<F> {
    type TranscriptConfig = PoseidonConfig<F>;

    fn new(poseidon_config: &Self::TranscriptConfig) -> Self {
        let sponge = PoseidonSponge::<F>::new(poseidon_config);
        Self { sponge }
    }
    fn absorb(&mut self, v: &F) {
        self.sponge.absorb(&v);
    }
    fn absorb_vec(&mut self, v: &[F]) {
        self.sponge.absorb(&v);
    }
    fn get_challenge(&mut self) -> F {
        let c = self.sponge.squeeze_field_elements(1);
        self.sponge.absorb(&c[0]);
        c[0]
    }
    fn get_challenges(&mut self, n: usize) -> Vec<F> {
        let c = self.sponge.squeeze_field_elements(n);
        self.sponge.absorb(&c);
        c
    }
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
mod tests {
    use super::*;
    use ark_bls12_381::Fr;
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
        let mut tr = PoseidonTranscript::<Fr>::new(&config);
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
