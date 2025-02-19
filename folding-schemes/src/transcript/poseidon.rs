use ark_crypto_primitives::sponge::{
    constraints::CryptographicSpongeVar,
    poseidon::{constraints::PoseidonSpongeVar, PoseidonConfig, PoseidonSponge},
    Absorb, CryptographicSponge,
};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{BigInteger, PrimeField};
use ark_r1cs_std::{boolean::Boolean, fields::fp::FpVar, groups::CurveVar};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};

use super::{AbsorbNonNative, AbsorbNonNativeGadget, Transcript, TranscriptVar};

impl<F: PrimeField + Absorb> Transcript<F> for PoseidonSponge<F> {
    fn new_with_pp_hash(config: &Self::Config, pp_hash: F) -> Self {
        let mut sponge = Self::new(config);
        sponge.absorb(&pp_hash);
        sponge
    }

    // Compatible with the in-circuit `TranscriptVar::absorb_point`
    fn absorb_point<C: CurveGroup<BaseField = F>>(&mut self, p: &C) {
        let (x, y) = p.into_affine().xy().unwrap_or_default();
        self.absorb(&x);
        self.absorb(&y);
    }
    fn absorb_nonnative<V: AbsorbNonNative>(&mut self, v: &V) {
        self.absorb(&v.to_native_sponge_field_elements_as_vec::<F>());
    }
    fn get_challenge(&mut self) -> F {
        let c = self.squeeze_field_elements(1);
        self.absorb(&c[0]);
        c[0]
    }
    fn get_challenge_nbits(&mut self, nbits: usize) -> Vec<bool> {
        let bits = self.squeeze_bits(nbits);
        self.absorb(&F::from(F::BigInt::from_bits_le(&bits)));
        bits
    }
    fn get_challenges(&mut self, n: usize) -> Vec<F> {
        let c = self.squeeze_field_elements(n);
        self.absorb(&c);
        c
    }
}

impl<F: PrimeField> TranscriptVar<F, PoseidonSponge<F>> for PoseidonSpongeVar<F> {
    fn new_with_pp_hash(
        config: &Self::Parameters,
        pp_hash: &FpVar<F>,
    ) -> Result<Self, SynthesisError> {
        let mut sponge = Self::new(ConstraintSystemRef::None, config);
        sponge.absorb(&pp_hash)?;
        Ok(sponge)
    }

    fn absorb_point<C: CurveGroup<BaseField = F>, GC: CurveVar<C, F>>(
        &mut self,
        v: &GC,
    ) -> Result<(), SynthesisError> {
        let mut vec = v.to_constraint_field()?;
        // The last element in the vector tells whether the point is infinity,
        // but we can in fact avoid absorbing it without loss of soundness.
        // This is because the `to_constraint_field` method internally invokes
        // [`ProjectiveVar::to_afine`](https://github.com/arkworks-rs/r1cs-std/blob/4020fbc22625621baa8125ede87abaeac3c1ca26/src/groups/curves/short_weierstrass/mod.rs#L160-L195),
        // which guarantees that an infinity point is represented as `(0, 0)`,
        // but the y-coordinate of a non-infinity point is never 0 (for why, see
        // https://crypto.stackexchange.com/a/108242 ).
        vec.pop();
        self.absorb(&vec)
    }
    fn absorb_nonnative<V: AbsorbNonNativeGadget<F>>(
        &mut self,
        v: &V,
    ) -> Result<(), SynthesisError> {
        self.absorb(&v.to_native_sponge_field_elements()?)
    }
    fn get_challenge(&mut self) -> Result<FpVar<F>, SynthesisError> {
        let c = self.squeeze_field_elements(1)?;
        self.absorb(&c[0])?;
        Ok(c[0].clone())
    }

    /// returns the bit representation of the challenge, we use its output in-circuit for the
    /// `GC.scalar_mul_le` method.
    fn get_challenge_nbits(&mut self, nbits: usize) -> Result<Vec<Boolean<F>>, SynthesisError> {
        let bits = self.squeeze_bits(nbits)?;
        self.absorb(&Boolean::le_bits_to_fp(&bits)?)?;
        Ok(bits)
    }
    fn get_challenges(&mut self, n: usize) -> Result<Vec<FpVar<F>>, SynthesisError> {
        let c = self.squeeze_field_elements(n)?;
        self.absorb(&c)?;
        Ok(c)
    }
}

/// This Poseidon configuration generator agrees with Circom's Poseidon(4) in the case of BN254's scalar field
pub fn poseidon_canonical_config<F: PrimeField>() -> PoseidonConfig<F> {
    // 120 bit security target as in
    // https://eprint.iacr.org/2019/458.pdf
    // t = rate + 1

    let full_rounds = 8;
    let partial_rounds = 60;
    let alpha = 5;
    let rate = 4;

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
    use ark_bn254::{constraints::GVar, g1::Config, Fq, Fr, G1Projective as G1};
    use ark_ec::PrimeGroup;
    use ark_ff::UniformRand;
    use ark_r1cs_std::{
        alloc::AllocVar, groups::curves::short_weierstrass::ProjectiveVar, R1CSVar,
    };
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::test_rng;

    use super::*;
    use crate::folding::circuits::nonnative::affine::NonNativeAffineVar;
    use crate::Error;

    // Test with value taken from https://github.com/iden3/circomlibjs/blob/43cc582b100fc3459cf78d903a6f538e5d7f38ee/test/poseidon.js#L32
    #[test]
    fn check_against_circom_poseidon() -> Result<(), Error> {
        use ark_bn254::Fr;
        use ark_crypto_primitives::sponge::{poseidon::PoseidonSponge, CryptographicSponge};
        use std::str::FromStr;

        let config = poseidon_canonical_config::<Fr>();
        let mut poseidon_sponge: PoseidonSponge<_> = CryptographicSponge::new(&config);
        let v: Vec<Fr> = vec!["1", "2", "3", "4"]
            .into_iter()
            .map(|x| {
                Fr::from_str(x).map_err(|_| {
                    Error::ConversionError("str".to_string(), "Fr".to_string(), x.to_string())
                })
            })
            .collect::<Result<Vec<Fr>, Error>>()?;
        poseidon_sponge.absorb(&v);
        poseidon_sponge.squeeze_field_elements::<Fr>(1);
        assert!(
            poseidon_sponge.state[0]
                == Fr::from_str(
                    "18821383157269793795438455681495246036402687001665670618754263018637548127333"
                )
                .map_err(|_| {
                    Error::ConversionError(
                        "str".to_string(),
                        "Fr".to_string(),
                        "hardcoded string".to_string(),
                    )
                })?
        );
        Ok(())
    }

    #[test]
    fn test_transcript_and_transcriptvar_absorb_native_point() -> Result<(), Error> {
        // use 'native' transcript
        let config = poseidon_canonical_config::<Fq>();
        let mut tr = PoseidonSponge::<Fq>::new(&config);
        let rng = &mut test_rng();

        let p = G1::rand(rng);
        tr.absorb_point(&p);
        let c = tr.get_challenge();

        // use 'gadget' transcript
        let cs = ConstraintSystem::<Fq>::new_ref();
        let mut tr_var = PoseidonSpongeVar::<Fq>::new(cs.clone(), &config);
        let p_var = ProjectiveVar::<Config, FpVar<Fq>>::new_witness(
            ConstraintSystem::<Fq>::new_ref(),
            || Ok(p),
        )?;
        tr_var.absorb_point(&p_var)?;
        let c_var = tr_var.get_challenge()?;

        // assert that native & gadget transcripts return the same challenge
        assert_eq!(c, c_var.value()?);
        Ok(())
    }

    #[test]
    fn test_transcript_and_transcriptvar_absorb_nonnative_point() -> Result<(), Error> {
        // use 'native' transcript
        let config = poseidon_canonical_config::<Fr>();
        let mut tr = PoseidonSponge::<Fr>::new(&config);
        let rng = &mut test_rng();

        let p = G1::rand(rng);
        tr.absorb_nonnative(&p);
        let c = tr.get_challenge();

        // use 'gadget' transcript
        let cs = ConstraintSystem::<Fr>::new_ref();
        let mut tr_var = PoseidonSpongeVar::<Fr>::new(cs.clone(), &config);
        let p_var =
            NonNativeAffineVar::<G1>::new_witness(ConstraintSystem::<Fr>::new_ref(), || Ok(p))?;
        tr_var.absorb_nonnative(&p_var)?;
        let c_var = tr_var.get_challenge()?;

        // assert that native & gadget transcripts return the same challenge
        assert_eq!(c, c_var.value()?);
        Ok(())
    }

    #[test]
    fn test_transcript_and_transcriptvar_get_challenge() -> Result<(), Error> {
        // use 'native' transcript
        let config = poseidon_canonical_config::<Fr>();
        let mut tr = PoseidonSponge::<Fr>::new(&config);
        tr.absorb(&Fr::from(42_u32));
        let c = tr.get_challenge();

        // use 'gadget' transcript
        let cs = ConstraintSystem::<Fr>::new_ref();
        let mut tr_var = PoseidonSpongeVar::<Fr>::new(cs.clone(), &config);
        let v = FpVar::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(42_u32)))?;
        tr_var.absorb(&v)?;
        let c_var = tr_var.get_challenge()?;

        // assert that native & gadget transcripts return the same challenge
        assert_eq!(c, c_var.value()?);
        Ok(())
    }

    #[test]
    fn test_transcript_and_transcriptvar_nbits() -> Result<(), Error> {
        let nbits = crate::constants::NOVA_N_BITS_RO;

        // use 'native' transcript
        let config = poseidon_canonical_config::<Fq>();
        let mut tr = PoseidonSponge::<Fq>::new(&config);
        tr.absorb(&Fq::from(42_u32));

        // get challenge from native transcript
        let c_bits = tr.get_challenge_nbits(nbits);

        // use 'gadget' transcript
        let cs = ConstraintSystem::<Fq>::new_ref();
        let mut tr_var = PoseidonSpongeVar::<Fq>::new(cs.clone(), &config);
        let v = FpVar::<Fq>::new_witness(cs.clone(), || Ok(Fq::from(42_u32)))?;
        tr_var.absorb(&v)?;

        // get challenge from circuit transcript
        let c_var = tr_var.get_challenge_nbits(nbits)?;

        let P = G1::generator();
        let PVar = GVar::new_witness(cs.clone(), || Ok(P))?;

        // multiply point P by the challenge in different formats, to ensure that we get the same
        // result natively and in-circuit

        // native c*P
        let c_Fr = Fr::from_bigint(BigInteger::from_bits_le(&c_bits)).ok_or(Error::OutOfBounds)?;
        let cP_native = P * c_Fr;

        // native c*P using mul_bits_be (notice the .rev to convert the LE to BE)
        let cP_native_bits = P.mul_bits_be(c_bits.into_iter().rev());

        // in-circuit c*P using scalar_mul_le
        let cPVar = PVar.scalar_mul_le(c_var.iter())?;

        // check that they are equal
        assert_eq!(cP_native.into_affine(), cPVar.value()?.into_affine());
        assert_eq!(cP_native_bits.into_affine(), cPVar.value()?.into_affine());
        Ok(())
    }
}
