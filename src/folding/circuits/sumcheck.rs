use ark_crypto_primitives::sponge::poseidon::constraints::PoseidonSpongeVar;
use ark_ff::PrimeField;
use ark_poly::univariate::DensePolynomial;
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    fields::fp::FpVar,
};
use ark_relations::r1cs::{ConstraintSystemRef, Namespace, SynthesisError};
use std::borrow::Borrow;

/// Heavily inspired from testudo: https://github.com/cryptonetlab/testudo/tree/master
/// Mostly changed typing to better stick to ark_poly's API

#[derive(Clone)]
pub struct DensePolynomialVar<F: PrimeField> {
    pub coeffs: Vec<FpVar<F>>,
}

impl<F: PrimeField> AllocVar<DensePolynomial<F>, F> for DensePolynomialVar<F> {
    fn new_variable<T: Borrow<DensePolynomial<F>>>(
        cs: impl Into<Namespace<F>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|c| {
            let cs = cs.into();
            let cp: &DensePolynomial<F> = c.borrow();
            let mut coeffs_var = Vec::<FpVar<F>>::with_capacity(cp.coeffs.len());
            for coeff in cp.coeffs.iter() {
                let coeff_var = FpVar::<F>::new_variable(cs.clone(), || Ok(coeff), mode)?;
                coeffs_var.push(coeff_var);
            }
            Ok(Self { coeffs: coeffs_var })
        })
    }
}

pub struct PoseidonTranscriptVar<F>
where
    F: PrimeField,
{
    pub cs: ConstraintSystemRef<F>,
    pub sponge: PoseidonSpongeVar<F>,
}

impl<F> PoseidonTranscriptVar<F>
where
    F: PrimeField,
{
    fn new(cs: ConstraintSystemRef<F>, params: &PoseidonConfig<F>, c_var: FpVar<F>) -> Self {
        let mut sponge = PoseidonSpongeVar::new(cs.clone(), params);

        sponge.absorb(&c_var).unwrap();

        Self { cs, sponge }
    }

    fn append(&mut self, input: &FpVar<F>) -> Result<(), SynthesisError> {
        self.sponge.absorb(&input)
    }

    fn append_vector(&mut self, input_vec: &[FpVar<F>]) -> Result<(), SynthesisError> {
        for input in input_vec.iter() {
            self.append(input)?;
        }
        Ok(())
    }

    fn challenge(&mut self) -> Result<FpVar<F>, SynthesisError> {
        Ok(self.sponge.squeeze_field_elements(1).unwrap().remove(0))
    }

    fn challenge_scalar_vec(&mut self, len: usize) -> Result<Vec<FpVar<F>>, SynthesisError> {
        let c_vars = self.sponge.squeeze_field_elements(len).unwrap();
        Ok(c_vars)
    }
}

#[derive(Clone)]
pub struct SumcheckVerificationCircuit<F: PrimeField> {
    pub polys: Vec<DensePolynomial<F>>,
}

impl<F: PrimeField> SumcheckVerificationCircuit<F> {
    fn verify_sumcheck(
        &self,
        poly_vars: &[DensePolynomialVar<F>],
        claim_var: &FpVar<F>,
        transcript_var: &mut PoseidonTranscriptVar<F>,
    ) -> Result<(FpVar<F>, Vec<FpVar<F>>), SynthesisError> {
        let mut e_var = claim_var.clone();
        let mut r_vars: Vec<FpVar<F>> = Vec::new();

        for (poly_var, _poly) in poly_vars.iter().zip(self.polys.iter()) {
            let res = poly_var.eval_at_one() + poly_var.eval_at_zero();
            res.enforce_equal(&e_var)?;
            transcript_var.append_vector(&poly_var.coeffs)?;
            let r_i_var = transcript_var.challenge()?;
            r_vars.push(r_i_var.clone());
            e_var = poly_var.evaluate(&r_i_var.clone());
        }

        Ok((e_var, r_vars))
    }
}

#[cfg(test)]
mod tests {

    use crate::transcript::poseidon::{tests::poseidon_test_config, PoseidonTranscript};
    use crate::transcript::Transcript;
    use ark_crypto_primitives::sponge::constraints::CryptographicSpongeVar;
    use ark_crypto_primitives::sponge::poseidon::constraints::PoseidonSpongeVar;
    use ark_ff::PrimeField;
    use ark_pallas::{Fr, Projective};
    use ark_r1cs_std::alloc::{AllocVar, AllocationMode};
    use ark_r1cs_std::fields::fp::FpVar;
    use ark_r1cs_std::R1CSVar;
    use ark_relations::r1cs::ConstraintSystem;

    #[test]
    fn test_poseidon_circuit() {
        // check how hashing works and get value to correspond
        let poseidon_config = poseidon_test_config::<Fr>();
        let mut transcript: PoseidonTranscript<Projective> =
            PoseidonTranscript::<Projective>::new(&poseidon_config);

        let to_hash: Fr = Fr::from_le_bytes_mod_order(b"test");
        transcript.absorb(&to_hash);
        let challenge = transcript.get_challenge();

        let cs = ConstraintSystem::<Fr>::new_ref();

        let mut poseidon_var = PoseidonSpongeVar::new(cs.clone(), &poseidon_config);
        let to_hash_var =
            FpVar::new_variable(cs.clone(), || Ok(to_hash), AllocationMode::Witness).unwrap();

        poseidon_var.absorb(&to_hash_var).unwrap();
        let hash_var: &FpVar<Fr> = &(poseidon_var.squeeze_field_elements(1).unwrap())[0];
    }
}
