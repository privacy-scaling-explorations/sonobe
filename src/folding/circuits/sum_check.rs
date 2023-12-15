use ark_ff::PrimeField;
use ark_poly::univariate::DensePolynomial;
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    eq::EqGadget,
    fields::fp::FpVar,
};
use ark_relations::r1cs::{Namespace, SynthesisError};
use std::borrow::Borrow;

use crate::transcript::{poseidon::PoseidonTranscriptVar, TranscriptVar};
use ark_r1cs_std::R1CSVar;

/// Heavily inspired from testudo: https://github.com/cryptonetlab/testudo/tree/master
/// Mostly changed typing to better stick to ark_poly's API
/// Uses `folding-schemes`' own `TranscriptVar` trait and `PoseidonTranscriptVar` struct

#[derive(Clone, Debug)]
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

impl<F: PrimeField> DensePolynomialVar<F> {
    pub fn eval_at_zero(&self) -> FpVar<F> {
        self.coeffs[0].clone()
    }

    pub fn eval_at_one(&self) -> FpVar<F> {
        let mut res = self.coeffs[0].clone();
        for i in 1..self.coeffs.len() {
            res = &res + &self.coeffs[i];
        }
        res
    }

    pub fn evaluate(&self, r: &FpVar<F>) -> FpVar<F> {
        let mut eval = self.coeffs[0].clone();
        let mut power = r.clone();

        for i in 1..self.coeffs.len() {
            eval += &power * &self.coeffs[i];
            power *= r;
        }
        eval
    }
}

#[derive(Clone)]
pub struct SumcheckVerificationCircuit<F: PrimeField> {
    pub prover_polys: Vec<DensePolynomial<F>>,
}

impl<F: PrimeField> SumcheckVerificationCircuit<F> {
    pub fn verify_sumcheck(
        &self,
        poly_vars: &[DensePolynomialVar<F>],
        claim_var: &FpVar<F>,
        transcript_var: &mut PoseidonTranscriptVar<F>,
    ) -> Result<(FpVar<F>, Vec<FpVar<F>>), SynthesisError> {
        let mut e_var = claim_var.clone();
        let mut r_vars: Vec<FpVar<F>> = Vec::new();

        for poly_var in poly_vars.iter() {
            let res = poly_var.eval_at_one() + poly_var.eval_at_zero();
            println!("res: {:?}, e: {:?}", res.value(), e_var.value());
            res.enforce_equal(&e_var)?;
            transcript_var.absorb_vec(&poly_var.coeffs)?;
            let r_i_var = transcript_var.get_challenge()?;
            r_vars.push(r_i_var.clone());
            e_var = poly_var.evaluate(&r_i_var.clone());
        }

        Ok((e_var, r_vars))
    }
}

#[cfg(test)]
mod tests {

    use std::sync::Arc;

    use crate::transcript::poseidon::PoseidonTranscriptVar;
    use crate::transcript::poseidon::{tests::poseidon_test_config, PoseidonTranscript};
    use crate::transcript::{Transcript, TranscriptVar};
    use crate::utils::sum_check::structs::IOPProof;
    use crate::utils::sum_check::{IOPSumCheck, SumCheck};
    use crate::utils::virtual_polynomial::VirtualPolynomial;
    use ark_ff::Field;
    use ark_pallas::{Fr, Projective};
    use ark_poly::univariate::DensePolynomial;
    use ark_poly::{DenseMultilinearExtension, DenseUVPolynomial, MultilinearExtension};
    use ark_r1cs_std::alloc::{AllocVar, AllocationMode};
    use ark_r1cs_std::fields::fp::FpVar;
    use ark_relations::r1cs::ConstraintSystem;

    use super::{DensePolynomialVar, SumcheckVerificationCircuit};

    #[test]
    fn sum_check_circuit() {
        let poseidon_config = poseidon_test_config::<Fr>();
        let mut poseidon_transcript_prove: PoseidonTranscript<Projective> =
            PoseidonTranscript::<Projective>::new(&poseidon_config);
        let cs = ConstraintSystem::<Fr>::new_ref();
        let mut rng = ark_std::test_rng();

        let poly_mle = DenseMultilinearExtension::rand(5, &mut rng);
        let virtual_poly = VirtualPolynomial::new_from_mle(&Arc::new(poly_mle), Fr::ONE);

        let sum_check: IOPProof<Fr> =
            IOPSumCheck::<Projective, PoseidonTranscript<Projective>>::prove(
                &virtual_poly,
                &mut poseidon_transcript_prove,
            )
            .unwrap();

        // initiate univariate polynomial variables
        let sumcheck_verification_circuit = SumcheckVerificationCircuit {
            prover_polys: sum_check
                .proofs
                .iter()
                .map(|message| DensePolynomial::from_coefficients_slice(&message.coeffs))
                .collect(),
        };

        let mut poly_vars = Vec::with_capacity(sumcheck_verification_circuit.prover_polys.len());
        for poly in &sumcheck_verification_circuit.prover_polys {
            let poly_var =
                DensePolynomialVar::new_variable(cs.clone(), || Ok(poly), AllocationMode::Witness)
                    .unwrap();
            poly_vars.push(poly_var);
        }

        // initiate poseidon hash variable
        let poly_num_variable = FpVar::new_variable(
            cs.clone(),
            || Ok(Fr::from(virtual_poly.aux_info.num_variables as u64)),
            AllocationMode::Witness,
        )
        .unwrap();

        let poly_max_degree = FpVar::new_variable(
            cs.clone(),
            || Ok(Fr::from(virtual_poly.aux_info.max_degree as u64)),
            AllocationMode::Witness,
        )
        .unwrap();

        let mut poseidon_var = PoseidonTranscriptVar::new(cs.clone(), &poseidon_config);
        poseidon_var.absorb(poly_num_variable).unwrap();
        poseidon_var.absorb(poly_max_degree).unwrap();

        let claim =
            IOPSumCheck::<Projective, PoseidonTranscript<Projective>>::extract_sum(&sum_check);
        let claim_var =
            FpVar::new_variable(cs.clone(), || Ok(claim), AllocationMode::Witness).unwrap();

        let res = sumcheck_verification_circuit.verify_sumcheck(
            &poly_vars,
            &claim_var,
            &mut poseidon_var,
        );

        assert!(res.is_ok());
        assert!(cs.is_satisfied().unwrap());
    }
}
