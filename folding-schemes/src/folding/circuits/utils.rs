use ark_ff::PrimeField;
use ark_r1cs_std::fields::{fp::FpVar, FieldVar};
use ark_relations::r1cs::SynthesisError;
use std::marker::PhantomData;

/// EqEval is a gadget for computing $\tilde{eq}(a, b) = \prod_{i=1}^{l}(a_i \cdot b_i + (1 - a_i)(1 - b_i))$
/// :warning: This is not the ark_r1cs_std::eq::EqGadget
pub struct EqEvalGadget<F: PrimeField> {
    _f: PhantomData<F>,
}

impl<F: PrimeField> EqEvalGadget<F> {
    /// Gadget to evaluate the eq polynomial.
    /// Follows the implementation of `eq_eval` found in this crate.
    pub fn eq_eval(x: &[FpVar<F>], y: &[FpVar<F>]) -> Result<FpVar<F>, SynthesisError> {
        if x.len() != y.len() {
            return Err(SynthesisError::Unsatisfiable);
        }
        if x.is_empty() || y.is_empty() {
            return Err(SynthesisError::AssignmentMissing);
        }
        let mut e = FpVar::<F>::one();
        for (xi, yi) in x.iter().zip(y.iter()) {
            let xi_yi = xi * yi;
            e *= xi_yi.clone() + xi_yi - xi - yi + F::one();
        }
        Ok(e)
    }
}

#[cfg(test)]
mod tests {
    use ark_ff::Field;
    use ark_pallas::Fr;
    use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar, R1CSVar};
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::{test_rng, UniformRand};

    use super::EqEvalGadget;
    use crate::utils::virtual_polynomial::eq_eval;
    use crate::Error;

    #[test]
    pub fn test_eq_eval_gadget() -> Result<(), Error> {
        let mut rng = test_rng();
        let cs = ConstraintSystem::<Fr>::new_ref();

        for i in 1..20 {
            let x_vec: Vec<Fr> = (0..i).map(|_| Fr::rand(&mut rng)).collect();
            let y_vec: Vec<Fr> = (0..i).map(|_| Fr::rand(&mut rng)).collect();
            let x: Vec<FpVar<Fr>> = x_vec
                .iter()
                .map(|x| FpVar::<Fr>::new_witness(cs.clone(), || Ok(x)))
                .collect::<Result<Vec<_>, _>>()?;
            let y: Vec<FpVar<Fr>> = y_vec
                .iter()
                .map(|y| FpVar::<Fr>::new_witness(cs.clone(), || Ok(y)))
                .collect::<Result<Vec<_>, _>>()?;
            let expected_eq_eval = eq_eval::<Fr>(&x_vec, &y_vec)?;
            let gadget_eq_eval: FpVar<Fr> = EqEvalGadget::<Fr>::eq_eval(&x, &y)?;
            assert_eq!(expected_eq_eval, gadget_eq_eval.value()?);
        }

        let x: Vec<FpVar<Fr>> = vec![];
        let y: Vec<FpVar<Fr>> = vec![];
        let gadget_eq_eval = EqEvalGadget::<Fr>::eq_eval(&x, &y);
        assert!(gadget_eq_eval.is_err());

        let x: Vec<FpVar<Fr>> = vec![];
        let y: Vec<FpVar<Fr>> = vec![FpVar::<Fr>::new_witness(cs.clone(), || Ok(&Fr::ONE))?];
        let gadget_eq_eval = EqEvalGadget::<Fr>::eq_eval(&x, &y);
        assert!(gadget_eq_eval.is_err());
        Ok(())
    }
}
