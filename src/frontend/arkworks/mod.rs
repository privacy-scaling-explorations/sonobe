/// arkworks frontend
use ark_ff::PrimeField;
use ark_relations::r1cs::ConstraintSystem;

use crate::ccs::r1cs::R1CS;
use crate::utils::vec::SparseMatrix;

/// extracts arkworks ConstraintSystem matrices into crate::utils::vec::SparseMatrix format, and
/// extracts public inputs and witness into z vector. Returns a tuple containing (R1CS, z).
pub fn extract_r1cs_and_z<F: PrimeField>(cs: &ConstraintSystem<F>) -> (R1CS<F>, Vec<F>) {
    let m = cs.to_matrices().unwrap();

    let n_rows = cs.num_constraints;
    let n_cols = cs.num_instance_variables + cs.num_witness_variables; // cs.num_instance_variables already counts the 1

    let A = SparseMatrix::<F> {
        n_rows,
        n_cols,
        coeffs: m.a,
    };
    let B = SparseMatrix::<F> {
        n_rows,
        n_cols,
        coeffs: m.b,
    };
    let C = SparseMatrix::<F> {
        n_rows,
        n_cols,
        coeffs: m.c,
    };

    // z = (1, x, w)
    let z: Vec<F> = [
        // 1 is already included in cs.instance_assignment
        cs.instance_assignment.clone(),
        cs.witness_assignment.clone(),
    ]
    .concat();

    (
        R1CS::<F> {
            l: cs.num_instance_variables,
            A,
            B,
            C,
        },
        z,
    )
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use ark_ff::PrimeField;
    use ark_pallas::Fr;
    use ark_r1cs_std::{alloc::AllocVar, eq::EqGadget, fields::fp::FpVar};
    use ark_relations::r1cs::{
        ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, SynthesisError,
    };

    // TestCircuit implements the R1CS for: x^3 + x + 5 = y (example from article
    // https://www.vitalik.ca/general/2016/12/10/qap.html )
    #[derive(Clone, Copy, Debug)]
    pub struct TestCircuit<F: PrimeField> {
        pub x: F,
        pub y: F,
    }
    impl<F: PrimeField> ConstraintSynthesizer<F> for TestCircuit<F> {
        fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
            let x = FpVar::<F>::new_input(cs.clone(), || Ok(self.x))?;
            let y = FpVar::<F>::new_witness(cs.clone(), || Ok(self.y))?;
            let five = FpVar::<F>::new_constant(cs.clone(), F::from(5u32))?;

            let comp_y = (&x * &x * &x) + &x + &five;
            comp_y.enforce_equal(&y)?;
            Ok(())
        }
    }

    #[test]
    fn test_cs_to_matrices() {
        let cs = ConstraintSystem::<Fr>::new_ref();

        let x = Fr::from(5_u32);
        let y = x * x * x + x + Fr::from(5_u32);

        let test_circuit = TestCircuit::<Fr> { x, y };
        test_circuit.generate_constraints(cs.clone()).unwrap();
        cs.finalize();
        assert!(cs.is_satisfied().unwrap());

        let cs = cs.into_inner().unwrap();

        // ensure that num_instance_variables is 2: 1 + 1 public input
        assert_eq!(cs.num_instance_variables, 2);

        let (r1cs, z) = extract_r1cs_and_z::<Fr>(&cs);
        r1cs.check_relation(&z).unwrap();
    }
}
