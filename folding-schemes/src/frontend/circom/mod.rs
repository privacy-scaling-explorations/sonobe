use ark_circom::circom::CircomCircuit;
use ark_ff::PrimeField;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::R1CSVar;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_std::fmt::Debug;
use num_bigint::BigInt;
use std::path::PathBuf;

use crate::frontend::FCircuit;
use crate::Error;

pub mod utils;
use utils::CircomWrapper;

/// Define CircomFCircuit
#[derive(Clone, Debug)]
pub struct CircomFCircuit<F: PrimeField> {
    circom_wrapper: CircomWrapper<F>,
}

impl<F: PrimeField> FCircuit<F> for CircomFCircuit<F> {
    type Params = (PathBuf, PathBuf);

    fn new(params: Self::Params) -> Self {
        let (r1cs_path, wasm_path) = params;
        let circom_wrapper = CircomWrapper::new(r1cs_path, wasm_path);
        Self { circom_wrapper }
    }

    fn state_len(&self) -> usize {
        1
    }

    fn step_native(&self, _i: usize, z_i: Vec<F>) -> Result<Vec<F>, Error> {
        // Converts PrimeField values to BigInt for computing witness.
        let input_num_bigint = z_i
            .iter()
            .map(|val| self.circom_wrapper.ark_primefield_to_num_bigint(*val))
            .collect::<Vec<BigInt>>();

        // Computes witness
        let witness = self
            .circom_wrapper
            .extract_witness(&[("ivc_input".to_string(), input_num_bigint)])
            .map_err(|e| {
                Error::WitnessCalculationError(format!("Failed to calculate witness: {}", e))
            })?;

        // Extracts the z_i1(next state) from the witness vector.
        let z_i1 = witness[1..1 + self.state_len()].to_vec();
        Ok(z_i1)
    }

    fn generate_step_constraints(
        &self,
        cs: ConstraintSystemRef<F>,
        _i: usize,
        z_i: Vec<FpVar<F>>,
    ) -> Result<Vec<FpVar<F>>, SynthesisError> {
        let mut input_values = Vec::new();
        // Converts each FpVar to PrimeField value, then to num_bigint::BigInt.
        for fp_var in z_i.iter() {
            // Extracts the PrimeField value from FpVar.
            let primefield_value = fp_var.value()?;
            // Converts the PrimeField value to num_bigint::BigInt.
            let num_bigint_value = self
                .circom_wrapper
                .ark_primefield_to_num_bigint(primefield_value);
            input_values.push(num_bigint_value);
        }

        let num_bigint_inputs = vec![("ivc_input".to_string(), input_values)];

        // Extracts R1CS and witness.
        let (r1cs, witness) = self
            .circom_wrapper
            .extract_r1cs_and_witness(&num_bigint_inputs)
            .map_err(|_| SynthesisError::AssignmentMissing)?;

        // Initializes the CircomCircuit.
        let circom_circuit = CircomCircuit {
            r1cs,
            witness: witness.clone(),
            inputs_already_computed: true,
        };

        // Generates the constraints for the circom_circuit.
        circom_circuit
            .generate_constraints(cs.clone())
            .map_err(|_| SynthesisError::AssignmentMissing)?;

        // Checks for constraint satisfaction.
        if !cs.is_satisfied().unwrap() {
            return Err(SynthesisError::Unsatisfiable);
        }

        let w = witness.ok_or(SynthesisError::Unsatisfiable)?;

        // Extracts the z_i1(next state) from the witness vector.
        let z_i1: Vec<FpVar<F>> =
            Vec::<FpVar<F>>::new_witness(cs.clone(), || Ok(w[1..1 + self.state_len()].to_vec()))?;

        Ok(z_i1)
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use ark_pallas::Fr;
    use ark_r1cs_std::alloc::AllocVar;
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};

    // Tests the step_native function of CircomFCircuit.
    #[test]
    fn test_circom_step_native() {
        let r1cs_path = PathBuf::from("./src/frontend/circom/test_folder/cubic_circuit.r1cs");
        let wasm_path =
            PathBuf::from("./src/frontend/circom/test_folder/cubic_circuit_js/cubic_circuit.wasm");

        let circom_fcircuit = CircomFCircuit::<Fr>::new((r1cs_path, wasm_path));

        let z_i = vec![Fr::from(3u32)];
        let z_i1 = circom_fcircuit.step_native(1, z_i).unwrap();
        assert_eq!(z_i1, vec![Fr::from(35u32)]);
    }

    // Tests the generate_step_constraints function of CircomFCircuit.
    #[test]
    fn test_circom_step_constraints() {
        let r1cs_path = PathBuf::from("./src/frontend/circom/test_folder/cubic_circuit.r1cs");
        let wasm_path =
            PathBuf::from("./src/frontend/circom/test_folder/cubic_circuit_js/cubic_circuit.wasm");

        let circom_fcircuit = CircomFCircuit::<Fr>::new((r1cs_path, wasm_path));

        let cs = ConstraintSystem::<Fr>::new_ref();

        let z_i = vec![Fr::from(3u32)];

        let z_i_var = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(z_i)).unwrap();

        let cs = ConstraintSystem::<Fr>::new_ref();
        let z_i1_var = circom_fcircuit
            .generate_step_constraints(cs.clone(), 1, z_i_var)
            .unwrap();
        assert_eq!(z_i1_var.value().unwrap(), vec![Fr::from(35u32)]);
    }

    // Tests the WrapperCircuit with CircomFCircuit.
    #[test]
    fn test_wrapper_circomtofcircuit() {
        let r1cs_path = PathBuf::from("./src/frontend/circom/test_folder/cubic_circuit.r1cs");
        let wasm_path =
            PathBuf::from("./src/frontend/circom/test_folder/cubic_circuit_js/cubic_circuit.wasm");

        let circom_fcircuit = CircomFCircuit::<Fr>::new((r1cs_path, wasm_path));

        // Allocates z_i1 by using step_native function.
        let z_i = vec![Fr::from(3_u32)];
        let wrapper_circuit = crate::frontend::tests::WrapperCircuit {
            FC: circom_fcircuit.clone(),
            z_i: Some(z_i.clone()),
            z_i1: Some(circom_fcircuit.step_native(0, z_i.clone()).unwrap()),
        };

        let cs = ConstraintSystem::<Fr>::new_ref();

        wrapper_circuit.generate_constraints(cs.clone()).unwrap();
        assert!(
            cs.is_satisfied().unwrap(),
            "Constraint system is not satisfied"
        );
    }
}
