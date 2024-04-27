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
    state_len: usize,
    external_inputs_len: usize,
}

impl<F: PrimeField> FCircuit<F> for CircomFCircuit<F> {
    /// (r1cs_path, wasm_path, state_len, external_inputs_len)
    type Params = (PathBuf, PathBuf, usize, usize);

    fn new(params: Self::Params) -> Self {
        let (r1cs_path, wasm_path, state_len, external_inputs_len) = params;
        let circom_wrapper = CircomWrapper::new(r1cs_path, wasm_path);
        Self {
            circom_wrapper,
            state_len,
            external_inputs_len,
        }
    }

    fn state_len(&self) -> usize {
        self.state_len
    }
    fn external_inputs_len(&self) -> usize {
        self.external_inputs_len
    }

    fn step_native(
        &self,
        _i: usize,
        z_i: Vec<F>,
        external_inputs: Vec<F>,
    ) -> Result<Vec<F>, Error> {
        #[cfg(test)]
        assert_eq!(z_i.len(), self.state_len());
        #[cfg(test)]
        assert_eq!(external_inputs.len(), self.external_inputs_len());

        let inputs_bi = z_i
            .iter()
            .map(|val| self.circom_wrapper.ark_primefield_to_num_bigint(*val))
            .collect::<Vec<BigInt>>();
        let mut inputs_map = vec![("ivc_input".to_string(), inputs_bi)];

        if !external_inputs.is_empty() {
            let external_inputs_bi = external_inputs
                .iter()
                .map(|val| self.circom_wrapper.ark_primefield_to_num_bigint(*val))
                .collect::<Vec<BigInt>>();
            inputs_map.push(("external_inputs".to_string(), external_inputs_bi));
        }

        // Computes witness
        let witness = self
            .circom_wrapper
            .extract_witness(&inputs_map)
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
        external_inputs: Vec<FpVar<F>>,
    ) -> Result<Vec<FpVar<F>>, SynthesisError> {
        #[cfg(test)]
        assert_eq!(z_i.len(), self.state_len());
        #[cfg(test)]
        assert_eq!(external_inputs.len(), self.external_inputs_len());

        let input_values = self.fpvars_to_bigints(z_i)?;
        let mut inputs_map = vec![("ivc_input".to_string(), input_values)];
        // if external_inputs.len() > 0 {
        if self.external_inputs_len() > 0 {
            let external_inputs_bi = self.fpvars_to_bigints(external_inputs)?;
            inputs_map.push(("external_inputs".to_string(), external_inputs_bi));
        }

        // Extracts R1CS and witness.
        let (r1cs, witness) = self
            .circom_wrapper
            .extract_r1cs_and_witness(&inputs_map)
            .map_err(|_| SynthesisError::AssignmentMissing)?;

        // Initializes the CircomCircuit.
        let circom_circuit = CircomCircuit {
            r1cs,
            witness: witness.clone(),
            inputs_already_allocated: true,
        };

        // Generates the constraints for the circom_circuit.
        circom_circuit.generate_constraints(cs.clone())?;

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

impl<F: PrimeField> CircomFCircuit<F> {
    fn fpvars_to_bigints(&self, fpVars: Vec<FpVar<F>>) -> Result<Vec<BigInt>, SynthesisError> {
        let mut input_values = Vec::new();
        // converts each FpVar to PrimeField value, then to num_bigint::BigInt.
        for fp_var in fpVars.iter() {
            // extracts the PrimeField value from FpVar.
            let primefield_value = fp_var.value()?;
            // converts the PrimeField value to num_bigint::BigInt.
            let num_bigint_value = self
                .circom_wrapper
                .ark_primefield_to_num_bigint(primefield_value);
            input_values.push(num_bigint_value);
        }
        Ok(input_values)
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

        let circom_fcircuit = CircomFCircuit::<Fr>::new((r1cs_path, wasm_path, 1, 0)); // state_len:1, external_inputs_len:0

        let z_i = vec![Fr::from(3u32)];
        let z_i1 = circom_fcircuit.step_native(1, z_i, vec![]).unwrap();
        assert_eq!(z_i1, vec![Fr::from(35u32)]);
    }

    // Tests the generate_step_constraints function of CircomFCircuit.
    #[test]
    fn test_circom_step_constraints() {
        let r1cs_path = PathBuf::from("./src/frontend/circom/test_folder/cubic_circuit.r1cs");
        let wasm_path =
            PathBuf::from("./src/frontend/circom/test_folder/cubic_circuit_js/cubic_circuit.wasm");

        let circom_fcircuit = CircomFCircuit::<Fr>::new((r1cs_path, wasm_path, 1, 0)); // state_len:1, external_inputs_len:0

        let cs = ConstraintSystem::<Fr>::new_ref();

        let z_i = vec![Fr::from(3u32)];

        let z_i_var = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(z_i)).unwrap();

        let cs = ConstraintSystem::<Fr>::new_ref();
        let z_i1_var = circom_fcircuit
            .generate_step_constraints(cs.clone(), 1, z_i_var, vec![])
            .unwrap();
        assert_eq!(z_i1_var.value().unwrap(), vec![Fr::from(35u32)]);
    }

    // Tests the WrapperCircuit with CircomFCircuit.
    #[test]
    fn test_wrapper_circomtofcircuit() {
        let r1cs_path = PathBuf::from("./src/frontend/circom/test_folder/cubic_circuit.r1cs");
        let wasm_path =
            PathBuf::from("./src/frontend/circom/test_folder/cubic_circuit_js/cubic_circuit.wasm");

        let circom_fcircuit = CircomFCircuit::<Fr>::new((r1cs_path, wasm_path, 1, 0)); // state_len:1, external_inputs_len:0

        // Allocates z_i1 by using step_native function.
        let z_i = vec![Fr::from(3_u32)];
        let wrapper_circuit = crate::frontend::tests::WrapperCircuit {
            FC: circom_fcircuit.clone(),
            z_i: Some(z_i.clone()),
            z_i1: Some(circom_fcircuit.step_native(0, z_i.clone(), vec![]).unwrap()),
        };

        let cs = ConstraintSystem::<Fr>::new_ref();

        wrapper_circuit.generate_constraints(cs.clone()).unwrap();
        assert!(
            cs.is_satisfied().unwrap(),
            "Constraint system is not satisfied"
        );
    }

    #[test]
    fn test_circom_external_inputs() {
        let r1cs_path = PathBuf::from("./src/frontend/circom/test_folder/external_inputs.r1cs");
        let wasm_path = PathBuf::from(
            "./src/frontend/circom/test_folder/external_inputs_js/external_inputs.wasm",
        );

        let circom_fcircuit = CircomFCircuit::<Fr>::new((r1cs_path, wasm_path, 1, 2)); // state_len:1, external_inputs_len:2

        let cs = ConstraintSystem::<Fr>::new_ref();

        let z_i = vec![Fr::from(3u32)];
        let external_inputs = vec![Fr::from(6u32), Fr::from(7u32)];

        // run native step
        let z_i1 = circom_fcircuit
            .step_native(1, z_i.clone(), external_inputs.clone())
            .unwrap();
        assert_eq!(z_i1, vec![Fr::from(52u32)]);

        // run gadget step
        let z_i_var = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(z_i)).unwrap();
        let external_inputs_var =
            Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(external_inputs)).unwrap();

        let cs = ConstraintSystem::<Fr>::new_ref();
        let z_i1_var = circom_fcircuit
            .generate_step_constraints(cs.clone(), 1, z_i_var, external_inputs_var)
            .unwrap();
        assert_eq!(z_i1_var.value().unwrap(), vec![Fr::from(52u32)]);
    }
}
