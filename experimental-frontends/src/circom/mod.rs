use ark_circom::circom::{CircomCircuit, R1CS as CircomR1CS};
use ark_ff::PrimeField;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::fields::fp::FpVar::Var;
use ark_r1cs_std::R1CSVar;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_std::fmt::Debug;
use folding_schemes::{frontend::FCircuit, utils::PathOrBin, Error};
use num_bigint::BigInt;

pub mod utils;
use crate::utils::{VecF, VecFpVar};
use utils::CircomWrapper;

/// Define CircomFCircuit. The parameter `SL` indicates the length of the state vector.
/// The parameter `EIL` indicates the length of the ExternalInputs vector of field elements.
#[derive(Clone, Debug)]
pub struct CircomFCircuit<F: PrimeField, const SL: usize, const EIL: usize> {
    circom_wrapper: CircomWrapper<F>,
    r1cs: CircomR1CS<F>,
}

impl<F: PrimeField, const SL: usize, const EIL: usize> FCircuit<F> for CircomFCircuit<F, SL, EIL> {
    /// (r1cs_path, wasm_path)
    type Params = (PathOrBin, PathOrBin);
    type ExternalInputs = VecF<F, EIL>;
    type ExternalInputsVar = VecFpVar<F, EIL>;

    fn new(params: Self::Params) -> Result<Self, Error> {
        let (r1cs_path, wasm_path) = params;
        let circom_wrapper = CircomWrapper::new(r1cs_path, wasm_path)?;

        let r1cs = circom_wrapper.extract_r1cs()?;
        Ok(Self {
            circom_wrapper,
            r1cs,
        })
    }

    fn state_len(&self) -> usize {
        SL
    }

    fn generate_step_constraints(
        &self,
        cs: ConstraintSystemRef<F>,
        _i: usize,
        z_i: Vec<FpVar<F>>,
        external_inputs: Self::ExternalInputsVar,
    ) -> Result<Vec<FpVar<F>>, SynthesisError> {
        #[cfg(test)]
        assert_eq!(z_i.len(), SL);
        #[cfg(test)]
        assert_eq!(external_inputs.0.len(), EIL);

        let input_values = self.fpvars_to_bigints(&z_i)?;
        let mut inputs_map = vec![("ivc_input".to_string(), input_values)];

        if EIL > 0 {
            let external_inputs_bi = self.fpvars_to_bigints(&external_inputs.0)?;
            inputs_map.push(("external_inputs".to_string(), external_inputs_bi));
        }

        let witness = self
            .circom_wrapper
            .extract_witness(&inputs_map)
            .map_err(|_| SynthesisError::AssignmentMissing)?;

        // Since public inputs are already allocated variables, we will tell `circom-compat` to not re-allocate those
        let mut already_allocated_public_inputs = vec![];
        for var in z_i.iter() {
            match var {
                Var(var) => already_allocated_public_inputs.push(var.variable),
                _ => return Err(SynthesisError::Unsatisfiable), // allocated z_i should be Var
            }
        }

        // Initializes the CircomCircuit.
        let circom_circuit = CircomCircuit {
            r1cs: self.r1cs.clone(),
            witness: Some(witness.clone()),
            public_inputs_indexes: already_allocated_public_inputs,
            allocate_inputs_as_witnesses: true,
        };

        // Generates the constraints for the circom_circuit.
        circom_circuit.generate_constraints(cs.clone())?;

        // TODO: https://github.com/privacy-scaling-explorations/sonobe/issues/104
        // We disable checking constraints for now
        // Checks for constraint satisfaction.
        // if !cs.is_satisfied().unwrap() {
        //     return Err(SynthesisError::Unsatisfiable);
        // }

        // Extracts the z_i1(next state) from the witness vector.
        let z_i1: Vec<FpVar<F>> =
            Vec::<FpVar<F>>::new_witness(cs.clone(), || Ok(witness[1..1 + SL].to_vec()))?;

        Ok(z_i1)
    }
}

impl<F: PrimeField, const SL: usize, const EIL: usize> CircomFCircuit<F, SL, EIL> {
    fn fpvars_to_bigints(&self, fpvars: &[FpVar<F>]) -> Result<Vec<BigInt>, SynthesisError> {
        let mut input_values = Vec::new();
        // converts each FpVar to PrimeField value, then to num_bigint::BigInt.
        for fp_var in fpvars.iter() {
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
    use ark_bn254::Fr;
    use ark_relations::r1cs::ConstraintSystem;
    use std::path::PathBuf;

    /// Native implementation of `src/circom/test_folder/cubic_circuit.r1cs`
    fn cubic_step_native<F: PrimeField>(z_i: Vec<F>) -> Vec<F> {
        let z = z_i[0];
        vec![z * z * z + z + F::from(5)]
    }

    /// Native implementation of `src/circom/test_folder/with_external_inputs.r1cs`
    fn external_inputs_step_native<F: PrimeField>(z_i: Vec<F>, external_inputs: Vec<F>) -> Vec<F> {
        let temp1 = z_i[0] * z_i[0];
        let temp2 = z_i[0] * external_inputs[0];
        vec![temp1 * z_i[0] + temp2 + external_inputs[1]]
    }

    /// Native implementation of `src/circom/test_folder/no_external_inputs.r1cs`
    fn no_external_inputs_step_native<F: PrimeField>(z_i: Vec<F>) -> Vec<F> {
        let temp1 = z_i[0] * z_i[1];
        let temp2 = temp1 * z_i[2];
        vec![
            temp1 * z_i[0],
            temp1 * z_i[1] + temp1,
            temp1 * z_i[2] + temp2,
        ]
    }

    // Tests the step_native function of CircomFCircuit.
    #[test]
    fn test_circom_step_native() -> Result<(), Error> {
        let z_i = vec![Fr::from(3u32)];
        let z_i1 = cubic_step_native(z_i);
        assert_eq!(z_i1, vec![Fr::from(35u32)]);
        Ok(())
    }

    // Tests the generate_step_constraints function of CircomFCircuit.
    #[test]
    fn test_circom_step_constraints() -> Result<(), Error> {
        let r1cs_path = PathBuf::from("./src/circom/test_folder/cubic_circuit.r1cs");
        let wasm_path =
            PathBuf::from("./src/circom/test_folder/cubic_circuit_js/cubic_circuit.wasm");

        let circom_fcircuit =
            CircomFCircuit::<Fr, 1, 0>::new((r1cs_path.into(), wasm_path.into()))?; // state_len:1, external_inputs_len:0

        let cs = ConstraintSystem::<Fr>::new_ref();

        let z_i = vec![Fr::from(3u32)];

        let z_i_var = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(z_i))?;
        let z_i1_var =
            circom_fcircuit.generate_step_constraints(cs.clone(), 1, z_i_var, VecFpVar(vec![]))?;
        assert_eq!(z_i1_var.value()?, vec![Fr::from(35u32)]);
        Ok(())
    }

    // Tests the WrapperCircuit with CircomFCircuit.
    #[test]
    fn test_wrapper_circomtofcircuit() -> Result<(), Error> {
        let r1cs_path = PathBuf::from("./src/circom/test_folder/cubic_circuit.r1cs");
        let wasm_path =
            PathBuf::from("./src/circom/test_folder/cubic_circuit_js/cubic_circuit.wasm");

        let circom_fcircuit =
            CircomFCircuit::<Fr, 1, 0>::new((r1cs_path.into(), wasm_path.into()))?; // state_len:1, external_inputs_len:0

        // Allocates z_i1 by using step_native function.
        let z_i = vec![Fr::from(3_u32)];
        let wrapper_circuit = folding_schemes::frontend::utils::WrapperCircuit {
            FC: circom_fcircuit.clone(),
            z_i: Some(z_i.clone()),
            z_i1: Some(cubic_step_native(z_i)),
        };

        let cs = ConstraintSystem::<Fr>::new_ref();

        wrapper_circuit.generate_constraints(cs.clone())?;
        assert!(cs.is_satisfied()?, "Constraint system is not satisfied");
        Ok(())
    }

    #[test]
    fn test_circom_external_inputs() -> Result<(), Error> {
        let r1cs_path = PathBuf::from("./src/circom/test_folder/with_external_inputs.r1cs");
        let wasm_path = PathBuf::from(
            "./src/circom/test_folder/with_external_inputs_js/with_external_inputs.wasm",
        );
        let circom_fcircuit =
            CircomFCircuit::<Fr, 1, 2>::new((r1cs_path.into(), wasm_path.into()))?; // state_len:1, external_inputs_len:2
        let cs = ConstraintSystem::<Fr>::new_ref();
        let z_i = vec![Fr::from(3u32)];
        let external_inputs = vec![Fr::from(6u32), Fr::from(7u32)];

        // run native step
        let z_i1_native = external_inputs_step_native(z_i.clone(), external_inputs.clone());

        // run gadget step
        let z_i_var = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(z_i))?;
        let external_inputs_var =
            Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(external_inputs.clone()))?;
        let z_i1_var = circom_fcircuit.generate_step_constraints(
            cs.clone(),
            1,
            z_i_var,
            VecFpVar(external_inputs_var),
        )?;

        assert_eq!(z_i1_var.value()?, z_i1_native);

        // re-init cs and run gadget step with wrong ivc inputs (first ivc should not be zero)
        let cs = ConstraintSystem::<Fr>::new_ref();
        let wrong_z_i = vec![Fr::from(0)];
        let wrong_z_i_var = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(wrong_z_i))?;
        let external_inputs_var =
            Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(external_inputs))?;
        let _z_i1_var = circom_fcircuit.generate_step_constraints(
            cs.clone(),
            1,
            wrong_z_i_var,
            VecFpVar(external_inputs_var),
        );
        // TODO:: https://github.com/privacy-scaling-explorations/sonobe/issues/104
        // Disable check for now
        // assert!(z_i1_var.is_err());
        Ok(())
    }

    #[test]
    fn test_circom_no_external_inputs() -> Result<(), Error> {
        let r1cs_path = PathBuf::from("./src/circom/test_folder/no_external_inputs.r1cs");
        let wasm_path =
            PathBuf::from("./src/circom/test_folder/no_external_inputs_js/no_external_inputs.wasm");
        let circom_fcircuit =
            CircomFCircuit::<Fr, 3, 0>::new((r1cs_path.into(), wasm_path.into()))?;
        let cs = ConstraintSystem::<Fr>::new_ref();
        let z_i = vec![Fr::from(3u32), Fr::from(4u32), Fr::from(5u32)];
        let z_i_var = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(z_i.clone()))?;

        // run native step
        let z_i1_native = no_external_inputs_step_native(z_i.clone());

        // run gadget step
        let z_i1_var =
            circom_fcircuit.generate_step_constraints(cs.clone(), 1, z_i_var, VecFpVar(vec![]))?;

        assert_eq!(z_i1_var.value()?, z_i1_native);

        // re-init cs and run gadget step with wrong ivc inputs (first ivc input should not be zero)
        let cs = ConstraintSystem::<Fr>::new_ref();
        let wrong_z_i = vec![Fr::from(0u32), Fr::from(4u32), Fr::from(5u32)];
        let wrong_z_i_var = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(wrong_z_i))?;
        let _z_i1_var = circom_fcircuit.generate_step_constraints(
            cs.clone(),
            1,
            wrong_z_i_var,
            VecFpVar(vec![]),
        );
        // TODO:: https://github.com/privacy-scaling-explorations/sonobe/issues/104
        // Disable check for now
        // assert!(z_i1_var.is_err())
        Ok(())
    }

    #[test]
    fn test_custom_code() -> Result<(), Error> {
        let r1cs_path = PathBuf::from("./src/circom/test_folder/cubic_circuit.r1cs");
        let wasm_path =
            PathBuf::from("./src/circom/test_folder/cubic_circuit_js/cubic_circuit.wasm");

        let circom_fcircuit =
            CircomFCircuit::<Fr, 1, 0>::new((r1cs_path.into(), wasm_path.into()))?; // state_len:1, external_inputs_len:0

        // Allocates z_i1 by using step_native function.
        let z_i = vec![Fr::from(3_u32)];
        let wrapper_circuit = folding_schemes::frontend::utils::WrapperCircuit {
            FC: circom_fcircuit.clone(),
            z_i: Some(z_i.clone()),
            z_i1: Some(cubic_step_native(z_i)),
        };

        let cs = ConstraintSystem::<Fr>::new_ref();

        wrapper_circuit.generate_constraints(cs.clone())?;
        assert!(cs.is_satisfied()?, "Constraint system is not satisfied");
        Ok(())
    }
}
