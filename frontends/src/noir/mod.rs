use std::collections::HashMap;

use acvm::{
    acir::{
        acir_field::GenericFieldElement,
        circuit::{Circuit, Program},
        native_types::{Witness as AcvmWitness, WitnessMap},
    },
    blackbox_solver::StubbedBlackBoxSolver,
    pwg::ACVM,
};
use ark_ff::PrimeField;
use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar, R1CSVar};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use folding_schemes::{frontend::FCircuit, utils::PathOrBin, Error};
use serde::{self, Deserialize, Serialize};

use self::bridge::AcirCircuitSonobe;

mod bridge;

#[derive(Clone, Debug)]
pub struct NoirFCircuit<F: PrimeField> {
    pub circuit: Circuit<GenericFieldElement<F>>,
    pub state_len: usize,
    pub external_inputs_len: usize,
}

#[derive(Clone, Serialize, Deserialize, Debug)]
pub struct ProgramArtifactGeneric<F: PrimeField> {
    #[serde(
        serialize_with = "Program::serialize_program_base64",
        deserialize_with = "Program::deserialize_program_base64"
    )]
    pub bytecode: Program<GenericFieldElement<F>>,
}

impl<F: PrimeField> FCircuit<F> for NoirFCircuit<F> {
    type Params = (PathOrBin, usize, usize);

    fn new(params: Self::Params) -> Result<Self, Error> {
        let (source, state_len, external_inputs_len) = params;
        let input_string = match source {
            PathOrBin::Path(path) => {
                let file_path = path.with_extension("json");
                std::fs::read(&file_path).map_err(|_| Error::Other(format!("{} is not a valid path\nRun either `nargo compile` to generate missing build artifacts or `nargo prove` to construct a proof", file_path.display())))?
            }
            PathOrBin::Bin(bin) => bin,
        };
        let program: ProgramArtifactGeneric<F> = serde_json::from_slice(&input_string)
            .map_err(|err| Error::JSONSerdeError(err.to_string()))?;
        let circuit: Circuit<GenericFieldElement<F>> = program.bytecode.functions[0].clone();
        let ivc_input_length = circuit.public_parameters.0.len();
        let ivc_return_length = circuit.return_values.0.len();

        if ivc_input_length != ivc_return_length {
            return Err(Error::NotSameLength(
                "IVC input: ".to_string(),
                ivc_input_length,
                "IVC output: ".to_string(),
                ivc_return_length,
            ));
        }

        Ok(NoirFCircuit {
            circuit,
            state_len,
            external_inputs_len,
        })
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
        external_inputs: Vec<F>, // inputs that are not part of the state
    ) -> Result<Vec<F>, Error> {
        let mut acvm = ACVM::new(
            &StubbedBlackBoxSolver,
            &self.circuit.opcodes,
            WitnessMap::new(),
            &[],
            &[],
        );

        self.circuit
            .public_parameters
            .0
            .iter()
            .map(|witness| {
                let idx: usize = witness.as_usize();
                let value = z_i[idx].to_string();
                let witness = AcvmWitness(witness.witness_index());
                let f = GenericFieldElement::<F>::try_from_str(&value)
                    .ok_or(SynthesisError::Unsatisfiable)?;
                acvm.overwrite_witness(witness, f);
                Ok(())
            })
            .collect::<Result<Vec<()>, SynthesisError>>()?;

        // write witness values for external_inputs
        self.circuit
            .private_parameters
            .iter()
            .map(|witness| {
                let idx = witness.as_usize() - z_i.len();
                let value = external_inputs[idx].to_string();
                let f = GenericFieldElement::<F>::try_from_str(&value)
                    .ok_or(SynthesisError::Unsatisfiable)?;
                acvm.overwrite_witness(AcvmWitness(witness.witness_index()), f);
                Ok(())
            })
            .collect::<Result<Vec<()>, SynthesisError>>()?;
        let _ = acvm.solve();

        let witness_map = acvm.finalize();

        // get the z_{i+1} output state
        let assigned_z_i1 = self
            .circuit
            .return_values
            .0
            .iter()
            .map(|witness| {
                let noir_field_element = witness_map
                    .get(witness)
                    .ok_or(SynthesisError::AssignmentMissing)?;
                Ok(noir_field_element.into_repr())
            })
            .collect::<Result<Vec<F>, SynthesisError>>()?;

        Ok(assigned_z_i1)
    }

    fn generate_step_constraints(
        &self,
        cs: ConstraintSystemRef<F>,
        _i: usize,
        z_i: Vec<FpVar<F>>,
        external_inputs: Vec<FpVar<F>>, // inputs that are not part of the state
    ) -> Result<Vec<FpVar<F>>, SynthesisError> {
        let mut acvm = ACVM::new(
            &StubbedBlackBoxSolver,
            &self.circuit.opcodes,
            WitnessMap::new(),
            &[],
            &[],
        );

        let mut already_assigned_witness_values = HashMap::new();

        self.circuit
            .public_parameters
            .0
            .iter()
            .map(|witness| {
                let idx: usize = witness.as_usize();
                let witness = AcvmWitness(witness.witness_index());
                already_assigned_witness_values.insert(witness, &z_i[idx]);
                let val = z_i[idx].value()?;
                let value = if val == F::zero() {
                    "0".to_string()
                } else {
                    val.to_string()
                };

                let f = GenericFieldElement::<F>::try_from_str(&value)
                    .ok_or(SynthesisError::Unsatisfiable)?;
                acvm.overwrite_witness(witness, f);
                Ok(())
            })
            .collect::<Result<Vec<()>, SynthesisError>>()?;

        // write witness values for external_inputs
        self.circuit
            .private_parameters
            .iter()
            .map(|witness| {
                let idx = witness.as_usize() - z_i.len();
                let witness = AcvmWitness(witness.witness_index());
                already_assigned_witness_values.insert(witness, &external_inputs[idx]);

                let val = external_inputs[idx].value()?;
                let value = if val == F::zero() {
                    "0".to_string()
                } else {
                    val.to_string()
                };

                let f = GenericFieldElement::<F>::try_from_str(&value)
                    .ok_or(SynthesisError::Unsatisfiable)?;
                acvm.overwrite_witness(witness, f);
                Ok(())
            })
            .collect::<Result<Vec<()>, SynthesisError>>()?;

        // computes the witness
        let _ = acvm.solve();
        let witness_map = acvm.finalize();

        // get the z_{i+1} output state
        let assigned_z_i1 = self
            .circuit
            .return_values
            .0
            .iter()
            .map(|witness| {
                let noir_field_element = witness_map
                    .get(witness)
                    .ok_or(SynthesisError::AssignmentMissing)?;
                FpVar::<F>::new_witness(cs.clone(), || Ok(noir_field_element.into_repr()))
            })
            .collect::<Result<Vec<FpVar<F>>, SynthesisError>>()?;

        // initialize circuit and set already assigned values
        let mut acir_circuit = AcirCircuitSonobe::from((&self.circuit, witness_map));
        acir_circuit.already_assigned_witnesses = already_assigned_witness_values;

        acir_circuit.generate_constraints(cs.clone())?;

        Ok(assigned_z_i1)
    }
}

#[cfg(test)]
mod tests {
    use ark_bn254::Fr;
    use ark_r1cs_std::R1CSVar;
    use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar};
    use ark_relations::r1cs::ConstraintSystem;
    use folding_schemes::frontend::FCircuit;
    use std::env;

    use crate::noir::NoirFCircuit;

    #[test]
    fn test_step_native() {
        let cur_path = env::current_dir().unwrap();
        let noirfcircuit = NoirFCircuit::new((
            cur_path
                .join("src/noir/test_folder/test_circuit/target/test_circuit.json")
                .into(),
            2,
            2,
        ))
        .unwrap();
        let inputs = vec![Fr::from(2), Fr::from(5)];
        let res = noirfcircuit.step_native(0, inputs.clone(), inputs);
        assert!(res.is_ok());
        assert_eq!(res.unwrap(), vec![Fr::from(4), Fr::from(25)]);
    }

    #[test]
    fn test_step_constraints() {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let cur_path = env::current_dir().unwrap();
        let noirfcircuit = NoirFCircuit::new((
            cur_path
                .join("src/noir/test_folder/test_circuit/target/test_circuit.json")
                .into(),
            2,
            2,
        ))
        .unwrap();
        let inputs = vec![Fr::from(2), Fr::from(5)];
        let z_i = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(inputs.clone())).unwrap();
        let external_inputs = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(inputs)).unwrap();
        let output = noirfcircuit
            .generate_step_constraints(cs.clone(), 0, z_i, external_inputs)
            .unwrap();
        assert_eq!(output[0].value().unwrap(), Fr::from(4));
        assert_eq!(output[1].value().unwrap(), Fr::from(25));
    }

    #[test]
    fn test_step_constraints_no_external_inputs() {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let cur_path = env::current_dir().unwrap();
        let noirfcircuit = NoirFCircuit::new((
            cur_path
                .join("src/noir/test_folder/test_no_external_inputs/target/test_no_external_inputs.json")
                .into(),
            2,
            0,
        ))
        .unwrap();
        let inputs = vec![Fr::from(2), Fr::from(5)];
        let z_i = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(inputs.clone())).unwrap();
        let external_inputs = vec![];
        let output = noirfcircuit
            .generate_step_constraints(cs.clone(), 0, z_i, external_inputs)
            .unwrap();
        assert_eq!(output[0].value().unwrap(), Fr::from(4));
        assert_eq!(output[1].value().unwrap(), Fr::from(25));
    }
}
