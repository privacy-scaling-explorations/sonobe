use std::{fs::File, io::Cursor, path::PathBuf};

use ark_circom::{
    circom::{r1cs_reader, R1CS},
    WitnessCalculator,
};
use ark_ff::PrimeField;
use ark_serialize::Read;
use num_bigint::BigInt;
use wasmer::{Module, Store};

use folding_schemes::{utils::PathOrBin, Error};

// A struct that wraps Circom functionalities, allowing for extraction of R1CS and witnesses
// based on file paths to Circom's .r1cs and .wasm.
#[derive(Clone, Debug)]
pub struct CircomWrapper {
    r1csfile_bytes: Vec<u8>,
    wasmfile_bytes: Vec<u8>,
}

impl CircomWrapper {
    // Creates a new instance of the CircomWrapper with the file paths.
    pub fn new(r1cs: PathOrBin, wasm: PathOrBin) -> Result<Self, Error> {
        match (r1cs, wasm) {
            (PathOrBin::Path(r1cs_path), PathOrBin::Path(wasm_path)) => {
                Self::new_from_path(r1cs_path, wasm_path)
            }
            (PathOrBin::Bin(r1cs_bin), PathOrBin::Bin(wasm_bin)) => Ok(Self {
                r1csfile_bytes: r1cs_bin,
                wasmfile_bytes: wasm_bin,
            }),
            _ => unreachable!("You should pass the same enum branch for both inputs"),
        }
    }

    // Creates a new instance of the CircomWrapper with the file paths.
    fn new_from_path(r1cs_file_path: PathBuf, wasm_file_path: PathBuf) -> Result<Self, Error> {
        let mut file = File::open(r1cs_file_path)?;
        let metadata = File::metadata(&file)?;
        let mut r1csfile_bytes = vec![0; metadata.len() as usize];
        file.read_exact(&mut r1csfile_bytes)?;

        let mut file = File::open(wasm_file_path)?;
        let metadata = File::metadata(&file)?;
        let mut wasmfile_bytes = vec![0; metadata.len() as usize];
        file.read_exact(&mut wasmfile_bytes)?;

        Ok(CircomWrapper {
            r1csfile_bytes,
            wasmfile_bytes,
        })
    }

    // Aggregated function to obtain R1CS and witness from Circom.
    pub fn extract_r1cs_and_witness<F: PrimeField>(
        &self,
        inputs: Vec<(String, Vec<BigInt>)>,
    ) -> Result<(R1CS<F>, Option<Vec<F>>), Error> {
        // Extracts the R1CS
        let r1cs_file = r1cs_reader::R1CSFile::new(Cursor::new(&self.r1csfile_bytes))?;
        let r1cs = r1cs_reader::R1CS::from(r1cs_file);

        // Extracts the witness vector
        let witness_vec = self.extract_witness(inputs)?;

        Ok((r1cs, Some(witness_vec)))
    }

    pub fn extract_r1cs<F: PrimeField>(&self) -> Result<R1CS<F>, Error> {
        let r1cs_file = r1cs_reader::R1CSFile::new(Cursor::new(&self.r1csfile_bytes))?;
        let mut r1cs = r1cs_reader::R1CS::from(r1cs_file);
        r1cs.wire_mapping = None;
        Ok(r1cs)
    }

    // Extracts the witness vector as a vector of PrimeField elements.
    pub fn extract_witness<F: PrimeField>(
        &self,
        inputs: Vec<(String, Vec<BigInt>)>,
    ) -> Result<Vec<F>, Error> {
        let witness_bigint = self.calculate_witness(inputs)?;

        witness_bigint
            .into_iter()
            .map(|big_int| {
                big_int.to_biguint().map(F::from).ok_or_else(|| {
                    Error::ConversionError(
                        "BigInt".into(),
                        "BigUint".into(),
                        "BigInt is negative".into(),
                    )
                })
            })
            .collect()
    }

    // Calculates the witness given the Wasm filepath and inputs.
    pub fn calculate_witness(
        &self,
        inputs: Vec<(String, Vec<BigInt>)>,
    ) -> Result<Vec<BigInt>, Error> {
        let mut store = Store::default();
        let module = Module::new(&store, &self.wasmfile_bytes).map_err(|e| {
            Error::WitnessCalculationError(format!("Failed to create Wasm module: {e}"))
        })?;
            let mut calculator =
                WitnessCalculator::from_module(&mut store, module).map_err(|e| {
                    Error::WitnessCalculationError(format!(
                        "Failed to create WitnessCalculator: {e}"
                    ))
        })?;
        calculator
            .calculate_witness(&mut store, inputs, true)
            .map_err(|e| {
                Error::WitnessCalculationError(format!("Failed to calculate witness: {e}"))
            })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bn254::Fr;
    use ark_circom::circom::{CircomBuilder, CircomConfig};
    use ark_circom::CircomCircuit;
    use ark_relations::gr1cs::{ConstraintSynthesizer, ConstraintSystem};

    //To generate .r1cs and .wasm files, run the below command in the terminal.
    //bash ./frontends/src/circom/test_folder/compile.sh

    // Test the satisfication by using the CircomBuilder of circom-compat
    #[test]
    fn test_circombuilder_satisfied() -> Result<(), Error> {
        let cfg = CircomConfig::<Fr>::new(
            "./src/circom/test_folder/cubic_circuit_js/cubic_circuit.wasm",
            "./src/circom/test_folder/cubic_circuit.r1cs",
        )
        .unwrap();
        let mut builder = CircomBuilder::new(cfg);
        builder.push_input("ivc_input", 3);

        let circom = builder.build().unwrap();
        let cs = ConstraintSystem::<Fr>::new_ref();
        circom.generate_constraints(cs.clone())?;
        assert!(cs.is_satisfied()?);
        Ok(())
    }

    // Test the satisfication by using the CircomWrapper
    #[test]
    fn test_extract_r1cs_and_witness() -> Result<(), Error> {
        let r1cs_path = PathBuf::from("./src/circom/test_folder/cubic_circuit.r1cs");
        let wasm_path =
            PathBuf::from("./src/circom/test_folder/cubic_circuit_js/cubic_circuit.wasm");

        let inputs = vec![("ivc_input".to_string(), vec![BigInt::from(3)])];
        let wrapper = CircomWrapper::new(r1cs_path.into(), wasm_path.into())?;

        let (r1cs, witness) = wrapper.extract_r1cs_and_witness(inputs)?;

        let cs = ConstraintSystem::<Fr>::new_ref();

        let circom_circuit = CircomCircuit { r1cs, witness };

        circom_circuit.generate_constraints(cs.clone())?;
        assert!(cs.is_satisfied()?);
        Ok(())
    }
}
