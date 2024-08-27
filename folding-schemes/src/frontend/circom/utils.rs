use ark_circom::{
    circom::{r1cs_reader, R1CS},
    WitnessCalculator,
};
use ark_ff::{BigInteger, PrimeField};
use ark_serialize::Read;
use color_eyre::Result;
use num_bigint::{BigInt, Sign};
use std::{fs::File, io::Cursor, marker::PhantomData, path::PathBuf};

use crate::{utils::PathOrBin, Error};

// A struct that wraps Circom functionalities, allowing for extraction of R1CS and witnesses
// based on file paths to Circom's .r1cs and .wasm.
#[derive(Clone, Debug)]
pub struct CircomWrapper<F: PrimeField> {
    r1csfile_bytes: Vec<u8>,
    wasmfile_bytes: Vec<u8>,
    _marker: PhantomData<F>,
}

impl<F: PrimeField> CircomWrapper<F> {
    // Creates a new instance of the CircomWrapper with the file paths.
    pub fn new(r1cs: PathOrBin, wasm: PathOrBin) -> Result<Self, Error> {
        match (r1cs, wasm) {
            (PathOrBin::Path(r1cs_path), PathOrBin::Path(wasm_path)) => {
                Self::new_from_path(r1cs_path, wasm_path)
            }
            (PathOrBin::Bin(r1cs_bin), PathOrBin::Bin(wasm_bin)) => Ok(Self {
                r1csfile_bytes: r1cs_bin,
                wasmfile_bytes: wasm_bin,
                _marker: PhantomData,
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
            _marker: PhantomData,
        })
    }

    // Aggregated function to obtain R1CS and witness from Circom.
    pub fn extract_r1cs_and_witness(
        &self,
        inputs: &[(String, Vec<BigInt>)],
    ) -> Result<(R1CS<F>, Option<Vec<F>>), Error> {
        // Extracts the R1CS
        let r1cs_file = r1cs_reader::R1CSFile::<F>::new(Cursor::new(&self.r1csfile_bytes))?;
        let r1cs = r1cs_reader::R1CS::<F>::from(r1cs_file);

        // Extracts the witness vector
        let witness_vec = self.extract_witness(inputs)?;

        Ok((r1cs, Some(witness_vec)))
    }

    pub fn extract_r1cs(&self) -> Result<R1CS<F>, Error> {
        let r1cs_file = r1cs_reader::R1CSFile::<F>::new(Cursor::new(&self.r1csfile_bytes))?;
        let mut r1cs = r1cs_reader::R1CS::<F>::from(r1cs_file);
        r1cs.wire_mapping = None;
        Ok(r1cs)
    }

    // Extracts the witness vector as a vector of PrimeField elements.
    pub fn extract_witness(&self, inputs: &[(String, Vec<BigInt>)]) -> Result<Vec<F>, Error> {
        let witness_bigint = self.calculate_witness(inputs)?;

        witness_bigint
            .iter()
            .map(|big_int| {
                self.num_bigint_to_ark_bigint(big_int)
                    .and_then(|ark_big_int| {
                        F::from_bigint(ark_big_int)
                            .ok_or_else(|| Error::Other("could not get F from bigint".to_string()))
                    })
            })
            .collect()
    }

    // Calculates the witness given the Wasm filepath and inputs.
    pub fn calculate_witness(
        &self,
        inputs: &[(String, Vec<BigInt>)],
    ) -> Result<Vec<BigInt>, Error> {
        let mut calculator = WitnessCalculator::from_binary(&self.wasmfile_bytes).map_err(|e| {
            Error::WitnessCalculationError(format!("Failed to create WitnessCalculator: {}", e))
        })?;
        calculator
            .calculate_witness(inputs.iter().cloned(), true)
            .map_err(|e| {
                Error::WitnessCalculationError(format!("Failed to calculate witness: {}", e))
            })
    }

    // Converts a num_bigint::BigInt to a PrimeField::BigInt.
    pub fn num_bigint_to_ark_bigint(&self, value: &BigInt) -> Result<F::BigInt, Error> {
        let big_uint = value
            .to_biguint()
            .ok_or_else(|| Error::BigIntConversionError("BigInt is negative".to_string()))?;
        F::BigInt::try_from(big_uint).map_err(|_| {
            Error::BigIntConversionError("Failed to convert to PrimeField::BigInt".to_string())
        })
    }

    // Converts a PrimeField element to a num_bigint::BigInt representation.
    pub fn ark_primefield_to_num_bigint(&self, value: F) -> BigInt {
        let primefield_bigint: F::BigInt = value.into_bigint();
        let bytes = primefield_bigint.to_bytes_be();
        BigInt::from_bytes_be(Sign::Plus, &bytes)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bn254::Fr;
    use ark_circom::circom::{CircomBuilder, CircomConfig};
    use ark_circom::CircomCircuit;
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};

    //To generate .r1cs and .wasm files, run the below command in the terminal.
    //bash ./folding-schemes/src/frontend/circom/test_folder/compile.sh

    // Test the satisfication by using the CircomBuilder of circom-compat
    #[test]
    fn test_circombuilder_satisfied() {
        let cfg = CircomConfig::<Fr>::new(
            "./src/frontend/circom/test_folder/cubic_circuit_js/cubic_circuit.wasm",
            "./src/frontend/circom/test_folder/cubic_circuit.r1cs",
        )
        .unwrap();
        let mut builder = CircomBuilder::new(cfg);
        builder.push_input("ivc_input", 3);

        let circom = builder.build().unwrap();
        let cs = ConstraintSystem::<Fr>::new_ref();
        circom.generate_constraints(cs.clone()).unwrap();
        assert!(cs.is_satisfied().unwrap());
    }

    // Test the satisfication by using the CircomWrapper
    #[test]
    fn test_extract_r1cs_and_witness() {
        let r1cs_path = PathBuf::from("./src/frontend/circom/test_folder/cubic_circuit.r1cs");
        let wasm_path =
            PathBuf::from("./src/frontend/circom/test_folder/cubic_circuit_js/cubic_circuit.wasm");

        let inputs = vec![("ivc_input".to_string(), vec![BigInt::from(3)])];
        let wrapper = CircomWrapper::<Fr>::new(r1cs_path.into(), wasm_path.into()).unwrap();

        let (r1cs, witness) = wrapper.extract_r1cs_and_witness(&inputs).unwrap();

        let cs = ConstraintSystem::<Fr>::new_ref();

        let circom_circuit = CircomCircuit {
            r1cs,
            witness,
            public_inputs_indexes: vec![],
            allocate_inputs_as_witnesses: false,
        };

        circom_circuit.generate_constraints(cs.clone()).unwrap();
        assert!(cs.is_satisfied().unwrap());
    }
}
