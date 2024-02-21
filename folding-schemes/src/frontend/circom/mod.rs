use std::{error::Error, fs::File, io::BufReader, marker::PhantomData, path::PathBuf};

use color_eyre::Result;
use num_bigint::{BigInt, Sign};

use ark_circom::{circom::{r1cs_reader, R1CS}, WitnessCalculator};
use ark_ec::pairing::Pairing;
use ark_ff::{BigInteger, PrimeField};

// Define the sparse matrices on PrimeFiled.
pub type Constraints<F> = (ConstraintVec<F>, ConstraintVec<F>, ConstraintVec<F>);
pub type ConstraintVec<F> = Vec<(usize, F)>;
type ExtractedConstraints<F> = (Vec<Constraints<F>>, usize, usize);
pub type ExtractedConstraintsResult<F> = Result<ExtractedConstraints<F>, Box<dyn Error>>;
// pub type R1CSandZ<F> = (R1CS<F>, Vec<F>);

// A struct that wraps Circom functionalities, allowing for extraction of R1CS and witnesses
// based on file paths to Circom's .r1cs and .wasm.
#[derive(Clone, Debug)]
pub struct CircomWrapper<E: Pairing> {
    r1cs_filepath: PathBuf,
    wasm_filepath: PathBuf,
    _marker: PhantomData<E>,
}

impl<E: Pairing> CircomWrapper<E> {
    // Creates a new instance of the CircomWrapper with the file paths.
    pub fn new(r1cs_filepath: PathBuf, wasm_filepath: PathBuf) -> Self {
        CircomWrapper {
            r1cs_filepath,
            wasm_filepath,
            _marker: PhantomData,
        }
    }

    // Aggregated funtion to obtain R1CS and witness from Circom.
    pub fn extract_r1cs_and_witness(
        &self,
        inputs: &[(String, Vec<BigInt>)],
    ) -> Result<(R1CS<E>, Option<Vec<E::ScalarField>>), Box<dyn Error>> {
        // extracts the R1CS data from the file.
        let file = File::open(&self.r1cs_filepath)?;
        let reader = BufReader::new(file);
        let r1cs_file = r1cs_reader::R1CSFile::<E>::new(reader)?;
        let r1cs = r1cs_reader::R1CS::<E>::from(r1cs_file);
    
        // Calcultes the witness
        let witness = self.calculate_witness(inputs)?;
    
        let witness_vec: Result<Vec<E::ScalarField>, _> = witness.iter().map(|big_int| {
            let ark_big_int = self.num_bigint_to_ark_bigint::<E::ScalarField>(big_int)
                .map_err(|_| Box::new(std::fmt::Error) as Box<dyn Error>)?;
            E::ScalarField::from_bigint(ark_big_int).ok_or_else(|| {
                Box::new(std::fmt::Error) as Box<dyn Error> 
            })
        }).collect();
          
    
        Ok((r1cs, witness_vec.ok()))
    }

    // Calculates the witness given the Wasm filepath and inputs.
    pub fn calculate_witness(&self, inputs: &[(String, Vec<BigInt>)]) -> Result<Vec<BigInt>> {
        let mut calculator = WitnessCalculator::new(&self.wasm_filepath)?;
        calculator.calculate_witness(inputs.iter().cloned(), true)
    }

    // This function 
    // Converts a num_bigint::Bigint to PrimeField::BigInt.
    pub fn num_bigint_to_ark_bigint<F: PrimeField>(
        &self,
        value: &BigInt,
    ) -> Result<F::BigInt, Box<dyn Error>> {
        let big_uint = value
            .to_biguint()
            .ok_or_else(|| "BigInt is negative".to_string())?;
        F::BigInt::try_from(big_uint).map_err(|_| "BigInt conversion failed".to_string().into())
    }

    // Converts a PrimeField::BigInt to num_bigint::BigInt.
    pub fn ark_bigint_to_num_bigint<F: PrimeField>(&self, value: F) -> BigInt {
        let bigint_repr: F::BigInt = value.into_bigint();  
        let bytes = bigint_repr.to_bytes_be();
        BigInt::from_bytes_be(Sign::Plus, &bytes)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bn254::{Bn254, Fr};
    use std::path::PathBuf;
    use ark_relations::r1cs::{ConstraintSystem, ConstraintSynthesizer};
    use ark_circom::CircomCircuit;
    use std::fs;

    #[test]
    fn test_circom_circuit_satisfiability() {

        let cs = ConstraintSystem::<Fr>::new_ref();

        // bash folding-schemes/src/frontend/circom/test_folder/compile.sh

        let r1cs_filepath = PathBuf::from("./src/frontend/circom/test_folder/test_circuit.r1cs");
        let wasm_filepath = PathBuf::from("./src/frontend/circom/test_folder/test_circuit_js/test_circuit.wasm");

        assert!(fs::metadata(&r1cs_filepath).is_ok(), "R1CS file does not exist: {:?}", r1cs_filepath);
        assert!(fs::metadata(&wasm_filepath).is_ok(), "WASM file does not exist: {:?}", wasm_filepath);

        let circom_wrapper = CircomWrapper::<Bn254>::new(r1cs_filepath, wasm_filepath);

        let inputs = vec![("ivc_input".to_string(), vec![BigInt::from(3)])];

        let (r1cs, witness_option) = circom_wrapper.extract_r1cs_and_witness(&inputs)
            .expect("Error extracting R1CS and witness");

        let witness = witness_option.expect("Witness is missing");

        let circom_circuit = CircomCircuit::<Bn254> { r1cs, witness: Some(witness) };
        circom_circuit.generate_constraints(cs.clone())
            .expect("Error generating constraints");

        assert!(cs.is_satisfied().unwrap(), "Constraint system is not satisfied");
    }
}