use std::{error::Error, fs::File, io::BufReader, marker::PhantomData, path::PathBuf};

use color_eyre::Result;
use num_bigint::BigInt;

use ark_circom::{circom::r1cs_reader, WitnessCalculator};
use ark_ec::pairing::Pairing;
use ark_ff::PrimeField;

use crate::ccs::r1cs::R1CS;
use crate::utils::vec::SparseMatrix;

// Define the sparse matrices on PrimeFiled.
pub type Constraints<F> = (ConstraintVec<F>, ConstraintVec<F>, ConstraintVec<F>);
pub type ConstraintVec<F> = Vec<(usize, F)>;
pub type ExtractedConstraintsResult<F> =
    Result<(Vec<Constraints<F>>, usize, usize), Box<dyn Error>>;

// Trait that provides an interface for extracting R1CS and Z vector from Circom.
pub trait CircomFrontend<F: PrimeField> {
    fn get(&self, inputs: &[(String, Vec<BigInt>)]) -> Result<(R1CS<F>, Vec<F>), Box<dyn Error>>;
}

impl<E: Pairing> CircomFrontend<E::ScalarField> for CircomWrapper<E> {
    fn get(
        &self,
        inputs: &[(String, Vec<BigInt>)],
    ) -> Result<(R1CS<E::ScalarField>, Vec<E::ScalarField>), Box<dyn Error>> {
        self.extract_and_convert(inputs)
    }
}

// A struct that wraps Circom functionalities, allowing for extraction of R1CS and witnesses 
// based on file paths to Circom's .r1cs and .wasm.
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

    // Aggregates multiple functions to obtain R1CS and Z as defined in folding-schemes from Circom.
    pub fn extract_and_convert(
        &self,
        inputs: &[(String, Vec<BigInt>)],
    ) -> Result<(R1CS<E::ScalarField>, Vec<E::ScalarField>), Box<dyn Error>> {
        let (constraints, pub_io_len, num_variables) = self.extract_constraints_from_r1cs()?;
        let witness = self.calculate_witness(inputs)?;
        self.circom_to_folding_schemes_r1cs_and_z(constraints, &witness, pub_io_len, num_variables)
    }

    // Extracts constraints from the r1cs file.
    pub fn extract_constraints_from_r1cs(&self) -> ExtractedConstraintsResult<E::ScalarField>
    where
        E: Pairing,
    {
        // Opens the .r1cs file and create a reader.
        let file = File::open(&self.r1cs_filepath)?;
        let reader = BufReader::new(file);

        // Reads the R1CS file and extract the constraints directly.
        let r1cs_file = r1cs_reader::R1CSFile::<E>::new(reader)?;
        let pub_io_len = (r1cs_file.header.n_pub_in + r1cs_file.header.n_pub_out) as usize;
        let r1cs = r1cs_reader::R1CS::<E>::from(r1cs_file);
        let num_variables = r1cs.num_variables;
        let constraints: Vec<Constraints<E::ScalarField>> = r1cs.constraints;

        Ok((constraints, pub_io_len, num_variables))
    }

    // Converts a set of constraints from ark-circom into R1CS format of folding-schemes.
    pub fn convert_to_folding_schemes_r1cs<F>(
        &self,
        constraints: Vec<Constraints<F>>,
        pub_io_len: usize,
        num_variables: usize,
    ) -> R1CS<F>
    where
        F: PrimeField,
    {
        let mut a_matrix: Vec<Vec<(F, usize)>> = Vec::new();
        let mut b_matrix: Vec<Vec<(F, usize)>> = Vec::new();
        let mut c_matrix: Vec<Vec<(F, usize)>> = Vec::new();

        let n_rows = constraints.len();

        for (ai, bi, ci) in constraints {
            a_matrix.push(
                ai.into_iter()
                    .map(|(index, scalar)| (scalar, index))
                    .collect(),
            );
            b_matrix.push(
                bi.into_iter()
                    .map(|(index, scalar)| (scalar, index))
                    .collect(),
            );
            c_matrix.push(
                ci.into_iter()
                    .map(|(index, scalar)| (scalar, index))
                    .collect(),
            );
        }

        let l = pub_io_len;
        let n_cols = num_variables;

        let A = SparseMatrix {
            n_rows,
            n_cols,
            coeffs: a_matrix,
        };
        let B = SparseMatrix {
            n_rows,
            n_cols,
            coeffs: b_matrix,
        };
        let C = SparseMatrix {
            n_rows,
            n_cols,
            coeffs: c_matrix,
        };

        R1CS::<F> { l, A, B, C }
    }

    // Calculates the witness given the Wasm filepath and inputs.
    pub fn calculate_witness(&self, inputs: &[(String, Vec<BigInt>)]) -> Result<Vec<BigInt>> {
        let mut calculator = WitnessCalculator::new(&self.wasm_filepath)?;
        calculator.calculate_witness(inputs.to_vec().into_iter(), true)
    }

    // Converts a num_bigint input to `PrimeField`'s BigInt.
    pub fn num_bigint_to_ark_bigint<F: PrimeField>(
        &self,
        value: &BigInt,
    ) -> Result<F::BigInt, Box<dyn Error>> {
        let big_uint = value
            .to_biguint()
            .ok_or_else(|| "BigInt is negative".to_string())?;
        F::BigInt::try_from(big_uint).map_err(|_| "BigInt conversion failed".to_string().into())
    }

    // Converts R1CS constraints and witness from ark-circom format
    // into folding-schemes R1CS and z format.
    pub fn circom_to_folding_schemes_r1cs_and_z<F>(
        &self,
        constraints: Vec<Constraints<F>>,
        witness: &[BigInt],
        pub_io_len: usize,
        num_variables: usize,
    ) -> Result<(R1CS<F>, Vec<F>), Box<dyn Error>>
    where
        F: PrimeField,
    {
        let folding_schemes_r1cs =
            self.convert_to_folding_schemes_r1cs(constraints, pub_io_len, num_variables);

        let z: Result<Vec<F>, _> = witness
            .iter()
            .map(|big_int| {
                let ark_big_int = self.num_bigint_to_ark_bigint::<F>(big_int)?;
                F::from_bigint(ark_big_int).ok_or_else(|| {
                    "Failed to convert bigint to field element"
                        .to_string()
                        .into()
                })
            })
            .collect();

        z.map(|z| (folding_schemes_r1cs, z))
    }
}

#[cfg(test)]
mod tests {
    use crate::frontend::circom::{CircomFrontend, CircomWrapper};
    use ark_bn254::Bn254;
    use num_bigint::BigInt;
    use std::{env, process::Command};

    // Compiles the .circom file to generate the .r1cs and .wasm files.
    fn compile_circom_to_r1cs_and_wasm(base_path: &std::path::Path) {
        let script_path = base_path.join("compile.sh");

        let status = Command::new("bash")
            .arg(script_path)
            .status()
            .expect("Failed to execute circom compilation script.");

        assert!(status.success(), "Circom compilation script failed.");
    }

    /*
    test_circuit represents 35 = x^3 + x + 5 in test_folder/test_circuit.circom.
    In the test_circom_conversion_success function, x is assigned the value 3, which satisfies the R1CS correctly.
    In the test_circom_conversion_failure function, x is assigned the value 6, which doesn't satisfy the R1CS.
    */

    fn test_circom_conversion_logic(expect_success: bool, inputs: Vec<(String, Vec<BigInt>)>) {
        let current_dir = env::current_dir().unwrap();
        let base_path = current_dir.join("src/frontend/circom/test_folder");

        compile_circom_to_r1cs_and_wasm(&base_path);

        let r1cs_filepath = base_path.join("test_circuit.r1cs");
        let wasm_filepath = base_path.join("test_circuit_js/test_circuit.wasm");

        assert!(r1cs_filepath.exists());
        assert!(wasm_filepath.exists());

        let circom_frontend =
            CircomWrapper::<Bn254>::new(r1cs_filepath.clone(), wasm_filepath.clone());

        let (r1cs, z) = circom_frontend
            .get(&inputs)
            .expect("Error processing input");

        // Checks the relationship of R1CS.
        let check_result = std::panic::catch_unwind(|| {
            r1cs.check_relation(&z).unwrap();
        });

        match (expect_success, check_result) {
            (true, Ok(_)) => {}
            (false, Err(_)) => {}
            (true, Err(_)) => panic!("Expected success but got a failure."),
            (false, Ok(_)) => panic!("Expected a failure but got success."),
        }
    }

    #[test]
    fn test_circom_conversion() {
        // expect it to pass for correct inputs.
        test_circom_conversion_logic(true, vec![("step_in".to_string(), vec![BigInt::from(3)])]);

        // expect it to fail for incorrect inputs.
        test_circom_conversion_logic(false, vec![("step_in".to_string(), vec![BigInt::from(7)])]);
    }
}
