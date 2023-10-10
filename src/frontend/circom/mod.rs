use std::{error::Error, fs::File, io::BufReader, path::Path};

use color_eyre::Result;
use num_bigint::BigInt;

use ark_circom::{circom::r1cs_reader, WitnessCalculator};
use ark_ec::pairing::Pairing;
use ark_ff::PrimeField;

use crate::ccs::r1cs::R1CS;
use crate::utils::vec::SparseMatrix;

// Define the sparse matrices on PrimeFiled
pub type Constraints<F> = (ConstraintVec<F>, ConstraintVec<F>, ConstraintVec<F>);
pub type ConstraintVec<F> = Vec<(usize, F)>;

type ExtractedConstraintsResult<F> = Result<(Vec<Constraints<F>>, usize, usize), Box<dyn Error>>;

// Extract the r1cs file
pub fn extract_constraints_from_r1cs<E>(
    r1cs_filepath: &Path,
) -> ExtractedConstraintsResult<E::ScalarField>
where
    E: Pairing,
{
    // Open the .r1cs file and create a reader
    let file = File::open(r1cs_filepath)?;
    let reader = BufReader::new(file);

    // Read the R1CS file and extract the constraints directly
    let r1cs_file = r1cs_reader::R1CSFile::<E>::new(reader)?;
    let pub_io_len = (r1cs_file.header.n_pub_in + r1cs_file.header.n_pub_out) as usize;
    let r1cs = r1cs_reader::R1CS::<E>::from(r1cs_file);
    let num_variables = r1cs.num_variables;
    let constraints: Vec<Constraints<E::ScalarField>> = r1cs.constraints;

    Ok((constraints, pub_io_len, num_variables))
}

// Convert a set of constraints from ark-circom into R1CS format of folding_schemes
pub fn convert_to_folding_schemes_r1cs<F>(
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

// Calculate the witness given the WASM filepath and inputs.
pub fn calculate_witness<I: IntoIterator<Item = (String, Vec<BigInt>)>>(
    wasm_filepath: &Path,
    inputs: I,
) -> Result<Vec<BigInt>> {
    let mut calculator = WitnessCalculator::new(wasm_filepath.clone())?;
    calculator.calculate_witness(inputs, true)
}

// Convert a num_bigint's BigInt to PrimeField's BigInt
fn num_bigint_to_ark_bigint<F: PrimeField>(value: &BigInt) -> Result<F::BigInt, Box<dyn Error>> {
    let big_uint = value
        .to_biguint()
        .ok_or_else(|| "BigInt is negative".to_string())?;
    F::BigInt::try_from(big_uint).map_err(|_| "BigInt conversion failed".to_string().into())
}

// Convert R1CS constraints and witness from ark-circom format
// into folding-schemes R1CS and z format.
pub fn circom_to_folding_schemes_r1cs_and_z<F>(
    constraints: Vec<Constraints<F>>,
    witness: &[BigInt],
    pub_io_len: usize,
    num_variables: usize,
) -> Result<(R1CS<F>, Vec<F>), Box<dyn Error>>
where
    F: PrimeField,
{
    let folding_schemes_r1cs =
        convert_to_folding_schemes_r1cs(constraints, pub_io_len, num_variables);

    let z: Result<Vec<F>, _> = witness
        .iter()
        .map(|big_int| {
            let ark_big_int = num_bigint_to_ark_bigint::<F>(big_int)?;
            F::from_bigint(ark_big_int).ok_or_else(|| {
                "Failed to convert bigint to field element"
                    .to_string()
                    .into()
            })
        })
        .collect();

    z.map(|z| (folding_schemes_r1cs, z))
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bn254::Bn254;
    use num_bigint::BigInt;
    use std::env;

    /*
    test_circuit represents 35 = x^3 + x + 5 in test_folder/test_circuit.circom.
    In the test_circom_conversion_success function, x is assigned the value 3, which satisfies the R1CS correctly.
    In the test_circom_conversion_failure function, x is assigned the value 6, which doesn't satisfy the R1CS.
    */

    fn test_circom_conversion_logic(expect_success: bool, inputs: Vec<(String, Vec<BigInt>)>) {
        let current_dir = env::current_dir().unwrap();
        let base_path = current_dir.join("src/frontend/circom/test_folder");
        let r1cs_filepath = base_path.join("test_circuit.r1cs");
        let wasm_filepath = base_path.join("test_circuit.wasm");

        assert!(r1cs_filepath.exists());
        assert!(wasm_filepath.exists());

        let (constraints, pub_io_len, num_variables) =
            extract_constraints_from_r1cs::<Bn254>(&r1cs_filepath)
                .expect("Error extracting constraints");
        assert!(!constraints.is_empty());

        let witness = calculate_witness(&wasm_filepath, inputs).expect("Error calculating witness");
        assert!(!witness.is_empty());

        let (r1cs, z) = circom_to_folding_schemes_r1cs_and_z(
            constraints,
            &witness,
            pub_io_len,
            num_variables,
        )
        .expect("Error converting to folding schemes");
        assert!(!z.is_empty());

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
        // expect it to pass for correct inputs
        test_circom_conversion_logic(true, vec![("step_in".to_string(), vec![BigInt::from(3)])]);

        // expect it to fail for incorrect inputs
        test_circom_conversion_logic(false, vec![("step_in".to_string(), vec![BigInt::from(7)])]);
    }
}
