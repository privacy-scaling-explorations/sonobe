use std::fs::File;
use std::io::BufReader;
use std::error::Error;
use std::path::PathBuf;

use num_bigint::BigInt;
use color_eyre::Result;

use ark_bn254::{Bn254, Fr};
use ark_ff::PrimeField;
use ark_ff::biginteger;
use ark_ec::pairing::Pairing;

mod r1cs_reader;
mod witness;

pub type Constraints<E> = (ConstraintVec<E>, ConstraintVec<E>, ConstraintVec<E>);
pub type ConstraintVec<E> = Vec<(usize, <E as Pairing>::ScalarField)>;

pub fn bigint_to_bn254_scalar(bigint: biginteger::BigInt<4>) -> Option<Fr> {
    Fr::from_bigint(bigint)
}

pub fn convert_constraints_bigint_to_scalar(constraints: Constraints<Bn254>) -> Constraints<Bn254> {
    let convert_vec = |vec: ConstraintVec<Bn254>| -> ConstraintVec<Bn254> {
        vec.into_iter()
            .filter_map(|(index, bigint)| {
                match bigint_to_bn254_scalar(bigint.into()) {
                    Some(scalar) => Some((index, scalar)),
                    None => None
                }
            })
            .collect()
    };

    (convert_vec(constraints.0), convert_vec(constraints.1), convert_vec(constraints.2))
}

pub fn extract_constraints_from_r1cs(filename: &PathBuf) -> Result<Vec<Constraints<Bn254>>, Box<dyn Error>> {
    let file = File::open(filename)?;
    let reader = BufReader::new(file);

    let r1cs_file = r1cs_reader::R1CSFile::<Bn254>::new(reader)?;
    let r1cs = r1cs_reader::R1CS::<Bn254>::from(r1cs_file);
    Ok(r1cs.constraints)
}

pub fn convert_to_folding_r1cs(constraints: Vec<Constraints<Bn254>>) -> crate::ccs::r1cs::R1CS<Fr> {
    let mut a_matrix: Vec<Vec<(Fr, usize)>> = Vec::new();
    let mut b_matrix: Vec<Vec<(Fr, usize)>> = Vec::new();
    let mut c_matrix: Vec<Vec<(Fr, usize)>> = Vec::new();

    let n_rows = constraints.len(); 

    for (ai, bi, ci) in constraints {
        a_matrix.push(ai.into_iter().map(|(index, scalar)| (scalar, index)).collect());
        b_matrix.push(bi.into_iter().map(|(index, scalar)| (scalar, index)).collect());
        c_matrix.push(ci.into_iter().map(|(index, scalar)| (scalar, index)).collect());
    }

    let l = a_matrix.first().map(|vec| vec.len()).unwrap_or(0);
    let n_cols = l;

    let A = crate::utils::vec::SparseMatrix::<Fr> {
        n_rows,
        n_cols,
        coeffs: a_matrix,
    };
    let B = crate::utils::vec::SparseMatrix::<Fr> {
        n_rows,
        n_cols,
        coeffs: b_matrix,
    };
    let C = crate::utils::vec::SparseMatrix::<Fr> {
        n_rows,
        n_cols,
        coeffs: c_matrix,
    };

    crate::ccs::r1cs::R1CS::<Fr> {
        l,
        A,
        B,
        C,
    }
}

pub fn calculate_witness<I: IntoIterator<Item = (String, Vec<BigInt>)>>(wasm_filepath: &PathBuf, inputs: I) -> Result<Vec<BigInt>> {
    let mut calculator = witness::WitnessCalculator::new(wasm_filepath.clone())?;
    calculator.calculate_witness(inputs, true)
}

fn bigint_to_ark_bigint(value: &num_bigint::BigInt) -> Result<ark_ff::BigInt<4>, Box<dyn Error>> {
    let big_uint = value.to_biguint().ok_or_else(|| Box::new(std::io::Error::new(std::io::ErrorKind::Other, "BigInt is negative")))?;
    Ok(ark_ff::BigInt::<4>::try_from(big_uint).map_err(|_| Box::new(std::io::Error::new(std::io::ErrorKind::Other, "BigInt conversion failed")))?)
}

pub fn circom_to_folding_r1cs_and_z(
    constraints: Vec<Constraints<Bn254>>,
    witness: &Vec<BigInt>,
) -> Result<(crate::ccs::r1cs::R1CS<Fr>, Vec<Fr>), Box<dyn Error>> {
    let folding_r1cs = convert_to_folding_r1cs(constraints);

    let z: Vec<Fr> = witness
        .iter()
        .filter_map(|big_int| {
            match bigint_to_ark_bigint(big_int) {
                Ok(ark_big_int) => bigint_to_bn254_scalar(ark_big_int.into()),
                Err(_) => None
            }
        })
        .collect();

    Ok((folding_r1cs, z))
}

#[cfg(test)]
mod tests {
    use ark_bn254::Bn254;
    use num_bigint::BigInt;

    use super::Constraints;
    use super::calculate_witness;
    use super::circom_to_folding_r1cs_and_z;
    use super::convert_constraints_bigint_to_scalar;
    use super::extract_constraints_from_r1cs;

    #[test]
    fn test_circom_to_folding_conversion() {
        let current_dir = std::env::current_dir().unwrap();
        
        let r1cs_filepath = current_dir.join("src").join("frontend").join("circom").join("test_folder").join("toy.r1cs");
        let wasm_filepath = current_dir.join("src").join("frontend").join("circom").join("test_folder").join("toy.wasm");

        assert!(r1cs_filepath.exists(), "R1CS filepath does not exist.");
        assert!(wasm_filepath.exists(), "WASM filepath does not exist.");

        let constraints = extract_constraints_from_r1cs(&r1cs_filepath).expect("Failed to extract constraints");
        assert!(!constraints.is_empty(), "No constraints were extracted.");

        let converted_constraints: Vec<Constraints<Bn254>> = constraints
            .iter()
            .map(|constraint| convert_constraints_bigint_to_scalar(constraint.clone()))
            .collect();
        assert_eq!(constraints.len(), converted_constraints.len(), "Converted constraints count doesn't match the original.");

        let inputs = vec![
            ("step_in".to_string(), vec![BigInt::from(10)]),
            ("adder".to_string(), vec![BigInt::from(2)]),
        ];

        let witness = calculate_witness(&wasm_filepath, inputs).expect("Failed to calculate the witness");
        assert!(!witness.is_empty(), "Witness calculation resulted in an empty vector.");

        let (r1cs, z) = circom_to_folding_r1cs_and_z(converted_constraints, &witness)
            .expect("Failed to convert circom R1CS to folding R1CS");
        assert!(!z.is_empty(), "The z vector is empty.");

        r1cs.check_relation(&z).expect("R1CS relation check failed");
    }

}
