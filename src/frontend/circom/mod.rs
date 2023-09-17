use std::{fs::File, io::BufReader, path::PathBuf, error::Error};

use num_bigint::BigInt;
use color_eyre::Result;

use ark_bn254::{Bn254, Fr};
use ark_ff::PrimeField;
use ark_ec::pairing::Pairing;

use crate::ccs::r1cs::R1CS;
use crate::utils::vec::SparseMatrix;

mod r1cs_reader;
mod witness;

pub type Constraints<E> = (ConstraintVec<E>, ConstraintVec<E>, ConstraintVec<E>);
pub type ConstraintVec<E> = Vec<(usize, <E as Pairing>::ScalarField)>;

pub fn convert_constraints_bigint_to_scalar(constraints: Constraints<Bn254>) -> Constraints<Bn254> {
    let convert_vec = |vec: ConstraintVec<Bn254>| -> ConstraintVec<Bn254> {
        vec.into_iter()
            .filter_map(|(index, bigint)| {
                match Fr::from_bigint(bigint.into()) {
                    Some(scalar) => Some((index, scalar)),
                    None => None
                }
            })
            .collect()
    };

    (convert_vec(constraints.0), convert_vec(constraints.1), convert_vec(constraints.2))
}

pub fn extract_constraints_from_r1cs(r1cs_filepath: &PathBuf) -> Result<Vec<Constraints<Bn254>>, Box<dyn Error>> {
    let file = File::open(r1cs_filepath)?;
    let reader = BufReader::new(file);

    let r1cs_file = r1cs_reader::R1CSFile::<Bn254>::new(reader)?;
    let r1cs = r1cs_reader::R1CS::<Bn254>::from(r1cs_file);
    Ok(r1cs.constraints)
}

pub fn convert_to_folding_schemes_r1cs(constraints: Vec<Constraints<Bn254>>) -> R1CS<Fr> {
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

    let A = SparseMatrix::<Fr> {
        n_rows,
        n_cols,
        coeffs: a_matrix,
    };
    let B = SparseMatrix::<Fr> {
        n_rows,
        n_cols,
        coeffs: b_matrix,
    };
    let C = SparseMatrix::<Fr> {
        n_rows,
        n_cols,
        coeffs: c_matrix,
    };

    R1CS::<Fr> {
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

fn num_bigint_to_ark_bigint(value: &num_bigint::BigInt) -> Result<ark_ff::BigInt<4>, Box<dyn Error>> {
    let big_uint = value.to_biguint().ok_or_else(|| Box::new(std::io::Error::new(std::io::ErrorKind::Other, "BigInt is negative")))?;
    Ok(ark_ff::BigInt::<4>::try_from(big_uint).map_err(|_| Box::new(std::io::Error::new(std::io::ErrorKind::Other, "BigInt conversion failed")))?)
}

pub fn circom_to_folding_schemes_r1cs_and_z(
    constraints: Vec<Constraints<Bn254>>,
    witness: &Vec<BigInt>,
) -> Result<(R1CS<Fr>, Vec<Fr>), Box<dyn Error>> {
    let folding_schemes_r1cs = convert_to_folding_schemes_r1cs(constraints);

    let z: Vec<Fr> = witness
        .iter()
        .filter_map(|big_int| {
            match num_bigint_to_ark_bigint(big_int) {
                Ok(ark_big_int) => Fr::from_bigint(ark_big_int.into()),
                Err(_) => None
            }
        })
        .collect();

    Ok((folding_schemes_r1cs, z))
}

#[cfg(test)]
mod tests {
    use ark_bn254::Bn254;
    use num_bigint::BigInt;

    use super::Constraints;
    use super::calculate_witness;
    use super::circom_to_folding_schemes_r1cs_and_z;
    use super::convert_constraints_bigint_to_scalar;
    use super::extract_constraints_from_r1cs;

    #[test]
    fn test_circom_to_folding_conversion() {
        let current_dir = std::env::current_dir().unwrap();
        
        let r1cs_filepath = current_dir.join("src").join("frontend").join("circom").join("test_folder").join("toy.r1cs");
        let wasm_filepath = current_dir.join("src").join("frontend").join("circom").join("test_folder").join("toy.wasm");
    
        assert!(r1cs_filepath.exists());
        assert!(wasm_filepath.exists());
    
        let constraints = extract_constraints_from_r1cs(&r1cs_filepath).expect("Error");
        assert!(!constraints.is_empty());
    
        let converted_constraints: Vec<Constraints<Bn254>> = constraints
            .iter()
            .map(|constraint| convert_constraints_bigint_to_scalar(constraint.clone()))
            .collect();
        assert_eq!(constraints.len(), converted_constraints.len());
    
        let inputs = vec![
            ("step_in".to_string(), vec![BigInt::from(10)]),
            ("adder".to_string(), vec![BigInt::from(2)]),
        ];
    
        let witness = calculate_witness(&wasm_filepath, inputs).expect("Error");
        assert!(!witness.is_empty());
    
        let (r1cs, z) = circom_to_folding_schemes_r1cs_and_z(converted_constraints, &witness)
            .expect("Error");
        assert!(!z.is_empty());
    
        r1cs.check_relation(&z).expect("Error");
    }    

}
