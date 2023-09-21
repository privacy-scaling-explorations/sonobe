use std::{fs::File, io::BufReader, path::PathBuf, error::Error};

use num_bigint::BigInt;
use color_eyre::Result;

use ark_ff::PrimeField;
use ark_ec::pairing::Pairing;
use ark_circom::{circom::r1cs_reader, WitnessCalculator};
use ark_bn254::{Bn254, Fr};

use crate::ccs::r1cs::R1CS;
use crate::utils::vec::SparseMatrix;

pub type Constraints<E> = (ConstraintVec<E>, ConstraintVec<E>, ConstraintVec<E>);
pub type ConstraintVec<E> = Vec<(usize, <E as Pairing>::ScalarField)>;

// Convert the BigInt constraints to Bn254's ScalarField constraints.
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

// Extract R1CS constraints from the provided R1CS file path.
pub fn extract_constraints_from_r1cs(r1cs_filepath: &PathBuf) -> Result<(Vec<Constraints<Bn254>>, usize), Box<dyn Error>> {
    let file = File::open(r1cs_filepath)?;
    let reader = BufReader::new(file);

    let r1cs_file = r1cs_reader::R1CSFile::<Bn254>::new(reader)?;
    let num_public_inputs = (r1cs_file.header.n_pub_in + r1cs_file.header.n_pub_out) as usize;
    let r1cs = r1cs_reader::R1CS::<Bn254>::from(r1cs_file);
    Ok((r1cs.constraints, num_public_inputs)) 
}

// Convert R1CS constraints for Bn254 to the format suited for folding-schemes.
pub fn convert_to_folding_schemes_r1cs(constraints: Vec<Constraints<Bn254>>, public_inputs: usize) -> R1CS<Fr> {
    let mut a_matrix: Vec<Vec<(Fr, usize)>> = Vec::new();
    let mut b_matrix: Vec<Vec<(Fr, usize)>> = Vec::new();
    let mut c_matrix: Vec<Vec<(Fr, usize)>> = Vec::new();

    let n_rows = constraints.len(); 

    for (ai, bi, ci) in constraints {
        a_matrix.push(ai.into_iter().map(|(index, scalar)| (scalar, index)).collect());
        b_matrix.push(bi.into_iter().map(|(index, scalar)| (scalar, index)).collect());
        c_matrix.push(ci.into_iter().map(|(index, scalar)| (scalar, index)).collect());
    }
 
    let l = public_inputs;
    let n_cols =  a_matrix.first().map(|vec| vec.len()).unwrap_or(0);

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

// Calculate the witness given the WASM filepath and inputs.
pub fn calculate_witness<I: IntoIterator<Item = (String, Vec<BigInt>)>>(wasm_filepath: &PathBuf, inputs: I) -> Result<Vec<BigInt>> {
    let mut calculator = WitnessCalculator::new(wasm_filepath.clone())?;
    calculator.calculate_witness(inputs, true)
}

// Helper function to convert `num_bigint::BigInt` to `ark_ff::BigInt`.
fn num_bigint_to_ark_bigint(value: &num_bigint::BigInt) -> Result<ark_ff::BigInt<4>, Box<dyn Error>> {
    let big_uint = value.to_biguint().ok_or_else(|| Box::new(std::io::Error::new(std::io::ErrorKind::Other, "BigInt is negative")))?;
    Ok(ark_ff::BigInt::<4>::try_from(big_uint).map_err(|_| Box::new(std::io::Error::new(std::io::ErrorKind::Other, "BigInt conversion failed")))?)
}

// Convert R1CS constraints and witness from Circom format to folding-schemes R1CS and z format.
pub fn circom_to_folding_schemes_r1cs_and_z(
    constraints: Vec<Constraints<Bn254>>,
    witness: &Vec<BigInt>,
    public_inputs: usize,
) -> Result<(R1CS<Fr>, Vec<Fr>), Box<dyn Error>> {
    let folding_schemes_r1cs = convert_to_folding_schemes_r1cs(constraints, public_inputs);

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
        
        let base_path = current_dir.join("src/frontend/circom/test_folder");
        let r1cs_filepath = base_path.join("test_circuit.r1cs");
        let wasm_filepath = base_path.join("test_circuit.wasm");

        /*
        This is the test_circuit.cirom file.
        When step_in equals 3, it will pass the test function.

        template Example () {
            signal input step_in;
            signal output step_out;   
            signal temp;
            
            temp <== step_in * step_in;
            step_out <== temp * step_in + step_in + 5;
            step_out === 35; 
        }
        component main = Example();
        */
    
        assert!(r1cs_filepath.exists());
        assert!(wasm_filepath.exists());
    
        let (constraints, public_inputs) = extract_constraints_from_r1cs(&r1cs_filepath).expect("Error");
        assert!(!constraints.is_empty());
    
        let converted_constraints: Vec<Constraints<Bn254>> = constraints
            .iter()
            .map(|constraint| convert_constraints_bigint_to_scalar(constraint.clone()))
            .collect();
        assert_eq!(constraints.len(), converted_constraints.len());
    
        let inputs = vec![
            // success
            ("step_in".to_string(), vec![BigInt::from(3)]),
            // fail
            // ("step_in".to_string(), vec![BigInt::from(6)]),
        ];
    
        let witness = calculate_witness(&wasm_filepath, inputs).expect("Error");
        assert!(!witness.is_empty());
    
        let (r1cs, z) = circom_to_folding_schemes_r1cs_and_z(converted_constraints, &witness, public_inputs)
            .expect("Error");
        assert!(!z.is_empty());
    
        r1cs.check_relation(&z).expect("Error");
    }    

}
