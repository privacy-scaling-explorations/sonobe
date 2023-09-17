use std::fs::File;
use std::io::BufReader;
use std::error::Error;
use std::path::PathBuf;
use ark_bn254::{Bn254, Fr};
use ark_ff::PrimeField;
use ark_ff::biginteger;
use ark_ec::pairing::Pairing;
use num_bigint::BigInt;

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

pub fn extract_constraints_from_r1cs(filename: &str) -> Result<Vec<Constraints<Bn254>>, Box<dyn Error>> {
    let current_dir = std::env::current_dir()?;
    let filepath: PathBuf = [current_dir.to_str().unwrap(), filename].iter().collect();
    let file = File::open(filepath)?;
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

pub fn calculate_witness<I: IntoIterator<Item = (String, Vec<BigInt>)>>(inputs: I) -> Result<(), Box<dyn Error>> {
    let current_dir = std::env::current_dir()?;
    let wasm_path = current_dir.join("src").join("toy.wasm");

    let mut calculator = witness::WitnessCalculator::new(wasm_path)?;

    match calculator.calculate_witness(inputs, true) {
        Ok(witness) => {
            println!("Witness as BigInt:");
            for w in &witness {
                println!("{:?}", w);
            }
        },
        Err(e) => {
            eprintln!("Error while calculating witness: {:?}", e);
            return Err(Box::<dyn Error>::from(format!("Witness calculation failed: {}", e)));
        }
    }

    Ok(())
}

#[test]
fn from_circom() {
    let filename = "src/toy.r1cs";

    match extract_constraints_from_r1cs(filename) {
        Ok(constraints) => {
            println!("Original Constraints:");
            for constraint in &constraints {
                println!("{:?}", constraint);
            }

            println!("Converted Constraints:");
            let converted_constraints: Vec<Constraints<Bn254>> = constraints.iter().map(|constraint| {
                convert_constraints_bigint_to_scalar(constraint.clone())
            }).collect();

            for constraint in &converted_constraints {
                println!("{:?}", constraint);
            }

            let folding_r1cs = convert_to_folding_r1cs(converted_constraints);
            println!("Folding R1CS: {:?}", folding_r1cs);
        },
        Err(e) => {
            eprintln!("Error while extracting constraints: {:?}", e);
        }
    }

    let inputs = vec![
        ("step_in".to_string(), vec![BigInt::from(10)]),
        ("adder".to_string(), vec![BigInt::from(2)])
    ];

    if let Err(e) = calculate_witness(inputs) {
        eprintln!("Failed to calculate the witness: {:?}", e);
    }
}