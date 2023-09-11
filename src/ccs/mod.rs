use ark_ec::CurveGroup;
use ark_std::log2;
use ark_std::{One, Zero};
use std::ops::Neg;

use crate::utils::vec::*;
use crate::Error;

pub mod r1cs;
use r1cs::R1CS;

/// CCS represents the Customizable Constraint Systems structure defined in
/// the [CCS paper](https://eprint.iacr.org/2023/552)
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct CCS<C: CurveGroup> {
    /// m: number of rows in M_i (such that M_i \in F^{m, n})
    pub m: usize,
    /// n = |z|, number of cols in M_i
    pub n: usize,
    /// l = |io|, size of public input/output
    pub l: usize,
    /// t = |M|, number of matrices
    pub t: usize,
    /// q = |c| = |S|, number of multisets
    pub q: usize,
    /// d: max degree in each variable
    pub d: usize,
    /// s = log(m), dimension of x
    pub s: usize,
    /// s_prime = log(n), dimension of y
    pub s_prime: usize,

    /// vector of matrices
    pub M: Vec<SparseMatrix<C::ScalarField>>,
    /// vector of multisets
    pub S: Vec<Vec<usize>>,
    /// vector of coefficients
    pub c: Vec<C::ScalarField>,
}

impl<C: CurveGroup> CCS<C> {
    /// check that a CCS structure is satisfied by a z vector. Only for testing.
    pub fn check_relation(&self, z: &[C::ScalarField]) -> Result<(), Error> {
        let mut result = vec![C::ScalarField::zero(); self.m];

        for i in 0..self.q {
            // extract the needed M_j matrices out of S_i
            let vec_M_j: Vec<&SparseMatrix<C::ScalarField>> =
                self.S[i].iter().map(|j| &self.M[*j]).collect();

            // complete the hadamard chain
            let mut hadamard_result = vec![C::ScalarField::one(); self.m];
            for M_j in vec_M_j.into_iter() {
                hadamard_result = hadamard(&hadamard_result, &mat_vec_mul_sparse(M_j, z));
            }

            // multiply by the coefficient of this step
            let c_M_j_z = vec_scalar_mul(&hadamard_result, &self.c[i]);

            // add it to the final vector
            result = vec_add(&result, &c_M_j_z);
        }

        // make sure the final vector is all zeroes
        for e in result {
            if !e.is_zero() {
                return Err(Error::NotSatisfied);
            }
        }

        Ok(())
    }
}

impl<C: CurveGroup> CCS<C> {
    pub fn from_r1cs(r1cs: R1CS<C::ScalarField>) -> Self {
        let m = r1cs.A.n_rows;
        let n = r1cs.A.n_cols;
        CCS {
            m,
            n,
            l: r1cs.l,
            s: log2(m) as usize,
            s_prime: log2(n) as usize,
            t: 3,
            q: 2,
            d: 2,

            S: vec![vec![0, 1], vec![2]],
            c: vec![C::ScalarField::one(), C::ScalarField::one().neg()],
            M: vec![r1cs.A, r1cs.B, r1cs.C],
        }
    }
    pub fn to_r1cs(self) -> R1CS<C::ScalarField> {
        R1CS::<C::ScalarField> {
            l: self.l,
            A: self.M[0].clone(),
            B: self.M[1].clone(),
            C: self.M[2].clone(),
        }
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::ccs::r1cs::tests::{get_test_r1cs, get_test_z as r1cs_get_test_z};
    use ark_ff::PrimeField;
    use ark_pallas::Projective;

    pub fn get_test_ccs<C: CurveGroup>() -> CCS<C> {
        let r1cs = get_test_r1cs::<C::ScalarField>();
        CCS::<C>::from_r1cs(r1cs)
    }
    pub fn get_test_z<F: PrimeField>(input: usize) -> Vec<F> {
        r1cs_get_test_z(input)
    }

    /// Test that a basic CCS relation can be satisfied
    #[test]
    fn test_ccs_relation() {
        let ccs = get_test_ccs::<Projective>();
        let z = get_test_z(3);

        ccs.check_relation(&z).unwrap();
    }
}
