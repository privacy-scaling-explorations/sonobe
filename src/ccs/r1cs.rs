use ark_ff::PrimeField;

use crate::utils::vec::*;

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct R1CS<F: PrimeField> {
    pub l: usize, // io len
    pub A: SparseMatrix<F>,
    pub B: SparseMatrix<F>,
    pub C: SparseMatrix<F>,
}
impl<F: PrimeField> R1CS<F> {
    /// returns a tuple containing (w, x) (witness and public inputs respectively)
    pub fn split_z(&self, z: &[F]) -> (Vec<F>, Vec<F>) {
        (z[self.l + 1..].to_vec(), z[1..self.l + 1].to_vec())
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::utils::vec::tests::{to_F_matrix, to_F_vec};

    pub fn get_test_r1cs<F: PrimeField>() -> R1CS<F> {
        // R1CS for: x^3 + x + 5 = y (example from article
        // https://www.vitalik.ca/general/2016/12/10/qap.html )
        let A = dense_matrix_to_sparse(to_F_matrix::<F>(vec![
            vec![0, 1, 0, 0, 0, 0],
            vec![0, 0, 0, 1, 0, 0],
            vec![0, 1, 0, 0, 1, 0],
            vec![5, 0, 0, 0, 0, 1],
        ]));
        let B = dense_matrix_to_sparse(to_F_matrix::<F>(vec![
            vec![0, 1, 0, 0, 0, 0],
            vec![0, 1, 0, 0, 0, 0],
            vec![1, 0, 0, 0, 0, 0],
            vec![1, 0, 0, 0, 0, 0],
        ]));
        let C = dense_matrix_to_sparse(to_F_matrix::<F>(vec![
            vec![0, 0, 0, 1, 0, 0],
            vec![0, 0, 0, 0, 1, 0],
            vec![0, 0, 0, 0, 0, 1],
            vec![0, 0, 1, 0, 0, 0],
        ]));

        R1CS::<F> { l: 1, A, B, C }
    }

    pub fn get_test_z<F: PrimeField>(input: usize) -> Vec<F> {
        // z = (1, io, w)
        to_F_vec(vec![
            1,
            input,                             // io
            input * input * input + input + 5, // x^3 + x + 5
            input * input,                     // x^2
            input * input * input,             // x^2 * x
            input * input * input + input,     // x^3 + x
        ])
    }
}
