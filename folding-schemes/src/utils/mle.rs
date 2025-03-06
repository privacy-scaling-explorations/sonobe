use crate::utils::mle::MultilinearExtension::{DenseMLE, SparseMLE};
use crate::utils::mle::SparseOrDensePolynomial::{DensePoly, SparsePoly};
/// Some basic MLE utilities
use ark_ff::{Field, PrimeField};
use ark_poly::univariate::{DensePolynomial, SparsePolynomial};
use ark_poly::{
    DenseMultilinearExtension, DenseUVPolynomial, Polynomial, SparseMultilinearExtension,
};
use ark_std::log2;
use matrex::Matrix;
use matrex::Matrix::{Dense, Sparse};

use super::vec::SparseMatrix;

/// Pad matrix so that its columns and rows are powers of two
pub fn pad_matrix<F: PrimeField>(m: &SparseMatrix<F>) -> SparseMatrix<F> {
    let mut r = m.clone();
    r.n_rows = m.n_rows.next_power_of_two();
    r.n_cols = m.n_cols.next_power_of_two();
    r
}

/// Returns the dense multilinear extension from the given matrix, without modifying the original
/// matrix.
pub fn matrix_to_dense_mle<F: PrimeField>(matrix: SparseMatrix<F>) -> DenseMultilinearExtension<F> {
    let n_vars: usize = (log2(matrix.n_rows) + log2(matrix.n_cols)) as usize; // n_vars = s + s'

    // Matrices might need to get padded before turned into an MLE
    let padded_matrix = pad_matrix(&matrix);

    // build dense vector representing the sparse padded matrix
    let mut v: Vec<F> = vec![F::zero(); padded_matrix.n_rows * padded_matrix.n_cols];
    for (row_i, row) in padded_matrix.coeffs.iter().enumerate() {
        for &(value, col_i) in row.iter() {
            v[(padded_matrix.n_cols * row_i) + col_i] = value;
        }
    }

    // convert the dense vector into a mle
    vec_to_dense_mle(n_vars, &v)
}

/// Takes the n_vars and a dense vector and returns its dense MLE.
pub fn vec_to_dense_mle<F: PrimeField>(n_vars: usize, v: &[F]) -> DenseMultilinearExtension<F> {
    let v_padded: Vec<F> = if v.len() != (1 << n_vars) {
        // pad to 2^n_vars
        [
            v.to_owned(),
            std::iter::repeat(F::zero())
                .take((1 << n_vars) - v.len())
                .collect(),
        ]
        .concat()
    } else {
        v.to_owned()
    };
    DenseMultilinearExtension::<F>::from_evaluations_vec(n_vars, v_padded)
}

/// Returns the sparse multilinear extension from the given matrix, without modifying the original
/// matrix.
pub fn matrix_to_mle<F: PrimeField>(m: SparseMatrix<F>) -> SparseMultilinearExtension<F> {
    let n_rows = m.n_rows.next_power_of_two();
    let n_cols = m.n_cols.next_power_of_two();
    let n_vars: usize = (log2(n_rows) + log2(n_cols)) as usize; // n_vars = s + s'

    // build the sparse vec representing the sparse matrix
    let mut v: Vec<(usize, F)> = Vec::new();
    for (i, row) in m.coeffs.iter().enumerate() {
        for (val, j) in row.iter() {
            v.push((i * n_cols + j, *val));
        }
    }

    // convert the dense vector into a mle
    vec_to_mle(n_vars, &v)
}

/// Takes the n_vars and a sparse vector and returns its sparse MLE.
pub fn vec_to_mle<F: PrimeField>(n_vars: usize, v: &[(usize, F)]) -> SparseMultilinearExtension<F> {
    SparseMultilinearExtension::<F>::from_evaluations(n_vars, v)
}

/// Takes the n_vars and a dense vector and returns its dense MLE.
pub fn dense_vec_to_dense_mle<F: PrimeField>(
    n_vars: usize,
    v: &[F],
) -> DenseMultilinearExtension<F> {
    // Pad to 2^n_vars
    let v_padded: Vec<F> = [
        v.to_owned(),
        std::iter::repeat(F::zero())
            .take((1 << n_vars) - v.len())
            .collect(),
    ]
    .concat();
    DenseMultilinearExtension::<F>::from_evaluations_vec(n_vars, v_padded)
}

/// Takes the n_vars and a dense vector and returns its sparse MLE.
pub fn dense_vec_to_mle<F: PrimeField>(n_vars: usize, v: &[F]) -> SparseMultilinearExtension<F> {
    let v_sparse = v
        .iter()
        .enumerate()
        .map(|(i, v_i)| (i, *v_i))
        .collect::<Vec<(usize, F)>>();
    SparseMultilinearExtension::<F>::from_evaluations(n_vars, &v_sparse)
}

/// Enum representing either a sparse or dense polynomial over a field.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum SparseOrDensePolynomial<F: Field> {
    SparsePoly(SparsePolynomial<F>),
    DensePoly(DensePolynomial<F>),
}

impl<F: Field> SparseOrDensePolynomial<F> {
    /// Creates a `SparseOrDensePolynomial` from a dense polynomial.
    pub fn from_dense(dense: DensePolynomial<F>) -> Self {
        DensePoly(dense)
    }

    /// Creates a `SparseOrDensePolynomial` from a sparse polynomial.
    pub fn from_sparse(sparse: SparsePolynomial<F>) -> Self {
        SparsePoly(sparse)
    }

    /// Returns the coefficients of the polynomial as a vector.
    pub fn coeffs(&self) -> Vec<F> {
        match &self {
            SparsePoly(poly) => {
                let mut coeffs = Vec::with_capacity(poly.len()); // Preallocate with known size
                coeffs.extend(poly.iter().map(|&(_, coeff)| coeff));
                coeffs
            }
            DensePoly(poly) => poly.coeffs().to_vec(),
        }
    }

    /// Evaluates the polynomial at a given field element `point`.
    pub fn evaluate(&self, point: &F) -> F {
        match &self {
            SparsePoly(poly) => poly.evaluate(point),
            DensePoly(poly) => poly.evaluate(point),
        }
    }
}

/// Enum representing either a dense or sparse multilinear extension over a field.
#[derive(Debug)]
pub enum MultilinearExtension<F: Field> {
    DenseMLE(DenseMultilinearExtension<F>),
    SparseMLE(SparseMultilinearExtension<F>),
}

impl<F: Field> MultilinearExtension<F> {
    /// Constructs a `MultilinearExtension` from a matrix of evaluations.
    ///
    /// - `matrix`: The input matrix containing evaluations.
    /// - `n_vars`: The number of variables in the extension.
    pub fn from_evaluations(matrix: &Matrix<F>, n_vars: usize) -> MultilinearExtension<F> {
        match &matrix {
            Dense(matrix) => {
                let mut v_padded = Vec::with_capacity(1 << n_vars);
                v_padded.extend_from_slice(matrix.as_slice());
                v_padded.resize(1 << n_vars, F::zero()); // Pad with zeros if necessary
                let mle = DenseMultilinearExtension::<F>::from_evaluations_vec(n_vars, v_padded);
                DenseMLE(mle)
            }
            Sparse(matrix) => SparseMLE(SparseMultilinearExtension::<F>::from_evaluations(
                n_vars,
                &matrix.as_slice().to_owned(),
            )),
        }
    }

    /// Evaluates the multilinear extension at given points.
    pub fn evaluate(&self, points: &[F]) -> F {
        match &self {
            DenseMLE(mle) => mle.evaluate(&points.to_vec()),
            SparseMLE(mle) => mle.evaluate(&points.to_vec()),
        }
    }

    /// Returns the number of variables in the multilinear extension.
    pub fn num_vars(&self) -> usize {
        match &self {
            DenseMLE(mle) => mle.num_vars,
            SparseMLE(mle) => mle.num_vars,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        arith::ccs::tests::get_test_z,
        utils::multilinear_polynomial::fix_variables,
        utils::multilinear_polynomial::tests::fix_last_variables,
        utils::{hypercube::BooleanHypercube, vec::tests::to_F_matrix},
    };
    use ark_poly::MultilinearExtension;
    use ark_std::Zero;

    use ark_pallas::Fr;

    #[test]
    fn test_matrix_to_mle() {
        let A = to_F_matrix::<Fr>(vec![
            vec![2, 3, 4, 4],
            vec![4, 11, 14, 14],
            vec![2, 8, 17, 17],
            vec![420, 4, 2, 0],
        ]);

        let A_mle = matrix_to_mle(A);
        assert_eq!(A_mle.evaluations.len(), 15); // 15 non-zero elements
        assert_eq!(A_mle.num_vars, 4); // 4x4 matrix, thus 2bit x 2bit, thus 2^4=16 evals

        let A = to_F_matrix::<Fr>(vec![
            vec![2, 3, 4, 4, 1],
            vec![4, 11, 14, 14, 2],
            vec![2, 8, 17, 17, 3],
            vec![420, 4, 2, 0, 4],
            vec![420, 4, 2, 0, 5],
        ]);
        let A_mle = matrix_to_mle(A.clone());
        assert_eq!(A_mle.evaluations.len(), 23); // 23 non-zero elements
        assert_eq!(A_mle.num_vars, 6); // 5x5 matrix, thus 3bit x 3bit, thus 2^6=64 evals

        // check that the A_mle evaluated over the boolean hypercube equals the matrix A_i_j values
        let bhc = BooleanHypercube::new(A_mle.num_vars);
        let A_padded = pad_matrix(&A);
        let A_padded_dense = A_padded.to_dense();
        for (i, A_row) in A_padded_dense.iter().enumerate() {
            for (j, _) in A_row.iter().enumerate() {
                let s_i_j = bhc.at_i(i * A_row.len() + j);
                assert_eq!(A_mle.fix_variables(&s_i_j)[0], A_padded_dense[i][j]);
            }
        }
    }

    #[test]
    fn test_vec_to_mle() {
        let z = get_test_z::<Fr>(3);
        let n_vars = 3;
        let z_mle = dense_vec_to_mle(n_vars, &z);

        // check that the z_mle evaluated over the boolean hypercube equals the vec z_i values
        let bhc = BooleanHypercube::new(z_mle.num_vars);
        for (i, z_i) in z.iter().enumerate() {
            let s_i = bhc.at_i(i);
            assert_eq!(z_mle.fix_variables(&s_i)[0], z_i.clone());
        }
        // for the rest of elements of the boolean hypercube, expect it to evaluate to zero
        for i in (z.len())..(1 << z_mle.num_vars) {
            let s_i = bhc.at_i(i);
            assert_eq!(z_mle.fix_variables(&s_i)[0], Fr::zero());
        }
    }

    #[test]
    fn test_fix_variables() {
        let A = to_F_matrix(vec![
            vec![2, 3, 4, 4],
            vec![4, 11, 14, 14],
            vec![2, 8, 17, 17],
            vec![420, 4, 2, 0],
        ]);

        let A_mle = matrix_to_dense_mle(A.clone());
        let A = A.to_dense();
        let bhc = BooleanHypercube::new(2);
        for (i, y) in bhc.enumerate() {
            // First check that the arkworks and espresso funcs match
            let expected_fix_left = A_mle.fix_variables(&y); // try arkworks fix_variables
            let fix_left = fix_variables(&A_mle, &y); // try espresso fix_variables
            assert_eq!(fix_left, expected_fix_left);

            // Check that fixing first variables pins down a column
            // i.e. fixing x to 0 will return the first column
            //      fixing x to 1 will return the second column etc.
            let column_i: Vec<Fr> = A.clone().iter().map(|x| x[i]).collect();
            assert_eq!(fix_left.evaluations, column_i);

            // Now check that fixing last variables pins down a row
            // i.e. fixing y to 0 will return the first row
            //      fixing y to 1 will return the second row etc.
            let row_i: Vec<Fr> = A[i].clone();
            let fix_right = fix_last_variables(&A_mle, &y);
            assert_eq!(fix_right.evaluations, row_i);
        }
    }
}
