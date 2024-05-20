use ark_ff::PrimeField;
use ark_poly::{
    univariate::DensePolynomial, EvaluationDomain, Evaluations, GeneralEvaluationDomain,
};
pub use ark_relations::r1cs::Matrix as R1CSMatrix;
use ark_std::cfg_iter;
use rayon::iter::{IndexedParallelIterator, IntoParallelRefIterator, ParallelIterator};

use crate::Error;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SparseMatrix<F: PrimeField> {
    pub n_rows: usize,
    pub n_cols: usize,
    /// coeffs = R1CSMatrix = Vec<Vec<(F, usize)>>, which contains each row and the F is the value
    /// of the coefficient and the usize indicates the column position
    pub coeffs: R1CSMatrix<F>,
}

impl<F: PrimeField> SparseMatrix<F> {
    pub fn to_dense(&self) -> Vec<Vec<F>> {
        let mut r: Vec<Vec<F>> = vec![vec![F::zero(); self.n_cols]; self.n_rows];
        for (row_i, row) in self.coeffs.iter().enumerate() {
            for &(value, col_i) in row.iter() {
                r[row_i][col_i] = value;
            }
        }
        r
    }
}

pub fn dense_matrix_to_sparse<F: PrimeField>(m: Vec<Vec<F>>) -> SparseMatrix<F> {
    let mut r = SparseMatrix::<F> {
        n_rows: m.len(),
        n_cols: m[0].len(),
        coeffs: Vec::new(),
    };
    for m_row in m.iter() {
        let mut row: Vec<(F, usize)> = Vec::new();
        for (col_i, value) in m_row.iter().enumerate() {
            if !value.is_zero() {
                row.push((*value, col_i));
            }
        }
        r.coeffs.push(row);
    }
    r
}

pub fn vec_add<F: PrimeField>(a: &[F], b: &[F]) -> Result<Vec<F>, Error> {
    if a.len() != b.len() {
        return Err(Error::NotSameLength(
            "a.len()".to_string(),
            a.len(),
            "b.len()".to_string(),
            b.len(),
        ));
    }
    Ok(a.iter().zip(b.iter()).map(|(x, y)| *x + y).collect())
}

pub fn vec_sub<F: PrimeField>(a: &[F], b: &[F]) -> Result<Vec<F>, Error> {
    if a.len() != b.len() {
        return Err(Error::NotSameLength(
            "a.len()".to_string(),
            a.len(),
            "b.len()".to_string(),
            b.len(),
        ));
    }
    Ok(a.iter().zip(b.iter()).map(|(x, y)| *x - y).collect())
}

pub fn vec_scalar_mul<F: PrimeField>(vec: &[F], c: &F) -> Vec<F> {
    vec.iter().map(|a| *a * c).collect()
}

pub fn is_zero_vec<F: PrimeField>(vec: &[F]) -> bool {
    vec.iter().all(|a| a.is_zero())
}

pub fn mat_vec_mul<F: PrimeField>(M: &[Vec<F>], z: &[F]) -> Result<Vec<F>, Error> {
    if M.is_empty() {
        return Err(Error::Empty);
    }
    if M[0].len() != z.len() {
        return Err(Error::NotSameLength(
            "M[0].len()".to_string(),
            M[0].len(),
            "z.len()".to_string(),
            z.len(),
        ));
    }

    let mut r: Vec<F> = vec![F::zero(); M.len()];
    for (i, M_i) in M.iter().enumerate() {
        for (j, M_ij) in M_i.iter().enumerate() {
            r[i] += *M_ij * z[j];
        }
    }
    Ok(r)
}

pub fn mat_vec_mul_sparse<F: PrimeField>(M: &SparseMatrix<F>, z: &[F]) -> Result<Vec<F>, Error> {
    if M.n_cols != z.len() {
        return Err(Error::NotSameLength(
            "M.n_cols".to_string(),
            M.n_cols,
            "z.len()".to_string(),
            z.len(),
        ));
    }
    let mut res = vec![F::zero(); M.n_rows];
    for (row_i, row) in M.coeffs.iter().enumerate() {
        for &(value, col_i) in row.iter() {
            res[row_i] += value * z[col_i];
        }
    }
    Ok(res)
}

pub fn hadamard<F: PrimeField>(a: &[F], b: &[F]) -> Result<Vec<F>, Error> {
    if a.len() != b.len() {
        return Err(Error::NotSameLength(
            "a.len()".to_string(),
            a.len(),
            "b.len()".to_string(),
            b.len(),
        ));
    }
    Ok(cfg_iter!(a).zip(b).map(|(a, b)| *a * b).collect())
}

/// returns the interpolated polynomial of degree=v.len().next_power_of_two(), which passes through all
/// the given elements of v.
pub fn poly_from_vec<F: PrimeField>(v: Vec<F>) -> Result<DensePolynomial<F>, Error> {
    let D = GeneralEvaluationDomain::<F>::new(v.len()).ok_or(Error::NewDomainFail)?;
    Ok(Evaluations::from_vec_and_domain(v, D).interpolate())
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use ark_pallas::Fr;

    pub fn to_F_matrix<F: PrimeField>(M: Vec<Vec<usize>>) -> SparseMatrix<F> {
        dense_matrix_to_sparse(to_F_dense_matrix(M))
    }
    pub fn to_F_dense_matrix<F: PrimeField>(M: Vec<Vec<usize>>) -> Vec<Vec<F>> {
        M.iter()
            .map(|m| m.iter().map(|r| F::from(*r as u64)).collect())
            .collect()
    }
    pub fn to_F_vec<F: PrimeField>(z: Vec<usize>) -> Vec<F> {
        z.iter().map(|c| F::from(*c as u64)).collect()
    }

    #[test]
    fn test_dense_sparse_conversions() {
        let A = to_F_dense_matrix::<Fr>(vec![
            vec![0, 1, 0, 0, 0, 0],
            vec![0, 0, 0, 1, 0, 0],
            vec![0, 1, 0, 0, 1, 0],
            vec![5, 0, 0, 0, 0, 1],
        ]);
        let A_sparse = dense_matrix_to_sparse(A.clone());
        assert_eq!(A_sparse.to_dense(), A);
    }

    // test mat_vec_mul & mat_vec_mul_sparse
    #[test]
    fn test_mat_vec_mul() {
        let A = to_F_matrix::<Fr>(vec![
            vec![0, 1, 0, 0, 0, 0],
            vec![0, 0, 0, 1, 0, 0],
            vec![0, 1, 0, 0, 1, 0],
            vec![5, 0, 0, 0, 0, 1],
        ])
        .to_dense();
        let z = to_F_vec(vec![1, 3, 35, 9, 27, 30]);
        assert_eq!(mat_vec_mul(&A, &z).unwrap(), to_F_vec(vec![3, 9, 30, 35]));
        assert_eq!(
            mat_vec_mul_sparse(&dense_matrix_to_sparse(A), &z).unwrap(),
            to_F_vec(vec![3, 9, 30, 35])
        );

        let A = to_F_matrix::<Fr>(vec![vec![2, 3, 4, 5], vec![4, 8, 12, 14], vec![9, 8, 7, 6]]);
        let v = to_F_vec(vec![19, 55, 50, 3]);

        assert_eq!(
            mat_vec_mul(&A.to_dense(), &v).unwrap(),
            to_F_vec(vec![418, 1158, 979])
        );
        assert_eq!(
            mat_vec_mul_sparse(&A, &v).unwrap(),
            to_F_vec(vec![418, 1158, 979])
        );
    }

    #[test]
    fn test_hadamard_product() {
        let a = to_F_vec::<Fr>(vec![1, 2, 3, 4, 5, 6]);
        let b = to_F_vec(vec![7, 8, 9, 10, 11, 12]);
        assert_eq!(
            hadamard(&a, &b).unwrap(),
            to_F_vec(vec![7, 16, 27, 40, 55, 72])
        );
    }

    #[test]
    fn test_vec_add() {
        let a: Vec<Fr> = to_F_vec::<Fr>(vec![1, 2, 3, 4, 5, 6]);
        let b: Vec<Fr> = to_F_vec(vec![7, 8, 9, 10, 11, 12]);
        assert_eq!(
            vec_add(&a, &b).unwrap(),
            to_F_vec(vec![8, 10, 12, 14, 16, 18])
        );
    }
}
