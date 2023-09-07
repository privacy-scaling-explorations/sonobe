use ark_ff::PrimeField;
pub use ark_relations::r1cs::Matrix as R1CSMatrix;
use ark_std::cfg_iter;
use rayon::iter::{IndexedParallelIterator, IntoParallelRefIterator, ParallelIterator};

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

pub fn vec_add<F: PrimeField>(a: &[F], b: &[F]) -> Vec<F> {
    assert_eq!(a.len(), b.len());
    let mut r: Vec<F> = vec![F::zero(); a.len()];
    for i in 0..a.len() {
        r[i] = a[i] + b[i];
    }
    r
}

pub fn vec_sub<F: PrimeField>(a: &[F], b: &[F]) -> Vec<F> {
    assert_eq!(a.len(), b.len());
    let mut r: Vec<F> = vec![F::zero(); a.len()];
    for i in 0..a.len() {
        r[i] = a[i] - b[i];
    }
    r
}

pub fn vec_scalar_mul<F: PrimeField>(vec: &[F], c: &F) -> Vec<F> {
    let mut result = vec![F::zero(); vec.len()];
    for (i, a) in vec.iter().enumerate() {
        result[i] = *a * c;
    }
    result
}

pub fn is_zero_vec<F: PrimeField>(vec: &[F]) -> bool {
    for e in vec {
        if !e.is_zero() {
            return false;
        }
    }
    true
}

pub fn mat_vec_mul<F: PrimeField>(M: &Vec<Vec<F>>, z: &[F]) -> Vec<F> {
    assert!(!M.is_empty());
    assert_eq!(M[0].len(), z.len());

    let mut r: Vec<F> = vec![F::zero(); M.len()];
    for (i, M_i) in M.iter().enumerate() {
        for (j, M_ij) in M_i.iter().enumerate() {
            r[i] += *M_ij * z[j];
        }
    }
    r
}

pub fn mat_vec_mul_sparse<F: PrimeField>(matrix: &SparseMatrix<F>, vector: &[F]) -> Vec<F> {
    let mut res = vec![F::zero(); matrix.n_rows];
    for (row_i, row) in matrix.coeffs.iter().enumerate() {
        for &(value, col_i) in row.iter() {
            res[row_i] += value * vector[col_i];
        }
    }

    res
}

pub fn hadamard<F: PrimeField>(a: &[F], b: &[F]) -> Vec<F> {
    assert_eq!(a.len(), b.len());
    cfg_iter!(a).zip(b).map(|(a, b)| *a * b).collect()
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use ark_pallas::Fr;

    pub fn to_F_matrix<F: PrimeField>(M: Vec<Vec<usize>>) -> Vec<Vec<F>> {
        let mut R: Vec<Vec<F>> = vec![Vec::new(); M.len()];
        for i in 0..M.len() {
            R[i] = vec![F::zero(); M[i].len()];
            for j in 0..M[i].len() {
                R[i][j] = F::from(M[i][j] as u64);
            }
        }
        R
    }
    pub fn to_F_vec<F: PrimeField>(z: Vec<usize>) -> Vec<F> {
        let mut r: Vec<F> = vec![F::zero(); z.len()];
        for i in 0..z.len() {
            r[i] = F::from(z[i] as u64);
        }
        r
    }

    #[test]
    fn test_dense_sparse_conversions() {
        let A = to_F_matrix::<Fr>(vec![
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
        ]);
        let z = to_F_vec(vec![1, 3, 35, 9, 27, 30]);
        assert_eq!(mat_vec_mul(&A, &z), to_F_vec(vec![3, 9, 30, 35]));
        assert_eq!(
            mat_vec_mul_sparse(&dense_matrix_to_sparse(A), &z),
            to_F_vec(vec![3, 9, 30, 35])
        );

        let A = to_F_matrix::<Fr>(vec![vec![2, 3, 4, 5], vec![4, 8, 12, 14], vec![9, 8, 7, 6]]);
        let v = to_F_vec(vec![19, 55, 50, 3]);

        assert_eq!(mat_vec_mul(&A, &v), to_F_vec(vec![418, 1158, 979]));
        assert_eq!(
            mat_vec_mul_sparse(&dense_matrix_to_sparse(A), &v),
            to_F_vec(vec![418, 1158, 979])
        );
    }

    #[test]
    fn test_hadamard_product() {
        let a = to_F_vec::<Fr>(vec![1, 2, 3, 4, 5, 6]);
        let b = to_F_vec(vec![7, 8, 9, 10, 11, 12]);
        assert_eq!(hadamard(&a, &b), to_F_vec(vec![7, 16, 27, 40, 55, 72]));
    }
    #[test]
    fn test_vec_add() {
        let a: Vec<Fr> = to_F_vec::<Fr>(vec![1, 2, 3, 4, 5, 6]);
        let b: Vec<Fr> = to_F_vec(vec![7, 8, 9, 10, 11, 12]);
        assert_eq!(vec_add(&a, &b), to_F_vec(vec![8, 10, 12, 14, 16, 18]));
    }
}
