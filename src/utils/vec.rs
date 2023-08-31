use ark_ff::PrimeField;
use ark_std::cfg_iter;
use rayon::iter::{IndexedParallelIterator, IntoParallelRefIterator, ParallelIterator};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SparseMatrix<F: PrimeField> {
    pub n_rows: usize,
    pub n_cols: usize,
    pub coeffs: Vec<(usize, usize, F)>,
}

pub fn dense_matrix_to_sparse<F: PrimeField>(m: Vec<Vec<F>>) -> SparseMatrix<F> {
    let mut r = SparseMatrix::<F> {
        n_rows: m.len(),
        n_cols: m[0].len(),
        coeffs: Vec::new(),
    };
    for (i, m_i) in m.iter().enumerate() {
        for (j, m_ij) in m_i.iter().enumerate() {
            if !m_ij.is_zero() {
                r.coeffs.push((i, j, *m_ij));
            }
        }
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
    for &(row, col, value) in matrix.coeffs.iter() {
        res[row] += value * vector[col];
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
    use ark_bls12_377::Fr;

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
