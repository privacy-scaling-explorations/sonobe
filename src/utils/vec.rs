use ark_ff::PrimeField;
use ark_std::cfg_iter;

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
    let mut res = vec![F::zero(); matrix.n_cols];
    for &(row, col, value) in matrix.coeffs.iter() {
        res[row] += value * vector[col];
    }
    res
}

pub fn hadamard<F: PrimeField>(a: &[F], b: &[F]) -> Vec<F> {
    assert_eq!(a.len(), b.len());
    cfg_iter!(a).zip(b).map(|(a, b)| *a * b).collect()
}
