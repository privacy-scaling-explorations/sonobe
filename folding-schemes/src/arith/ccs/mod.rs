use ark_ff::PrimeField;
use ark_std::log2;

use crate::utils::vec::{
    hadamard, is_zero_vec, mat_vec_mul, vec_add, vec_scalar_mul, SparseMatrix,
};
use crate::Error;

use super::{r1cs::R1CS, ArithRelation};
use super::{Arith, ArithSerializer};

pub mod circuits;

/// CCS represents the Customizable Constraint Systems structure defined in
/// the [CCS paper](https://eprint.iacr.org/2023/552)
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct CCS<F: PrimeField> {
    /// m: number of rows in M_i (such that M_i \in F^{m, n})
    m: usize,
    /// n = |z|, number of cols in M_i
    n: usize,
    /// l = |io|, size of public input/output
    l: usize,
    /// t = |M|, number of matrices
    pub t: usize,
    /// q = |c| = |S|, number of multisets
    q: usize,
    /// d: max degree in each variable
    d: usize,
    /// s = log(m), dimension of x
    pub s: usize,

    /// vector of matrices
    pub M: Vec<SparseMatrix<F>>,
    /// vector of multisets
    pub S: Vec<Vec<usize>>,
    /// vector of coefficients
    pub c: Vec<F>,
}

impl<F: PrimeField> CCS<F> {
    /// Evaluates the CCS relation at a given vector of assignments `z`
    pub fn eval_at_z(&self, z: &[F]) -> Result<Vec<F>, Error> {
        let mut result = vec![F::zero(); self.m];

        for i in 0..self.q {
            // extract the needed M_j matrices out of S_i
            let vec_M_j: Vec<&SparseMatrix<F>> = self.S[i].iter().map(|j| &self.M[*j]).collect();

            // complete the hadamard chain
            let mut hadamard_result = vec![F::one(); self.m];
            for M_j in vec_M_j.into_iter() {
                hadamard_result = hadamard(&hadamard_result, &mat_vec_mul(M_j, z)?)?;
            }

            // multiply by the coefficient of this step
            let c_M_j_z = vec_scalar_mul(&hadamard_result, &self.c[i]);

            // add it to the final vector
            result = vec_add(&result, &c_M_j_z)?;
        }

        Ok(result)
    }
}

impl<F: PrimeField> Arith for CCS<F> {
    #[inline]
    fn degree(&self) -> usize {
        self.d
    }

    #[inline]
    fn n_constraints(&self) -> usize {
        self.m
    }

    #[inline]
    fn n_variables(&self) -> usize {
        self.n
    }

    #[inline]
    fn n_public_inputs(&self) -> usize {
        self.l
    }

    #[inline]
    fn n_witnesses(&self) -> usize {
        self.n_variables() - self.n_public_inputs() - 1
    }

    fn split_z<P: PrimeField>(&self, z: &[P]) -> (Vec<P>, Vec<P>) {
        (z[self.l + 1..].to_vec(), z[1..self.l + 1].to_vec())
    }
}

impl<F: PrimeField, W: AsRef<[F]>, U: AsRef<[F]>> ArithRelation<W, U> for CCS<F> {
    type Evaluation = Vec<F>;

    fn eval_relation(&self, w: &W, u: &U) -> Result<Self::Evaluation, Error> {
        self.eval_at_z(&[&[F::one()], u.as_ref(), w.as_ref()].concat())
    }

    fn check_evaluation(_w: &W, _u: &U, e: Self::Evaluation) -> Result<(), Error> {
        is_zero_vec(&e).then_some(()).ok_or(Error::NotSatisfied)
    }
}

impl<F: PrimeField> ArithSerializer for CCS<F> {
    fn params_to_le_bytes(&self) -> Vec<u8> {
        [
            self.l.to_le_bytes(),
            self.m.to_le_bytes(),
            self.n.to_le_bytes(),
            self.t.to_le_bytes(),
            self.q.to_le_bytes(),
            self.d.to_le_bytes(),
        ]
        .concat()
    }
}

impl<F: PrimeField> From<R1CS<F>> for CCS<F> {
    fn from(r1cs: R1CS<F>) -> Self {
        let m = r1cs.n_constraints();
        let n = r1cs.n_variables();
        CCS {
            m,
            n,
            l: r1cs.n_public_inputs(),
            s: log2(m) as usize,
            t: 3,
            q: 2,
            d: r1cs.degree(),

            S: vec![vec![0, 1], vec![2]],
            c: vec![F::one(), F::one().neg()],
            M: vec![r1cs.A, r1cs.B, r1cs.C],
        }
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::{
        arith::r1cs::tests::{get_test_r1cs, get_test_z as r1cs_get_test_z, get_test_z_split},
        utils::vec::is_zero_vec,
    };
    use ark_pallas::Fr;

    pub fn get_test_ccs<F: PrimeField>() -> CCS<F> {
        get_test_r1cs::<F>().into()
    }
    pub fn get_test_z<F: PrimeField>(input: usize) -> Vec<F> {
        r1cs_get_test_z(input)
    }

    #[test]
    fn test_eval_ccs_relation() -> Result<(), Error> {
        let ccs = get_test_ccs::<Fr>();
        let (_, x, mut w) = get_test_z_split(3);

        let f_w = ccs.eval_relation(&w, &x)?;
        assert!(is_zero_vec(&f_w));

        w[1] = Fr::from(111);
        let f_w = ccs.eval_relation(&w, &x)?;
        assert!(!is_zero_vec(&f_w));
        Ok(())
    }

    /// Test that a basic CCS relation can be satisfied
    #[test]
    fn test_check_ccs_relation() -> Result<(), Error> {
        let ccs = get_test_ccs::<Fr>();
        let (_, x, w) = get_test_z_split(3);

        ccs.check_relation(&w, &x)?;
        Ok(())
    }
}
