use ark_ff::PrimeField;
use ark_relations::r1cs::ConstraintSystem;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::rand::Rng;

use super::ccs::CCS;
use super::{Arith, ArithSerializer};
use crate::utils::vec::{
    hadamard, is_zero_vec, mat_vec_mul, vec_scalar_mul, vec_sub, SparseMatrix,
};
use crate::Error;

#[derive(Debug, Clone, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct R1CS<F: PrimeField> {
    pub l: usize, // io len
    pub A: SparseMatrix<F>,
    pub B: SparseMatrix<F>,
    pub C: SparseMatrix<F>,
}

impl<F: PrimeField> R1CS<F> {
    /// Evaluates the CCS relation at a given vector of variables `z`
    pub fn eval_at_z(&self, z: &[F]) -> Result<Vec<F>, Error> {
        if z.len() != self.A.n_cols {
            return Err(Error::NotSameLength(
                "z.len()".to_string(),
                z.len(),
                "number of variables in R1CS".to_string(),
                self.A.n_cols,
            ));
        }

        let Az = mat_vec_mul(&self.A, z)?;
        let Bz = mat_vec_mul(&self.B, z)?;
        let Cz = mat_vec_mul(&self.C, z)?;
        // Multiply Cz by z[0] (u) here, allowing this method to be reused for
        // both relaxed and plain R1CS.
        let uCz = vec_scalar_mul(&Cz, &z[0]);
        let AzBz = hadamard(&Az, &Bz)?;
        vec_sub(&AzBz, &uCz)
    }
}

impl<F: PrimeField, W: AsRef<[F]>, U: AsRef<[F]>> Arith<W, U> for R1CS<F> {
    type Evaluation = Vec<F>;

    fn eval_relation(&self, w: &W, u: &U) -> Result<Self::Evaluation, Error> {
        self.eval_at_z(&[&[F::one()], u.as_ref(), w.as_ref()].concat())
    }

    fn check_evaluation(_w: &W, _u: &U, e: Self::Evaluation) -> Result<(), Error> {
        is_zero_vec(&e).then_some(()).ok_or(Error::NotSatisfied)
    }
}

impl<F: PrimeField> ArithSerializer for R1CS<F> {
    fn params_to_le_bytes(&self) -> Vec<u8> {
        [
            self.l.to_le_bytes(),
            self.A.n_rows.to_le_bytes(),
            self.A.n_cols.to_le_bytes(),
        ]
        .concat()
    }
}

impl<F: PrimeField> R1CS<F> {
    pub fn empty() -> Self {
        R1CS {
            l: 0,
            A: SparseMatrix::empty(),
            B: SparseMatrix::empty(),
            C: SparseMatrix::empty(),
        }
    }
    pub fn rand<R: Rng>(rng: &mut R, n_rows: usize, n_cols: usize) -> Self {
        Self {
            l: 1,
            A: SparseMatrix::rand(rng, n_rows, n_cols),
            B: SparseMatrix::rand(rng, n_rows, n_cols),
            C: SparseMatrix::rand(rng, n_rows, n_cols),
        }
    }

    #[inline]
    pub fn num_constraints(&self) -> usize {
        self.A.n_rows
    }

    #[inline]
    pub fn num_public_inputs(&self) -> usize {
        self.l
    }

    #[inline]
    pub fn num_variables(&self) -> usize {
        self.A.n_cols
    }

    #[inline]
    pub fn num_witnesses(&self) -> usize {
        self.num_variables() - self.num_public_inputs() - 1
    }

    /// returns a tuple containing (w, x) (witness and public inputs respectively)
    pub fn split_z(&self, z: &[F]) -> (Vec<F>, Vec<F>) {
        (z[self.l + 1..].to_vec(), z[1..self.l + 1].to_vec())
    }
}

impl<F: PrimeField> From<CCS<F>> for R1CS<F> {
    fn from(ccs: CCS<F>) -> Self {
        R1CS::<F> {
            l: ccs.l,
            A: ccs.M[0].clone(),
            B: ccs.M[1].clone(),
            C: ccs.M[2].clone(),
        }
    }
}

/// extracts arkworks ConstraintSystem matrices into crate::utils::vec::SparseMatrix format as R1CS
/// struct.
pub fn extract_r1cs<F: PrimeField>(cs: &ConstraintSystem<F>) -> R1CS<F> {
    let m = cs.to_matrices().unwrap();

    let n_rows = cs.num_constraints;
    let n_cols = cs.num_instance_variables + cs.num_witness_variables; // cs.num_instance_variables already counts the 1

    let A = SparseMatrix::<F> {
        n_rows,
        n_cols,
        coeffs: m.a,
    };
    let B = SparseMatrix::<F> {
        n_rows,
        n_cols,
        coeffs: m.b,
    };
    let C = SparseMatrix::<F> {
        n_rows,
        n_cols,
        coeffs: m.c,
    };

    R1CS::<F> {
        l: cs.num_instance_variables - 1, // -1 to subtract the first '1'
        A,
        B,
        C,
    }
}

/// extracts the witness and the public inputs from arkworks ConstraintSystem.
pub fn extract_w_x<F: PrimeField>(cs: &ConstraintSystem<F>) -> (Vec<F>, Vec<F>) {
    (
        cs.witness_assignment.clone(),
        // skip the first element which is '1'
        cs.instance_assignment[1..].to_vec(),
    )
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::utils::vec::{
        is_zero_vec,
        tests::{to_F_matrix, to_F_vec},
    };

    use ark_pallas::Fr;

    pub fn get_test_r1cs<F: PrimeField>() -> R1CS<F> {
        // R1CS for: x^3 + x + 5 = y (example from article
        // https://www.vitalik.ca/general/2016/12/10/qap.html )
        let A = to_F_matrix::<F>(vec![
            vec![0, 1, 0, 0, 0, 0],
            vec![0, 0, 0, 1, 0, 0],
            vec![0, 1, 0, 0, 1, 0],
            vec![5, 0, 0, 0, 0, 1],
        ]);
        let B = to_F_matrix::<F>(vec![
            vec![0, 1, 0, 0, 0, 0],
            vec![0, 1, 0, 0, 0, 0],
            vec![1, 0, 0, 0, 0, 0],
            vec![1, 0, 0, 0, 0, 0],
        ]);
        let C = to_F_matrix::<F>(vec![
            vec![0, 0, 0, 1, 0, 0],
            vec![0, 0, 0, 0, 1, 0],
            vec![0, 0, 0, 0, 0, 1],
            vec![0, 0, 1, 0, 0, 0],
        ]);

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

    pub fn get_test_z_split<F: PrimeField>(input: usize) -> (F, Vec<F>, Vec<F>) {
        // z = (1, io, w)
        (
            F::one(),
            to_F_vec(vec![
                input, // io
            ]),
            to_F_vec(vec![
                input * input * input + input + 5, // x^3 + x + 5
                input * input,                     // x^2
                input * input * input,             // x^2 * x
                input * input * input + input,     // x^3 + x
            ]),
        )
    }

    #[test]
    fn test_eval_r1cs_relation() {
        let mut rng = ark_std::test_rng();
        let r1cs = get_test_r1cs::<Fr>();
        let (_, x, mut w) = get_test_z_split::<Fr>(rng.gen::<u16>() as usize);

        let f_w = r1cs.eval_relation(&w, &x).unwrap();
        assert!(is_zero_vec(&f_w));

        w[1] = Fr::from(111);
        let f_w = r1cs.eval_relation(&w, &x).unwrap();
        assert!(!is_zero_vec(&f_w));
    }

    #[test]
    fn test_check_r1cs_relation() {
        let r1cs = get_test_r1cs::<Fr>();
        let (_, x, w) = get_test_z_split(5);
        r1cs.check_relation(&w, &x).unwrap();
    }
}
