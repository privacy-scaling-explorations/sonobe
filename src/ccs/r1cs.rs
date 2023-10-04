use ark_ff::PrimeField;

use crate::utils::vec::*;
use crate::Error;

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

    /// check that a R1CS structure is satisfied by a z vector. Only for testing.
    pub fn check_relation(&self, z: &[F]) -> Result<(), Error> {
        let Az = mat_vec_mul_sparse(&self.A, z);
        let Bz = mat_vec_mul_sparse(&self.B, z);
        let Cz = mat_vec_mul_sparse(&self.C, z);
        let AzBz = hadamard(&Az, &Bz)?;
        if AzBz != Cz {
            return Err(Error::NotSatisfied);
        }

        Ok(())
    }

    /// converts the R1CS instance into a RelaxedR1CS as described in
    /// [Nova](https://eprint.iacr.org/2021/370.pdf) section 4.1.
    pub fn relax(self) -> RelaxedR1CS<F> {
        RelaxedR1CS::<F> {
            l: self.l,
            E: vec![F::zero(); self.A.n_rows],
            A: self.A,
            B: self.B,
            C: self.C,
            u: F::one(),
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct RelaxedR1CS<F: PrimeField> {
    pub l: usize, // io len
    pub A: SparseMatrix<F>,
    pub B: SparseMatrix<F>,
    pub C: SparseMatrix<F>,
    pub u: F,
    pub E: Vec<F>,
}
impl<F: PrimeField> RelaxedR1CS<F> {
    /// check that a RelaxedR1CS structure is satisfied by a z vector. Only for testing.
    pub fn check_relation(&self, z: &[F]) -> Result<(), Error> {
        let Az = mat_vec_mul_sparse(&self.A, z);
        let Bz = mat_vec_mul_sparse(&self.B, z);
        let Cz = mat_vec_mul_sparse(&self.C, z);
        let uCz = vec_scalar_mul(&Cz, &self.u);
        let uCzE = vec_add(&uCz, &self.E);
        let AzBz = hadamard(&Az, &Bz);
        if AzBz != uCzE {
            return Err(Error::NotSatisfied);
        }

        Ok(())
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::utils::vec::tests::{to_F_matrix, to_F_vec};
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

    #[test]
    fn test_check_relation() {
        let r1cs = get_test_r1cs::<Fr>();
        let z = get_test_z(5);
        r1cs.check_relation(&z).unwrap();
        r1cs.relax().check_relation(&z).unwrap();
    }
}
