use ark_ff::PrimeField;

use crate::Error;

pub mod ccs;
pub mod r1cs;

pub trait Arith<F: PrimeField> {
    /// Evaluate the given Arith structure at `z`, a vector of assignments, and
    /// return the evaluation.
    fn eval_relation(&self, z: &[F]) -> Result<Vec<F>, Error>;

    /// Checks that the given Arith structure is satisfied by a z vector, i.e.,
    /// if the evaluation is a zero vector
    ///
    /// Used only for testing.
    fn check_relation(&self, z: &[F]) -> Result<(), Error> {
        if self.eval_relation(z)?.iter().all(|f| f.is_zero()) {
            Ok(())
        } else {
            Err(Error::NotSatisfied)
        }
    }

    /// Returns the bytes that represent the parameters, that is, the matrices sizes, the amount of
    /// public inputs, etc, without the matrices/polynomials values.
    fn params_to_le_bytes(&self) -> Vec<u8>;
}
