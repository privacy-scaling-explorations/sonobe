use crate::commitment::CommitmentScheme;
use crate::folding::nova::{CommittedInstance, Witness};
use crate::RngCore;
use ark_crypto_primitives::sponge::Absorb;
use ark_ec::{CurveGroup, Group};
use ark_ff::PrimeField;
use ark_relations::r1cs::ConstraintSystem;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::rand::Rng;

use super::Arith;
use crate::Error;

#[derive(Debug, Clone, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct PlonkArith<F: PrimeField> {
    // Ammount of rows of the circuit
    rows: usize,
    // Number of witness wires
    wit_wires: usize,
    // Number of selector wires
    sel_wires: usize,
    // Each constraint, contains 3 selectors (q_m, q_l, q_r).
    constraints: Vec<[F; 3]>,
}

impl<F: PrimeField> Arith<F> for PlonkArith<F> {
    /// check that a plonk structure is satisfied by a z vector. Only for testing.
    fn check_relation(&self, z: &[F]) -> Result<(), Error> {
        let all_pass = self
            .constraints
            .iter()
            .copied()
            .zip(z.chunks_exact(self.wit_wires))
            .map(|([q_m, q_l, q_r], witness)| {
                q_m * (witness[0] * witness[1]) + q_l * witness[0] + q_r * witness[1] - witness[2]
            })
            .fold(true, |acc, res| acc && res.is_zero());

        if all_pass {
            Ok(())
        } else {
            Err(Error::NotSatisfied)
        }
    }

    fn params_to_le_bytes(&self) -> Vec<u8> {
        [
            self.rows.to_le_bytes(),
            self.wit_wires.to_le_bytes(),
            self.sel_wires.to_le_bytes(),
        ]
        .concat()
    }
}

impl<F: PrimeField> PlonkArith<F> {
    /// Generates a set of dummy constraints to be used for testing.
    pub(crate) fn generate_dummy_constraints(rows: usize) -> (PlonkArith<F>, Vec<[F; 3]>) {
        (
            PlonkArith {
                rows,
                wit_wires: 3,
                sel_wires: 3,
                constraints: vec![[F::zero(), F::one(), F::one()]; rows],
            },
            vec![[F::ONE, F::ONE, F::ONE + F::ONE]; rows],
        )
    }
}
