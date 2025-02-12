use ark_crypto_primitives::sponge::CryptographicSponge;
use ark_ff::{batch_inversion, PrimeField};
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::{
    lc,
    r1cs::{ConstraintSystem, LinearCombination, SynthesisError, Variable},
};

use crate::{
    folding::circuits::{nonnative::affine::NonNativeAffineVar, CF1},
    transcript::{Transcript, TranscriptVar},
    Curve,
};

use super::alloc::{ArkCacheCast, LookupTable, Multiplicity, Query};

/// [`LogUp`] implements the checks for the set inclusion identity described in
/// [the LogUp paper](https://eprint.iacr.org/2022/1530.pdf).
///
/// Specifically, as per Lemma 5 of LogUp, all the queries $(q_1, ..., q_N)$ are
/// in the lookup table $(t_1, ..., t_M)$ (i.e., $\{ q_i \} \subseteq \{ t_j \}$
/// by removing duplicates in $(q_1, ..., q_N)$) if and only if there exists a
/// vector of multiplicities $(m_1, ..., m_M)$, such that:
/// $\sum_{i=1}^{N} \frac{1}{X - q_i} = \sum_{j=1}^{M} \frac{m_j}{X - t_j}$.
///
/// By the Schwartz-Zippel lemma, we can check the identity by evaluating at a
/// random point $c$, which can be computed as the Fiat-Shamir challenge.
///
/// Note that the LogUp paper further provides a dedicated protocol for checking
/// the identity, while in this implementation, the identity is encoded as an
/// arithmetic circuit, whose satisfiability is guaranteed by a SNARK.
pub struct LogUp;

impl LogUp {
    /// Computes the challenge $c$ for the set inclusion identity.
    pub fn challenge<C: Curve, T: Transcript<CF1<C>>>(sponge: &T, cm: &C) -> CF1<C> {
        let mut sponge = sponge.clone();
        sponge.absorb_nonnative(cm);
        sponge.get_challenge()
    }

    pub fn challenge_gadget<C: Curve, S: CryptographicSponge, T: TranscriptVar<CF1<C>, S>>(
        sponge: &T,
        cm: &NonNativeAffineVar<C>,
    ) -> Result<FpVar<CF1<C>>, SynthesisError> {
        let mut sponge = sponge.clone();
        sponge.absorb_nonnative(cm)?;
        sponge.get_challenge()
    }

    /// Generates constraints for checking the set inclusion identity at random
    /// point $c$.
    pub fn generate_verification_constraints<F: PrimeField>(
        cs: &mut ConstraintSystem<F>,
        c: F,
    ) -> Result<(), SynthesisError> {
        // Return early if the lookup table is not initialized, i.e., lookup
        // argument is unnecessary for the user.
        // Wrapped in a block to make the borrow checker happy.
        {
            let cache = cs.cache_map.borrow();
            if cache.get_as::<LookupTable, Vec<F>>().is_none() {
                return Ok(());
            }
        }
        let c = cs.new_input_variable(|| Ok(c))?;

        let lhs = Self::compute_lhs(cs, c)?;
        let rhs = Self::compute_rhs(cs, c)?;

        cs.enforce_constraint(lhs, Variable::One.into(), rhs)?;

        Ok(())
    }

    /// Computes the left-hand side of the set inclusion identity, i.e.,
    /// $\sum_{i=1}^{N} \frac{1}{X - q_i}$.
    fn compute_lhs<F: PrimeField>(
        cs: &mut ConstraintSystem<F>,
        c: Variable,
    ) -> Result<LinearCombination<F>, SynthesisError> {
        // Wrapped in a block to make the borrow checker happy.
        let (a_lcs, summand_values) = {
            let cache = cs.cache_map.borrow();
            let queries = cache
                .get_as::<Query, Vec<usize>>()
                .ok_or(SynthesisError::AssignmentMissing)?;

            let summands = if cs.is_in_setup_mode() {
                vec![F::zero(); queries.len()]
            } else {
                let c_value = cs
                    .assigned_value(c)
                    .ok_or(SynthesisError::AssignmentMissing)?;
                let mut inverses = queries
                    .iter()
                    .map(|&query| Ok(c_value - cs.witness_assignment[query]))
                    .collect::<Result<Vec<_>, _>>()?;
                // Compute inverses in batch for better performance.
                batch_inversion(&mut inverses);
                inverses
            };

            (
                queries
                    .iter()
                    .map(|&query| lc!() + c - Variable::Witness(query))
                    .collect::<Vec<_>>(),
                summands,
            )
        };

        let mut sum = lc!();
        for (a_lc, summand_value) in a_lcs.into_iter().zip(summand_values) {
            let summand_variable = cs.new_witness_variable(|| Ok(summand_value))?;
            sum = sum + summand_variable;
            cs.enforce_constraint(a_lc, summand_variable.into(), Variable::One.into())?;
        }

        Ok(sum)
    }

    /// Computes the right-hand side of the set inclusion identity, i.e.,
    /// $\sum_{j=1}^{M} \frac{m_j}{X - t_j}$.
    fn compute_rhs<F: PrimeField>(
        cs: &mut ConstraintSystem<F>,
        c: Variable,
    ) -> Result<LinearCombination<F>, SynthesisError> {
        // Wrapped in a block to make the borrow checker happy.
        let (a_lcs, c_lcs, summand_values) = {
            let cache = cs.cache_map.borrow();
            let table = cache
                .get_as::<LookupTable, Vec<F>>()
                .ok_or(SynthesisError::AssignmentMissing)?;
            let multiplicities = cache
                .get_as::<Multiplicity, Vec<usize>>()
                .ok_or(SynthesisError::AssignmentMissing)?;

            let summands = if cs.is_in_setup_mode() {
                vec![F::zero(); table.len()]
            } else {
                let c_value = cs
                    .assigned_value(c)
                    .ok_or(SynthesisError::AssignmentMissing)?;
                let mut inverses = table.iter().map(|i| c_value - i).collect::<Vec<_>>();
                // Compute inverses in batch for better performance.
                batch_inversion(&mut inverses);
                inverses
                    .into_iter()
                    .zip(multiplicities)
                    .map(|(inverse, &multiplicity)| {
                        Ok(inverse * cs.witness_assignment[multiplicity])
                    })
                    .collect::<Result<Vec<_>, _>>()?
            };

            (
                table
                    .iter()
                    .map(|&entry| lc!() + c - (entry, Variable::One))
                    .collect::<Vec<_>>(),
                multiplicities
                    .iter()
                    .map(|&m| Variable::Witness(m).into())
                    .collect::<Vec<_>>(),
                summands,
            )
        };

        let mut sum = lc!();
        for ((a_lc, c_lc), summand_value) in a_lcs.into_iter().zip(c_lcs).zip(summand_values) {
            let summand_variable = cs.new_witness_variable(|| Ok(summand_value))?;
            sum = sum + summand_variable;
            cs.enforce_constraint(a_lc, summand_variable.into(), c_lc)?;
        }

        Ok(sum)
    }
}
