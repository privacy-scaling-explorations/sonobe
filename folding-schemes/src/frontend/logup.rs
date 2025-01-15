use ark_ff::{batch_inversion, PrimeField};
use ark_r1cs_std::{alloc::AllocVar, fields::fp::AllocatedFp};
use ark_relations::{
    lc,
    r1cs::{ConstraintSystemRef, LinearCombination, SynthesisError, Variable},
};
use ark_std::{any::TypeId, collections::HashMap, Zero};

use crate::{
    commitment::CommitmentScheme, folding::circuits::CF1, transcript::Transcript, Curve, Error,
};

use super::alloc::{ArkCacheCast, LookupTable, Multiplicity, Query};

pub struct LogUp;

impl LogUp {
    pub fn compute_multiplicities<F: PrimeField>(
        cs: ConstraintSystemRef<F>,
    ) -> Result<(), SynthesisError> {
        let mut cs = cs.borrow_mut().ok_or(SynthesisError::MissingCS)?;

        // Wrapped in a block to make the borrow checker happy.
        let multiplicity_values = {
            let cache = cs.cache_map.borrow();
            let table = match cache.get_as::<LookupTable, Vec<F>>() {
                Some(table) => table,
                None => return Ok(()),
            };
            let mut histo = table
                .iter()
                .map(|&entry| (entry, 0u64))
                .collect::<HashMap<_, _>>();
            let queries = cache
                .get_as::<Query, Vec<Variable>>()
                .ok_or(SynthesisError::AssignmentMissing)?;

            if !cs.is_in_setup_mode() {
                for &query in queries {
                    let assignment = cs
                        .assigned_value(query)
                        .ok_or(SynthesisError::AssignmentMissing)?;
                    histo
                        .get_mut(&assignment)
                        .map(|c| *c += 1)
                        .ok_or(SynthesisError::AssignmentMissing)?;
                }
            }

            table
                .iter()
                .map(|entry| F::from(histo[entry]))
                .collect::<Vec<_>>()
        };

        let multiplicity_variables = multiplicity_values
            .iter()
            .map(|&value| cs.new_witness_variable(|| Ok(value)))
            .collect::<Result<Vec<_>, _>>()?;

        let mut cache = cs.cache_map.borrow_mut();
        cache.insert(
            TypeId::of::<Multiplicity>(),
            Box::new(multiplicity_variables),
        );

        Ok(())
    }

    pub fn commit<C: Curve, CS: CommitmentScheme<C, H>, const H: bool>(
        cs: ConstraintSystemRef<CF1<C>>,
        pp: &CS::ProverParams,
    ) -> Result<C, Error> {
        let cs = cs.borrow().ok_or(SynthesisError::MissingCS)?;
        let cache = cs.cache_map.borrow();
        let queries = cache
            .get_as::<Query, Vec<Variable>>()
            .ok_or(SynthesisError::AssignmentMissing)?;
        let multiplicities = cache
            .get_as::<Multiplicity, Vec<Variable>>()
            .ok_or(SynthesisError::AssignmentMissing)?;

        CS::commit(
            pp,
            &queries
                .iter()
                .chain(multiplicities)
                .map(|&v| cs.assigned_value(v))
                .collect::<Option<Vec<_>>>()
                .ok_or(SynthesisError::AssignmentMissing)?,
            &CF1::<C>::zero(),
        )
    }

    pub fn challenge<C: Curve, H: Transcript<CF1<C>>>(sponge: &H, cm: &C) -> CF1<C> {
        let mut sponge = sponge.clone();
        sponge.absorb_nonnative(cm);
        sponge.get_challenge()
    }

    pub fn generate_verification_constraints<F: PrimeField>(
        cs: ConstraintSystemRef<F>,
        c: F,
    ) -> Result<(), SynthesisError> {
        // Return early if the lookup table is not initialized, i.e., lookup
        // argument is unnecessary for the user.
        // Wrapped in a block to make the borrow checker happy.
        {
            let cs = cs.borrow().ok_or(SynthesisError::MissingCS)?;
            let cache = cs.cache_map.borrow();
            if cache.get_as::<LookupTable, Vec<F>>().is_none() {
                return Ok(());
            }
        }
        // TODO: change this to `new_input`
        let c = AllocatedFp::new_witness(cs.clone(), || Ok(c))?;

        let lhs = Self::compute_lhs(cs.clone(), &c)?;
        let rhs = Self::compute_rhs(cs.clone(), &c)?;

        cs.enforce_constraint(lhs, Variable::One.into(), rhs)?;

        Ok(())
    }

    fn compute_lhs<F: PrimeField>(
        cs: ConstraintSystemRef<F>,
        c: &AllocatedFp<F>,
    ) -> Result<LinearCombination<F>, SynthesisError> {
        let mut cs = cs.borrow_mut().ok_or(SynthesisError::MissingCS)?;

        // Wrapped in a block to make the borrow checker happy.
        let (a_lcs, c_lcs, summand_values) = {
            let cache = cs.cache_map.borrow();
            let table = cache
                .get_as::<LookupTable, Vec<F>>()
                .ok_or(SynthesisError::AssignmentMissing)?;
            let multiplicities = cache
                .get_as::<Multiplicity, Vec<Variable>>()
                .ok_or(SynthesisError::AssignmentMissing)?;

            let summands = if cs.is_in_setup_mode() {
                vec![F::zero(); table.len()]
            } else {
                let c_value = cs
                    .assigned_value(c.variable)
                    .ok_or(SynthesisError::AssignmentMissing)?;
                let mut inverses = table.iter().map(|i| c_value - i).collect::<Vec<_>>();
                batch_inversion(&mut inverses);
                inverses
                    .into_iter()
                    .zip(multiplicities)
                    .map(|(inverse, &multiplicity)| {
                        Ok(inverse
                            * cs.assigned_value(multiplicity)
                                .ok_or(SynthesisError::AssignmentMissing)?)
                    })
                    .collect::<Result<Vec<_>, _>>()?
            };

            (
                table
                    .iter()
                    .map(|&entry| lc!() + c.variable - (entry, Variable::One))
                    .collect::<Vec<_>>(),
                multiplicities.iter().map(|&m| m.into()).collect::<Vec<_>>(),
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

    fn compute_rhs<F: PrimeField>(
        cs: ConstraintSystemRef<F>,
        c: &AllocatedFp<F>,
    ) -> Result<LinearCombination<F>, SynthesisError> {
        let mut cs = cs.borrow_mut().ok_or(SynthesisError::MissingCS)?;

        // Wrapped in a block to make the borrow checker happy.
        let (a_lcs, summand_values) = {
            let cache = cs.cache_map.borrow();
            let queries = cache
                .get_as::<Query, Vec<Variable>>()
                .ok_or(SynthesisError::AssignmentMissing)?;

            let summands = if cs.is_in_setup_mode() {
                vec![F::zero(); queries.len()]
            } else {
                let c_value = cs
                    .assigned_value(c.variable)
                    .ok_or(SynthesisError::AssignmentMissing)?;
                let mut inverses = queries
                    .iter()
                    .map(|&i| {
                        Ok(c_value
                            - cs.assigned_value(i)
                                .ok_or(SynthesisError::AssignmentMissing)?)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                batch_inversion(&mut inverses);
                inverses
            };

            (
                queries
                    .iter()
                    .map(|&query| lc!() + c.variable - query)
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
}
