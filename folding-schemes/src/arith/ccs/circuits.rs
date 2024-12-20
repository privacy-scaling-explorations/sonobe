//! Circuit implementations for Customizable Constraint Systems (CCS).
//!
//! This module provides the circuit (gadget) variants of CCS components for use in
//! constraint system implementations. These are used when CCS operations need to
//! be performed inside another constraint system.

use super::CCS;
use crate::utils::gadgets::SparseMatrixVar;
use ark_ff::PrimeField;
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    fields::fp::FpVar,
};
use ark_relations::r1cs::{Namespace, SynthesisError};
use ark_std::borrow::Borrow;

/// [`CCSMatricesVar`] contains the matrices 'M' of the CCS without the rest of CCS parameters.
#[derive(Debug, Clone)]
pub struct CCSMatricesVar<F: PrimeField> {
    /// Vector of sparse matrices in their circuit representation
    /// We only need native representation, so the constraint field equals F
    pub M: Vec<SparseMatrixVar<FpVar<F>>>,
}

impl<F: PrimeField> AllocVar<CCS<F>, F> for CCSMatricesVar<F> {
    fn new_variable<T: Borrow<CCS<F>>>(
        cs: impl Into<Namespace<F>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        _mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|val| {
            let cs = cs.into();
            let M: Vec<SparseMatrixVar<FpVar<F>>> = val
                .borrow()
                .M
                .iter()
                .map(|M| SparseMatrixVar::<FpVar<F>>::new_constant(cs.clone(), M.clone()))
                .collect::<Result<_, SynthesisError>>()?;
            Ok(Self { M })
        })
    }
}
