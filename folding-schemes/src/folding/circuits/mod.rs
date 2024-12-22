//! Circuit implementations and gadgets shared across different folding schemes.
//!
//! # Overview
//!
//! This module provides core circuit components used by various folding schemes including:
//!
//! - [`cyclefold`] - CycleFold circuit implementation that enables cross-curve folding operations
//! - [`decider`] - Decider circuits for verifying folding operations both on-chain and off-chain
//! - [`nonnative`] - Gadgets for working with non-native field arithmetic in circuits
//! - [`sum_check`] - Implementation of sum-check protocol circuits and gadgets
//! - [`utils`] - Common circuit utilities and helper gadgets
//!
//! # Type Aliases
//!
//! The module defines two important type aliases for working with constraint fields:
//!
//! - [`CF1`] - The constraint field used for the main folding circuit, using the scalar field of
//!   the main curve where folding occurs
//! - [`CF2`] - The constraint field used for the CycleFold circuit, using the base field which allows
//!   native representation of curve points
//!
//! # Architecture
//!
//! The circuits in this module are designed to be:
//!
//! - Reusable across different folding scheme implementations
//! - Composable to build more complex circuits
//! - Efficient by sharing common gadgets and optimizations
//!
//! Most circuits work with two curves in a cycle (C1, C2) where:
//! - C1 is the main curve whose scalar field is used for field operations
//! - C2 is the auxiliary curve used for commitments, with its base field matching C1's scalar field

/// Circuits and gadgets shared across the different folding schemes.
use ark_ec::{CurveGroup, PrimeGroup};
use ark_ff::Field;

pub mod cyclefold;
pub mod decider;
pub mod nonnative;
pub mod sum_check;
pub mod utils;

// TODO (autoparallel): nit -- I think the short variable names `CF1` and `CF2` could be made more clear by something
// like `ConstraintFieldPrimary` and `ConstraintFieldSecondary`, but this isn't a hill I'll die on

/// CF1 uses the ScalarField of the given C. CF1 represents the ConstraintField used for the main
/// folding circuit which is over E1::Fr, where E1 is the main curve where we do the folding.
/// In CF1, the points of C can not be natively represented.
pub type CF1<C> = <C as PrimeGroup>::ScalarField;
/// CF2 uses the BaseField of the given C. CF2 represents the ConstraintField used for the
/// CycleFold circuit which is over E2::Fr=E1::Fq, where E2 is the auxiliary curve (from
/// [CycleFold](https://eprint.iacr.org/2023/1192.pdf) approach) where we check the folding of the
/// commitments (elliptic curve points).
/// In CF2, the points of C can be natively represented.
pub type CF2<C> = <<C as CurveGroup>::BaseField as Field>::BasePrimeField;
