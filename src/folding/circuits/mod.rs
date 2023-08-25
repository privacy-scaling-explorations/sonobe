/// Circuits and gadgets shared across the different folding schemes.
use ark_ec::CurveGroup;
use ark_ff::Field;

pub mod cyclefold;

pub type ConstraintF<C> = <<C as CurveGroup>::BaseField as Field>::BasePrimeField;
