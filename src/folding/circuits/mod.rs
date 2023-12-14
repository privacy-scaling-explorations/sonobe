/// Circuits and gadgets shared across the different folding schemes.
use ark_ec::CurveGroup;
use ark_ff::Field;

pub mod cyclefold;
pub mod nonnative;
pub mod sum_check;

// CF represents the constraints field
pub type CF<C> = <<C as CurveGroup>::BaseField as Field>::BasePrimeField;
