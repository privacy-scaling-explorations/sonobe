/// Circuits and gadgets shared across the different folding schemes.
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::Field;

pub mod cyclefold;
pub mod nonnative;
pub mod sum_check;
pub mod utils;

/// CF1 uses the ScalarField of the given C. CF1 represents the ConstraintField used for the main
/// folding circuit which is over E1::Fr, where E1 is the main curve where we do the folding.
/// In CF1, the points of C can not be natively represented.
pub type CF1<C> = <<C as CurveGroup>::Affine as AffineRepr>::ScalarField;
/// CF2 uses the BaseField of the given C. CF2 represents the ConstraintField used for the
/// CycleFold circuit which is over E2::Fr=E1::Fq, where E2 is the auxiliary curve (from
/// [CycleFold](https://eprint.iacr.org/2023/1192.pdf) approach) where we check the folding of the
/// commitments (elliptic curve points).
/// In CF2, the points of C can be natively represented.
pub type CF2<C> = <<C as CurveGroup>::BaseField as Field>::BasePrimeField;
