use ark_ec::CurveGroup;
use ark_std::fmt::Debug;

use crate::Error;

pub mod kzg;
pub mod pedersen;

/// CommitmentScheme defines a common trait for both polynomial commitment schemes and vector
/// commitment schemes, such as KZG and Pedersen commitments.
pub trait CommitmentScheme<C1: CurveGroup, C2: CurveGroup> {
    type Params: Debug;
    type Proof: Debug;

    fn setup() -> Self::Params;
    fn commit(params: Self::Params, v: Vec<C1::ScalarField>) -> C1;
    fn prove(params: Self::Params, v: Vec<C1::ScalarField>) -> Self::Proof;
    fn verify(params: Self::Params, cm: C1, proof: Self::Proof) -> Result<(), Error>;
}
