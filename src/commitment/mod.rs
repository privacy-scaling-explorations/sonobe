use ark_ec::CurveGroup;
use ark_std::fmt::Debug;

use crate::transcript::Transcript;
use crate::Error;

pub mod kzg;
pub mod pedersen;

/// CommitmentProver defines the vector commitment scheme prover trait.
pub trait CommitmentProver<'a, C: CurveGroup> {
    type Params: Debug;
    type Proof: Debug;

    fn commit(
        params: &Self::Params,
        v: &[C::ScalarField],
        blind: &C::ScalarField,
    ) -> Result<C, Error>;
    fn prove(
        params: &Self::Params,
        transcript: &mut impl Transcript<C>,
        cm: &C,
        v: &[C::ScalarField],
        blind: &C::ScalarField,
    ) -> Result<Self::Proof, Error>;
}
