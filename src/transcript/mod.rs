use crate::Error;
use ark_ec::{CurveGroup, Group};
use ark_serialize::CanonicalSerialize;
use ark_std::fmt::Debug;

pub mod poseidon;

pub trait Transcript<C: CurveGroup> {
    type TranscriptConfig: Debug;

    fn new(config: &Self::TranscriptConfig) -> Self;
    fn absorb(&mut self, v: &C::ScalarField);
    fn absorb_vec(&mut self, v: &[C::ScalarField]);
    fn absorb_point(&mut self, v: &C) -> Result<(), Error>;
    fn get_challenge(&mut self) -> C::ScalarField;
    /// get_challenge_nbits returns a field element of size nbits
    fn get_challenge_nbits(&mut self, nbits: usize) -> Vec<bool>;
    fn get_challenges(&mut self, n: usize) -> Vec<C::ScalarField>;
}

/// A (temporary) extension trait to the Transcript trait
pub trait TranscriptWithAppendableMessagesExt<C: CurveGroup> {
    fn append_serializable_element<S: CanonicalSerialize>(&mut self, label: &'static [u8], group_elem: &S);
    fn get_and_append_challenge(&mut self, label: &'static [u8]) -> <C as Group>::ScalarField;
}