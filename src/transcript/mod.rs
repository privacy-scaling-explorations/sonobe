use crate::Error;
use ark_ec::CurveGroup;
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