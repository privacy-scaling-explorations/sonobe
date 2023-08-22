use ark_ec::CurveGroup;
use ark_std::fmt::Debug;

pub mod poseidon;

pub trait Transcript<C: CurveGroup> {
    type TranscriptConfig: Debug;

    fn new(config: &Self::TranscriptConfig) -> Self;
    fn absorb(&mut self, v: &C::ScalarField);
    fn absorb_vec(&mut self, v: &[C::ScalarField]);
    fn absorb_point(&mut self, v: &C);
    fn get_challenge(&mut self) -> C::ScalarField;
    fn get_challenges(&mut self, n: usize) -> Vec<C::ScalarField>;
}
