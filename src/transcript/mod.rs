use ark_ff::PrimeField;
use ark_std::fmt::Debug;

pub mod poseidon;

pub trait Transcript<F: PrimeField> {
    type TranscriptConfig: Debug;

    fn new(config: &Self::TranscriptConfig) -> Self;
    fn absorb(&mut self, v: &F);
    fn absorb_vec(&mut self, v: &[F]);
    fn get_challenge(&mut self) -> F;
    fn get_challenges(&mut self, n: usize) -> Vec<F>;
}
