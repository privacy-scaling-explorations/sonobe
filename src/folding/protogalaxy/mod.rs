/// Implements the scheme described in [ProtoGalaxy](https://eprint.iacr.org/2023/1106.pdf)
use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use thiserror::Error;

pub mod folding;
pub mod traits;
pub(crate) mod utils;

#[derive(Clone, Debug)]
pub struct CommittedInstance<C: CurveGroup> {
    phi: C,
    betas: Vec<C::ScalarField>,
    e: C::ScalarField,
}

#[derive(Clone, Debug)]
pub struct Witness<F: PrimeField> {
    w: Vec<F>,
    r_w: F,
}

#[derive(Debug, Error, PartialEq)]
pub enum ProtoGalaxyError {
    #[error("The remainder from G(X)-F(α)*L_0(X)) / Z(X) should be zero")]
    RemainderNotZero,
    #[error("Could not divide by vanishing polynomial")]
    CouldNotDivideByVanishing,
    #[error("The number of incoming instances + 1 should be a power of two, current number of instances: {0}")]
    WrongNumInstances(usize),
}
