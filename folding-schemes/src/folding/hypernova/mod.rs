/// Implements the scheme described in [HyperNova](https://eprint.iacr.org/2023/573.pdf)
use crate::ccs::CCS;
use ark_ff::PrimeField;

pub mod cccs;
pub mod circuits;
pub mod lcccs;
pub mod nimfs;
pub mod utils;

/// Witness for the LCCCS & CCCS, containing the w vector, and the r_w used as randomness in the Pedersen commitment.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Witness<F: PrimeField> {
    pub w: Vec<F>,
    pub r_w: F,
}

impl<F: PrimeField> Witness<F> {
    pub fn new(w: Vec<F>) -> Self {
        // note: at the current version, we don't use the blinding factors and we set them to 0
        // always.
        Self { w, r_w: F::zero() }
    }
    pub fn dummy(ccs: &CCS<F>) -> Self {
        Witness::<F>::new(vec![F::zero(); ccs.n - ccs.l - 1])
    }
}
