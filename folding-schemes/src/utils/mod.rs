use ark_ff::PrimeField;

pub mod gadgets;
pub mod hypercube;
pub mod lagrange_poly;
pub mod mle;
pub mod vec;

// expose espresso local modules
pub mod espresso;
pub use crate::utils::espresso::multilinear_polynomial;
pub use crate::utils::espresso::sum_check;
pub use crate::utils::espresso::virtual_polynomial;

/// For a given x, returns [1, x^1, x^2, ..., x^n-1];
pub fn powers_of<F: PrimeField>(x: F, n: usize) -> Vec<F> {
    let mut c: Vec<F> = vec![F::zero(); n];
    c[0] = F::one();
    for i in 1..n {
        c[i] = c[i - 1] * x;
    }
    c
}
