pub mod hypercube;
pub mod mle;
pub mod vec;
pub mod lagrange_poly;

// expose espresso local modules
pub mod espresso;
pub use crate::utils::espresso::multilinear_polynomial;
pub use crate::utils::espresso::sum_check;
pub use crate::utils::espresso::virtual_polynomial;
