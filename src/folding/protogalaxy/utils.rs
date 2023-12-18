use ark_ff::PrimeField;

// returns (b, b^2, b^4, ..., b^{2^{t-1}})
pub fn exponential_powers<F: PrimeField>(b: F, t: usize) -> Vec<F> {
    let mut r = vec![F::zero(); t];
    r[0] = b;
    for i in 1..t {
        r[i] = r[i - 1].square();
    }
    r
}
pub fn all_powers<F: PrimeField>(a: F, n: usize) -> Vec<F> {
    let mut r = vec![F::zero(); n];
    for (i, r_i) in r.iter_mut().enumerate() {
        *r_i = a.pow([i as u64]);
    }
    r
}

// returns a vector containing βᵢ* = βᵢ + α ⋅ δᵢ
pub fn betas_star<F: PrimeField>(betas: &[F], deltas: &[F], alpha: F) -> Vec<F> {
    betas
        .iter()
        .zip(
            deltas
                .iter()
                .map(|delta_i| alpha * delta_i)
                .collect::<Vec<F>>(),
        )
        .map(|(beta_i, delta_i_alpha)| *beta_i + delta_i_alpha)
        .collect()
}
