// code forked from
// https://github.com/EspressoSystems/hyperplonk/blob/main/arithmetic/src/multilinear_polynomial.rs
//
// Copyright (c) 2023 Espresso Systems (espressosys.com)
// This file is part of the HyperPlonk library.

// You should have received a copy of the MIT License
// along with the HyperPlonk library. If not, see <https://mit-license.org/>.

use ark_ff::Field;
#[cfg(feature = "parallel")]
use rayon::prelude::{IndexedParallelIterator, IntoParallelRefMutIterator, ParallelIterator};

pub use ark_poly::DenseMultilinearExtension;

pub fn fix_variables<F: Field>(
    poly: &DenseMultilinearExtension<F>,
    partial_point: &[F],
) -> DenseMultilinearExtension<F> {
    assert!(
        partial_point.len() <= poly.num_vars,
        "invalid size of partial point"
    );
    let nv = poly.num_vars;
    let mut poly = poly.evaluations.to_vec();
    let dim = partial_point.len();
    // evaluate single variable of partial point from left to right
    for (i, point) in partial_point.iter().enumerate().take(dim) {
        poly = fix_one_variable_helper(&poly, nv - i, point);
    }

    DenseMultilinearExtension::<F>::from_evaluations_slice(nv - dim, &poly[..(1 << (nv - dim))])
}

fn fix_one_variable_helper<F: Field>(data: &[F], nv: usize, point: &F) -> Vec<F> {
    let mut res = vec![F::zero(); 1 << (nv - 1)];

    // evaluate single variable of partial point from left to right
    #[cfg(not(feature = "parallel"))]
    for i in 0..(1 << (nv - 1)) {
        res[i] = data[i << 1] + (data[(i << 1) + 1] - data[i << 1]) * point;
    }

    #[cfg(feature = "parallel")]
    res.par_iter_mut().enumerate().for_each(|(i, x)| {
        *x = data[i << 1] + (data[(i << 1) + 1] - data[i << 1]) * point;
    });

    res
}

pub fn evaluate_no_par<F: Field>(poly: &DenseMultilinearExtension<F>, point: &[F]) -> F {
    assert_eq!(poly.num_vars, point.len());
    fix_variables_no_par(poly, point).evaluations[0]
}

fn fix_variables_no_par<F: Field>(
    poly: &DenseMultilinearExtension<F>,
    partial_point: &[F],
) -> DenseMultilinearExtension<F> {
    assert!(
        partial_point.len() <= poly.num_vars,
        "invalid size of partial point"
    );
    let nv = poly.num_vars;
    let mut poly = poly.evaluations.to_vec();
    let dim = partial_point.len();
    // evaluate single variable of partial point from left to right
    for i in 1..dim + 1 {
        let r = partial_point[i - 1];
        for b in 0..(1 << (nv - i)) {
            poly[b] = poly[b << 1] + (poly[(b << 1) + 1] - poly[b << 1]) * r;
        }
    }
    DenseMultilinearExtension::from_evaluations_slice(nv - dim, &poly[..(1 << (nv - dim))])
}

/// Given multilinear polynomial `p(x)` and s `s`, compute `s*p(x)`
pub fn scalar_mul<F: Field>(
    poly: &DenseMultilinearExtension<F>,
    s: &F,
) -> DenseMultilinearExtension<F> {
    DenseMultilinearExtension {
        evaluations: poly.evaluations.iter().map(|e| *e * s).collect(),
        num_vars: poly.num_vars,
    }
}

/// Test-only methods used in virtual_polynomial.rs
#[cfg(test)]
pub mod tests {
    use super::*;
    use ark_ff::PrimeField;
    use ark_std::rand::RngCore;
    use ark_std::{end_timer, start_timer};
    use std::sync::Arc;

    pub fn fix_last_variables<F: PrimeField>(
        poly: &DenseMultilinearExtension<F>,
        partial_point: &[F],
    ) -> DenseMultilinearExtension<F> {
        assert!(
            partial_point.len() <= poly.num_vars,
            "invalid size of partial point"
        );
        let nv = poly.num_vars;
        let mut poly = poly.evaluations.to_vec();
        let dim = partial_point.len();
        // evaluate single variable of partial point from left to right
        for (i, point) in partial_point.iter().rev().enumerate().take(dim) {
            poly = fix_last_variable_helper(&poly, nv - i, point);
        }

        DenseMultilinearExtension::<F>::from_evaluations_slice(nv - dim, &poly[..(1 << (nv - dim))])
    }

    fn fix_last_variable_helper<F: Field>(data: &[F], nv: usize, point: &F) -> Vec<F> {
        let half_len = 1 << (nv - 1);
        let mut res = vec![F::zero(); half_len];

        // evaluate single variable of partial point from left to right
        #[cfg(not(feature = "parallel"))]
        for b in 0..half_len {
            res[b] = data[b] + (data[b + half_len] - data[b]) * point;
        }

        #[cfg(feature = "parallel")]
        res.par_iter_mut().enumerate().for_each(|(i, x)| {
            *x = data[i] + (data[i + half_len] - data[i]) * point;
        });

        res
    }

    /// Sample a random list of multilinear polynomials.
    /// Returns
    /// - the list of polynomials,
    /// - its sum of polynomial evaluations over the boolean hypercube.
    #[cfg(test)]
    pub fn random_mle_list<F: PrimeField, R: RngCore>(
        nv: usize,
        degree: usize,
        rng: &mut R,
    ) -> (Vec<Arc<DenseMultilinearExtension<F>>>, F) {
        let start = start_timer!(|| "sample random mle list");
        let mut multiplicands = Vec::with_capacity(degree);
        for _ in 0..degree {
            multiplicands.push(Vec::with_capacity(1 << nv))
        }
        let mut sum = F::zero();

        for _ in 0..(1 << nv) {
            let mut product = F::one();

            for e in multiplicands.iter_mut() {
                let val = F::rand(rng);
                e.push(val);
                product *= val;
            }
            sum += product;
        }

        let list = multiplicands
            .into_iter()
            .map(|x| Arc::new(DenseMultilinearExtension::from_evaluations_vec(nv, x)))
            .collect();

        end_timer!(start);
        (list, sum)
    }

    // Build a randomize list of mle-s whose sum is zero.
    #[cfg(test)]
    pub fn random_zero_mle_list<F: PrimeField, R: RngCore>(
        nv: usize,
        degree: usize,
        rng: &mut R,
    ) -> Vec<Arc<DenseMultilinearExtension<F>>> {
        let start = start_timer!(|| "sample random zero mle list");

        let mut multiplicands = Vec::with_capacity(degree);
        for _ in 0..degree {
            multiplicands.push(Vec::with_capacity(1 << nv))
        }
        for _ in 0..(1 << nv) {
            multiplicands[0].push(F::zero());
            for e in multiplicands.iter_mut().skip(1) {
                e.push(F::rand(rng));
            }
        }

        let list = multiplicands
            .into_iter()
            .map(|x| Arc::new(DenseMultilinearExtension::from_evaluations_vec(nv, x)))
            .collect();

        end_timer!(start);
        list
    }
}
