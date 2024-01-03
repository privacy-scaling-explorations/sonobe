use ark_ff::PrimeField;
use ark_poly::{univariate::DensePolynomial, DenseUVPolynomial};

/// Computes the lagrange interpolated polynomial from the given points `p_i`
pub fn compute_lagrange_interpolated_poly<F: PrimeField>(p_i: &[F]) -> DensePolynomial<F> {
    // TODO: build domain directly from field, avoid explicit conversions within the loop

    // domain is 0..p_i.len(), to fit `interpolate_uni_poly` from hyperplonk
    let domain: Vec<usize> = (0..p_i.len()).collect();

    // compute l(x), common to every basis polynomial
    let mut l_x = DensePolynomial::from_coefficients_vec(vec![F::ONE]);
    for x_m in domain.clone() {
        let prod_m = DensePolynomial::from_coefficients_vec(vec![-F::from(x_m as u64), F::ONE]);
        l_x = &l_x * &prod_m;
    }

    // compute each w_j - barycentric weights
    let mut w_j_vector: Vec<F> = vec![];
    for x_j in domain.clone() {
        let mut w_j = F::ONE;
        for x_m in domain.clone() {
            if x_m != x_j {
                let prod = (F::from(x_j as u64) - F::from(x_m as u64))
                    .inverse()
                    .unwrap();
                w_j *= prod;
            }
        }
        w_j_vector.push(w_j);
    }

    // compute each polynomial within the sum L(x)
    let mut lagrange_poly = DensePolynomial::from_coefficients_vec(vec![F::ZERO]);
    for (j, w_j) in w_j_vector.iter().enumerate() {
        let x_j = domain[j];
        let y_j = p_i[j];
        // we multiply by l(x) here, otherwise the below division will not work - deg(0)/deg(d)
        let poly_numerator = &(&l_x * (*w_j)) * (y_j);
        let poly_denominator =
            DensePolynomial::from_coefficients_vec(vec![-F::from(x_j as u64), F::ONE]);
        let poly = &poly_numerator / &poly_denominator;
        lagrange_poly = &lagrange_poly + &poly;
    }

    lagrange_poly
}
