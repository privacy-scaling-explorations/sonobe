use ark_crypto_primitives::sponge::Absorb;
use ark_ec::{CurveGroup, Group};
use ark_ff::{One, PrimeField};
use ark_poly::univariate::DensePolynomial;
use ark_poly::{DenseMultilinearExtension, DenseUVPolynomial, Polynomial};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{log2, Zero};

use super::mova::{CommittedInstance, Witness};
use crate::transcript::Transcript;
use crate::utils::mle::dense_vec_to_dense_mle;
use crate::Error;

/// Implements the Points vs Line as described in
/// [Mova](https://eprint.iacr.org/2024/1220.pdf) and Section 4.5.2 from Thaler’s book

/// Claim from step 3 protocol 6
pub struct PointvsLineEvaluationClaim<C: CurveGroup> {
    pub mleE1_prime: C::ScalarField,
    pub mleE2_prime: C::ScalarField,
    pub rE_prime: Vec<C::ScalarField>,
}
/// Proof from step 1 protocol 6
#[derive(Debug, Clone, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct PointVsLineProof<C: CurveGroup> {
    pub h1: DensePolynomial<C::ScalarField>,
    pub h2: DensePolynomial<C::ScalarField>,
}

#[derive(Clone, Debug, Default)]
pub struct PointVsLine<C: CurveGroup, T: Transcript<C::ScalarField>> {
    _phantom_C: std::marker::PhantomData<C>,
    _phantom_T: std::marker::PhantomData<T>,
}

/// Protocol 6 from Mova
impl<C: CurveGroup, T: Transcript<C::ScalarField>> PointVsLine<C, T>
where
    <C as Group>::ScalarField: Absorb,
{
    pub fn prove(
        transcript: &mut T,
        ci1: &CommittedInstance<C>,
        ci2: &CommittedInstance<C>,
        w1: &Witness<C>,
        w2: &Witness<C>,
    ) -> Result<(PointVsLineProof<C>, PointvsLineEvaluationClaim<C>), Error> {
        let n_vars: usize = log2(w1.E.len()) as usize;

        let mleE1 = dense_vec_to_dense_mle(n_vars, &w1.E);
        let mleE2 = dense_vec_to_dense_mle(n_vars, &w2.E);

        // We have l(0) = r1, l(1) = r2 so we know that l(x) = r1 + x(r2-r1) thats why we need r2-r1
        let r1_sub_r2: Vec<<C>::ScalarField> = ci1
            .rE
            .iter()
            .zip(&ci2.rE)
            .map(|(&r1, r2)| r1 - r2)
            .collect();

        let h1 = compute_h(&mleE1, &ci1.rE, &r1_sub_r2)?;
        let h2 = compute_h(&mleE2, &ci1.rE, &r1_sub_r2)?;

        transcript.absorb(&h1.coeffs());
        transcript.absorb(&h2.coeffs());

        let beta_scalar = C::ScalarField::from_le_bytes_mod_order(b"beta");
        transcript.absorb(&beta_scalar);
        let beta = transcript.get_challenge();

        let mleE1_prime = h1.evaluate(&beta);
        let mleE2_prime = h2.evaluate(&beta);

        let rE_prime = compute_l(&ci1.rE, &r1_sub_r2, beta)?;

        Ok((
            PointVsLineProof { h1, h2 },
            PointvsLineEvaluationClaim {
                mleE1_prime,
                mleE2_prime,
                rE_prime,
            },
        ))
    }

    pub fn verify(
        transcript: &mut T,
        ci1: &CommittedInstance<C>,
        ci2: &CommittedInstance<C>,
        proof: &PointVsLineProof<C>,
        mleE1_prime: &<C>::ScalarField,
        mleE2_prime: &<C>::ScalarField,
    ) -> Result<
        Vec<<C>::ScalarField>, // rE=rE1'=rE2'.
        Error,
    > {
        if proof.h1.evaluate(&C::ScalarField::zero()) != ci1.mleE {
            return Err(Error::NotEqual);
        }

        if proof.h2.evaluate(&C::ScalarField::one()) != ci2.mleE {
            return Err(Error::NotEqual);
        }

        transcript.absorb(&proof.h1.coeffs());
        transcript.absorb(&proof.h2.coeffs());

        let beta_scalar = C::ScalarField::from_le_bytes_mod_order(b"beta");
        transcript.absorb(&beta_scalar);
        let beta = transcript.get_challenge();

        if *mleE1_prime != proof.h1.evaluate(&beta) {
            return Err(Error::NotEqual);
        }

        if *mleE2_prime != proof.h2.evaluate(&beta) {
            return Err(Error::NotEqual);
        }

        let r1_sub_r2: Vec<<C>::ScalarField> = ci1
            .rE
            .iter()
            .zip(&ci2.rE)
            .map(|(&r1, r2)| r1 - r2)
            .collect();
        let rE_prime = compute_l(&ci1.rE, &r1_sub_r2, beta)?;

        Ok(rE_prime)
    }
}

fn compute_h<F: PrimeField>(
    mle: &DenseMultilinearExtension<F>,
    r1: &[F],
    r1_sub_r2: &[F],
) -> Result<DensePolynomial<F>, Error> {
    let n_vars: usize = mle.num_vars;
    if r1.len() != r1_sub_r2.len() || r1.len() != n_vars {
        return Err(Error::NotEqual);
    }

    // Initialize the polynomial vector from the evaluations in the multilinear extension.
    // Each evaluation is turned into a constant polynomial.
    let mut poly: Vec<DensePolynomial<F>> = mle
        .evaluations
        .iter()
        .map(|&x| DensePolynomial::from_coefficients_slice(&[x]))
        .collect();

    for (i, (&r1_i, &r1_sub_r2_i)) in r1.iter().zip(r1_sub_r2.iter()).enumerate().take(n_vars) {
        // Create a linear polynomial r(X) = r1_i + (r1_sub_r2_i) * X (basically l)
        let r = DensePolynomial::from_coefficients_slice(&[r1_i, r1_sub_r2_i]);
        let half_len = 1 << (n_vars - i - 1);

        for b in 0..half_len {
            let left = &poly[b << 1];
            let right = &poly[(b << 1) + 1];
            poly[b] = left + &(&r * &(right - left));
        }
    }

    // After the loop, we should be left with a single polynomial, so return it.
    Ok(poly.swap_remove(0))
}

fn compute_l<F: PrimeField>(r1: &[F], r1_sub_r2: &[F], x: F) -> Result<Vec<F>, Error> {
    if r1.len() != r1_sub_r2.len() {
        return Err(Error::NotEqual);
    }

    // we have l(x) = r1 + x(r2-r1) so return the result
    Ok(r1
        .iter()
        .zip(r1_sub_r2)
        .map(|(&r1, &r1_sub_r0)| r1 + x * r1_sub_r0)
        .collect())
}

#[cfg(test)]
mod tests {
    use super::{compute_h, compute_l};
    use ark_pallas::Fq;
    use ark_poly::{DenseMultilinearExtension, DenseUVPolynomial};

    #[test]
    fn test_compute_h() {
        let mle = DenseMultilinearExtension::from_evaluations_slice(1, &[Fq::from(1), Fq::from(2)]);
        let r0 = [Fq::from(5)];
        let r1 = [Fq::from(6)];
        let r1_sub_r0: Vec<Fq> = r1.iter().zip(&r0).map(|(&x, y)| x - y).collect();

        let result = compute_h(&mle, &r0, &r1_sub_r0).unwrap();
        assert_eq!(
            result,
            DenseUVPolynomial::from_coefficients_slice(&[Fq::from(6), Fq::from(1)])
        );

        let mle = DenseMultilinearExtension::from_evaluations_slice(1, &[Fq::from(1), Fq::from(2)]);
        let r0 = [Fq::from(4)];
        let r1 = [Fq::from(7)];
        let r1_sub_r0: Vec<Fq> = r1.iter().zip(&r0).map(|(&x, y)| x - y).collect();

        let result = compute_h(&mle, &r0, &r1_sub_r0).unwrap();
        assert_eq!(
            result,
            DenseUVPolynomial::from_coefficients_slice(&[Fq::from(5), Fq::from(3)])
        );

        let mle = DenseMultilinearExtension::from_evaluations_slice(
            2,
            &[Fq::from(1), Fq::from(2), Fq::from(3), Fq::from(4)],
        );
        let r0 = [Fq::from(5), Fq::from(4)];
        let r1 = [Fq::from(2), Fq::from(7)];
        let r1_sub_r0: Vec<Fq> = r1.iter().zip(&r0).map(|(&x, y)| x - y).collect();

        let result = compute_h(&mle, &r0, &r1_sub_r0).unwrap();
        assert_eq!(
            result,
            DenseUVPolynomial::from_coefficients_slice(&[Fq::from(14), Fq::from(3)])
        );
        let mle = DenseMultilinearExtension::from_evaluations_slice(
            3,
            &[
                Fq::from(1),
                Fq::from(2),
                Fq::from(3),
                Fq::from(4),
                Fq::from(5),
                Fq::from(6),
                Fq::from(7),
                Fq::from(8),
            ],
        );
        let r0 = [Fq::from(1), Fq::from(2), Fq::from(3)];
        let r1 = [Fq::from(5), Fq::from(6), Fq::from(7)];
        let r1_sub_r0: Vec<Fq> = r1.iter().zip(&r0).map(|(&x, y)| x - y).collect();

        let result = compute_h(&mle, &r0, &r1_sub_r0).unwrap();
        assert_eq!(
            result,
            DenseUVPolynomial::from_coefficients_slice(&[Fq::from(18), Fq::from(28)])
        );
    }

    #[test]
    fn test_compute_h_errors() {
        let mle = DenseMultilinearExtension::from_evaluations_slice(1, &[Fq::from(1), Fq::from(2)]);
        let r0 = [Fq::from(5)];
        let r1_sub_r0 = [];
        let result = compute_h(&mle, &r0, &r1_sub_r0);
        assert!(result.is_err());

        let mle = DenseMultilinearExtension::from_evaluations_slice(
            2,
            &[Fq::from(1), Fq::from(2), Fq::from(1), Fq::from(2)],
        );
        let r0 = [Fq::from(4)];
        let r1 = [Fq::from(7)];
        let r1_sub_r0: Vec<Fq> = r1.iter().zip(&r0).map(|(&x, y)| x - y).collect();

        let result = compute_h(&mle, &r0, &r1_sub_r0);
        assert!(result.is_err())
    }

    #[test]
    fn test_compute_l() {
        // Test with simple non-zero values
        let r1 = vec![Fq::from(1), Fq::from(2), Fq::from(3)];
        let r1_sub_r2 = vec![Fq::from(4), Fq::from(5), Fq::from(6)];
        let x = Fq::from(2);

        let expected = vec![
            Fq::from(1) + Fq::from(2) * Fq::from(4),
            Fq::from(2) + Fq::from(2) * Fq::from(5),
            Fq::from(3) + Fq::from(2) * Fq::from(6),
        ];

        let result = compute_l(&r1, &r1_sub_r2, x).unwrap();
        assert_eq!(result, expected);
    }
}
