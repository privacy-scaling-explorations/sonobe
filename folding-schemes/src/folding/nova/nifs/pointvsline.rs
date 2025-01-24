use ark_crypto_primitives::sponge::Absorb;
use ark_ff::{One, PrimeField};
use ark_poly::univariate::DensePolynomial;
use ark_poly::{DenseMultilinearExtension, DenseUVPolynomial, Polynomial};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{log2, Zero};
use std::fmt::Debug;

use crate::folding::nova::nifs::mova::{CommittedInstance, Witness};
use crate::folding::nova::nifs::mova_matrix::{RelaxedCommitedRelation, Witness as MatrixWitness};
use crate::transcript::Transcript;
use crate::utils::mle::dense_vec_to_dense_mle;
use crate::{Curve, Error};

/// Implements the Points vs Line as described in
/// [Mova](https://eprint.iacr.org/2024/1220.pdf) and Section 4.5.2 from Thaler’s book

pub struct PointVsLineEvaluationClaimR1CS<C: Curve> {
    pub mleE1_prime: C::ScalarField,
    pub mleE2_prime: C::ScalarField,
    pub rE_prime: Vec<C::ScalarField>,
}
/// Proof from step 1 protocol 6
#[derive(Debug, Clone, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct PointVsLineProofR1CS<C: Curve> {
    pub h1: DensePolynomial<C::ScalarField>,
    pub h2: DensePolynomial<C::ScalarField>,
}

pub struct PointVsLineEvaluationClaimMatrix<C: Curve> {
    pub mleE2_prime: C::ScalarField,
    pub rE_prime: Vec<C::ScalarField>,
}
/// Proof from step 1 protocol 6
#[derive(Debug, Clone, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct PointVsLineProofMatrix<C: Curve> {
    pub h2: DensePolynomial<C::ScalarField>,
}

pub trait PointVsLine<C: Curve, T: Transcript<C::ScalarField>> {
    type PointVsLineProof: Debug + Clone;

    type PointVsLineEvaluationClaim;

    type CommittedInstance: Debug + Clone + Absorb; // + CommittedInstanceOps<C>;
    type Witness: Debug + Clone;

    fn prove(
        transcript: &mut T,
        ci1: Option<&Self::CommittedInstance>,
        ci2: &Self::CommittedInstance,
        w1: &Self::Witness,
        w2: &Self::Witness,
    ) -> Result<(Self::PointVsLineProof, Self::PointVsLineEvaluationClaim), Error>;

    fn verify(
        transcript: &mut T,
        ci1: &Self::CommittedInstance,
        ci2: &Self::CommittedInstance,
        proof: &Self::PointVsLineProof,
        mleE1_prime: Option<&C::ScalarField>,
        mleE2_prime: &<C>::ScalarField,
    ) -> Result<
        Vec<<C>::ScalarField>, // rE=rE1'=rE2'.
        Error,
    >;
}
#[derive(Clone, Debug, Default)]
pub struct PointVsLineR1CS<C: Curve, T: Transcript<C::ScalarField>> {
    _phantom_C: std::marker::PhantomData<C>,
    _phantom_T: std::marker::PhantomData<T>,
}

/// Protocol 6 from Mova
impl<C: Curve, T: Transcript<C::ScalarField>> PointVsLine<C, T> for PointVsLineR1CS<C, T> {
    type PointVsLineProof = PointVsLineProofR1CS<C>;
    type PointVsLineEvaluationClaim = PointVsLineEvaluationClaimR1CS<C>;
    type CommittedInstance = CommittedInstance<C>;
    type Witness = Witness<C>;

    fn prove(
        transcript: &mut T,
        ci1: Option<&Self::CommittedInstance>,
        ci2: &Self::CommittedInstance,
        w1: &Self::Witness,
        w2: &Self::Witness,
    ) -> Result<(Self::PointVsLineProof, Self::PointVsLineEvaluationClaim), Error> {
        let ci1 = ci1.ok_or_else(|| Error::Other("Missing ci1 in R1CS prove".to_string()))?;

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

        let beta = transcript.get_challenge();

        let mleE1_prime = h1.evaluate(&beta);
        let mleE2_prime = h2.evaluate(&beta);

        let rE_prime = compute_l(&ci1.rE, &r1_sub_r2, beta)?;

        Ok((
            Self::PointVsLineProof { h1, h2 },
            Self::PointVsLineEvaluationClaim {
                mleE1_prime,
                mleE2_prime,
                rE_prime,
            },
        ))
    }

    fn verify(
        transcript: &mut T,
        ci1: &Self::CommittedInstance,
        ci2: &Self::CommittedInstance,
        proof: &Self::PointVsLineProof,
        mleE1_prime: Option<&C::ScalarField>,
        mleE2_prime: &<C>::ScalarField,
    ) -> Result<Vec<<C>::ScalarField>, Error> {
        if proof.h1.evaluate(&C::ScalarField::zero()) != ci1.mleE {
            return Err(Error::NotEqual);
        }

        if proof.h2.evaluate(&C::ScalarField::one()) != ci2.mleE {
            return Err(Error::NotEqual);
        }

        transcript.absorb(&proof.h1.coeffs());
        transcript.absorb(&proof.h2.coeffs());

        let beta = transcript.get_challenge();

        if let Some(mleE1_prime_val) = mleE1_prime {
            if *mleE1_prime_val != proof.h1.evaluate(&beta) {
                return Err(Error::NotEqual);
            }
        } else {
            return Err(Error::Other(
                "Missing mleE1_prime in R1CS verify".to_string(),
            ));
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

#[derive(Clone, Debug, Default)]
pub struct PointVsLineMatrix<C: Curve, T: Transcript<C::ScalarField>> {
    _phantom_C: std::marker::PhantomData<C>,
    _phantom_T: std::marker::PhantomData<T>,
}

impl<C: Curve, T: Transcript<C::ScalarField>> PointVsLine<C, T> for PointVsLineMatrix<C, T> {
    type PointVsLineProof = PointVsLineProofMatrix<C>;
    type PointVsLineEvaluationClaim = PointVsLineEvaluationClaimMatrix<C>;
    type CommittedInstance = RelaxedCommitedRelation<C>;
    type Witness = MatrixWitness<C>;

    fn prove(
        transcript: &mut T,
        _ci1: Option<&Self::CommittedInstance>,
        ci2: &Self::CommittedInstance,
        w1: &Self::Witness,
        w2: &Self::Witness,
    ) -> Result<(Self::PointVsLineProof, Self::PointVsLineEvaluationClaim), Error> {
        let n_vars: usize = log2(w1.E.len()) as usize;
        let r1_scalar = C::ScalarField::from_le_bytes_mod_order(b"r1");
        transcript.absorb(&r1_scalar);

        let r1 = transcript.get_challenges(ci2.rE.len());

        let mleE2 = dense_vec_to_dense_mle(n_vars, &w2.E);

        // We have l(0) = r1, l(1) = r2 so we know that l(x) = r1 + x(r2-r1) thats why we need r2-r1
        let r1_sub_r2: Vec<<C>::ScalarField> =
            r1.iter().zip(&ci2.rE).map(|(&r1, r2)| r1 - r2).collect();

        let h2 = compute_h(&mleE2, &r1, &r1_sub_r2)?;

        transcript.absorb(&h2.coeffs());

        let beta = transcript.get_challenge();

        let mleE2_prime = h2.evaluate(&beta);

        let rE_prime = compute_l(&r1, &r1_sub_r2, beta)?;

        Ok((
            Self::PointVsLineProof { h2 },
            Self::PointVsLineEvaluationClaim {
                mleE2_prime,
                rE_prime,
            },
        ))
    }

    fn verify(
        transcript: &mut T,
        ci1: &Self::CommittedInstance,
        ci2: &Self::CommittedInstance,
        proof: &Self::PointVsLineProof,
        _mleE1_prime: Option<&C::ScalarField>,
        mleE2_prime: &<C>::ScalarField,
    ) -> Result<Vec<<C>::ScalarField>, Error> {
        if proof.h2.evaluate(&C::ScalarField::one()) != ci2.mleE {
            return Err(Error::NotEqual);
        }

        let r1_scalar = C::ScalarField::from_le_bytes_mod_order(b"r1");
        transcript.absorb(&r1_scalar);

        let r1 = transcript.get_challenges(ci2.rE.len());

        transcript.absorb(&proof.h2.coeffs());

        let beta = transcript.get_challenge();

        if *mleE2_prime != proof.h2.evaluate(&beta) {
            return Err(Error::NotEqual);
        }

        let r1_sub_r2: Vec<<C>::ScalarField> =
            r1.iter().zip(&ci2.rE).map(|(&r1, r2)| r1 - r2).collect();
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
    use crate::Error;
    use ark_pallas::Fq;
    use ark_poly::{DenseMultilinearExtension, DenseUVPolynomial};

    #[test]
    fn test_compute_h() -> Result<(), Error> {
        let mle = DenseMultilinearExtension::from_evaluations_slice(1, &[Fq::from(1), Fq::from(2)]);
        let r0 = [Fq::from(5)];
        let r1 = [Fq::from(6)];
        let r1_sub_r0: Vec<Fq> = r1.iter().zip(&r0).map(|(&x, y)| x - y).collect();

        let result = compute_h(&mle, &r0, &r1_sub_r0)?;
        assert_eq!(
            result,
            DenseUVPolynomial::from_coefficients_slice(&[Fq::from(6), Fq::from(1)])
        );

        let mle = DenseMultilinearExtension::from_evaluations_slice(1, &[Fq::from(1), Fq::from(2)]);
        let r0 = [Fq::from(4)];
        let r1 = [Fq::from(7)];
        let r1_sub_r0: Vec<Fq> = r1.iter().zip(&r0).map(|(&x, y)| x - y).collect();

        let result = compute_h(&mle, &r0, &r1_sub_r0)?;
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

        let result = compute_h(&mle, &r0, &r1_sub_r0)?;
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

        let result = compute_h(&mle, &r0, &r1_sub_r0)?;
        assert_eq!(
            result,
            DenseUVPolynomial::from_coefficients_slice(&[Fq::from(18), Fq::from(28)])
        );
        Ok(())
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
    fn test_compute_l() -> Result<(), Error> {
        // Test with simple non-zero values
        let r1 = vec![Fq::from(1), Fq::from(2), Fq::from(3)];
        let r1_sub_r2 = vec![Fq::from(4), Fq::from(5), Fq::from(6)];
        let x = Fq::from(2);

        let expected = vec![
            Fq::from(1) + Fq::from(2) * Fq::from(4),
            Fq::from(2) + Fq::from(2) * Fq::from(5),
            Fq::from(3) + Fq::from(2) * Fq::from(6),
        ];

        let result = compute_l(&r1, &r1_sub_r2, x)?;
        assert_eq!(result, expected);
        Ok(())
    }
}
