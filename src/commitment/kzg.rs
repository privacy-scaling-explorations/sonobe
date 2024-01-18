/// This file is a wrapper over arkworks/poly-commit's KZG implementation, to adapt it to the
/// CommitmentScheme trait.
///
/// The motivation to do so, is that we want to be able to use KZG / Pedersen for committing to
/// vectors indistinctly, and the arkworks KZG10 implementation contains all the methods under the
/// same trait, which requires the Pairing trait, where the prover does not need access to the
/// Pairing but only to G1.
/// For our case, we want the folding schemes prover to be agnostic to pairings, since in the
/// non-ethereum cases we may use non-pairing-friendly curves with Pedersen commitments, so the
/// trait & types that we use should not depend on the Pairing type for the prover. Therefore, we
/// separate the CommitmentSchemeProver from the setup and verify phases, so the prover can be
/// defined without depending on pairings.
use ark_ec::{pairing::Pairing, CurveGroup, VariableBaseMSM};
use ark_ff::PrimeField;
use ark_poly::{
    univariate::DensePolynomial, DenseUVPolynomial, EvaluationDomain, Evaluations,
    GeneralEvaluationDomain, Polynomial,
};
use ark_poly_commit::kzg10::{UniversalParams, VerifierKey, KZG10};
use ark_std::rand::Rng;
use ark_std::{borrow::Cow, fmt::Debug};
use core::marker::PhantomData;
use rayon::iter::{IntoParallelRefIterator, ParallelIterator};

use super::CommitmentProver;
use crate::transcript::Transcript;
use crate::Error;

/// Powers defines the same struct as in ark_poly_commit::kzg10::Powers, but instead of depending
/// on the Pairing trait it depends on the CurveGroup trait.
#[derive(Debug, Clone, Default, Eq, PartialEq)]
pub struct Powers<'a, C: CurveGroup> {
    /// Group elements of the form `β^i G`, for different values of `i`.
    pub powers_of_g: Cow<'a, [C::Affine]>,
    /// Group elements of the form `β^i γG`, for different values of `i`.
    pub powers_of_gamma_g: Cow<'a, [C::Affine]>,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct KZGParams<'a, P: Pairing> {
    pub universal_params: UniversalParams<P>,
    pub powers: Powers<'a, P::G1>,
}
impl<'a, P: Pairing> KZGParams<'a, P> {
    pub fn verifier_key(self) -> VerifierKey<P> {
        VerifierKey {
            g: self.universal_params.powers_of_g[0],
            gamma_g: self.universal_params.powers_of_gamma_g[&0],
            h: self.universal_params.h,
            beta_h: self.universal_params.beta_h,
            prepared_h: self.universal_params.prepared_h.clone(),
            prepared_beta_h: self.universal_params.prepared_beta_h.clone(),
        }
    }
}

pub struct KZGSetup<P: Pairing> {
    _p: PhantomData<P>,
}

impl<'a, P> KZGSetup<P>
where
    P: Pairing,
{
    pub fn setup<R: Rng>(rng: &mut R, len: usize) -> KZGParams<'a, P> {
        let len = len.next_power_of_two();
        let universal_params = KZG10::<P, DensePolynomial<P::ScalarField>>::setup(len, false, rng)
            .expect("Setup failed");
        let powers_of_g = universal_params.powers_of_g[..=len].to_vec();
        let powers_of_gamma_g = (0..=len)
            .map(|i| universal_params.powers_of_gamma_g[&i])
            .collect();
        let powers = Powers::<P::G1> {
            powers_of_g: ark_std::borrow::Cow::Owned(powers_of_g),
            powers_of_gamma_g: ark_std::borrow::Cow::Owned(powers_of_gamma_g),
        };
        KZGParams {
            universal_params,
            powers,
        }
    }
}

/// KZGProver implements the CommitmentProver trait for the KZG commitment scheme.
pub struct KZGProver<'a, C: CurveGroup> {
    _a: PhantomData<&'a ()>,
    _c: PhantomData<C>,
}
impl<'a, C> CommitmentProver<'a, C> for KZGProver<'a, C>
where
    C: CurveGroup,
{
    type Params = Powers<'a, C>;
    type Proof = (C::ScalarField, C); // (evaluation, proof)

    /// commit implements the CommitmentProver commit interface, adapting the implementation from
    /// https://github.com/arkworks-rs/poly-commit/tree/c724fa666e935bbba8db5a1421603bab542e15ab/poly-commit/src/kzg10/mod.rs#L178
    /// with the main difference being the removal of the blinding factors and the no-dependancy to
    /// the Pairing trait.
    fn commit(
        params: &Self::Params,
        v: &[C::ScalarField],
        _blind: &C::ScalarField,
    ) -> Result<C, Error> {
        let polynomial = poly_from_vec(&v.to_vec())?;
        check_degree_is_too_large(polynomial.degree(), params.powers_of_g.len())?;

        let (num_leading_zeros, plain_coeffs) =
            skip_leading_zeros_and_convert_to_bigints(&polynomial);
        let commitment = <C as VariableBaseMSM>::msm_bigint(
            &params.powers_of_g[num_leading_zeros..],
            &plain_coeffs,
        );
        Ok(commitment)
    }

    /// prove implements the CommitmentProver prove interface, adapting the implementation from
    /// https://github.com/arkworks-rs/poly-commit/tree/c724fa666e935bbba8db5a1421603bab542e15ab/poly-commit/src/kzg10/mod.rs#L307
    /// with the main difference being the removal of the blinding factors and the no-dependancy to
    /// the Pairing trait.
    fn prove(
        params: &Self::Params,
        transcript: &mut impl Transcript<C>,
        cm: &C,
        v: &[C::ScalarField],
        _blind: &C::ScalarField,
    ) -> Result<Self::Proof, Error> {
        let polynomial = poly_from_vec(&v.to_vec())?;
        check_degree_is_too_large(polynomial.degree(), params.powers_of_g.len())?;

        transcript.absorb_point(cm)?;
        let challenge = transcript.get_challenge();

        let witness_poly = compute_witness_polynomial::<C::ScalarField>(&polynomial, challenge);

        let proof = open_with_witness_polynomial(params, challenge, &witness_poly)?;
        Ok((polynomial.evaluate(&challenge), proof))
    }
}

/// method adapted from
/// https://github.com/arkworks-rs/poly-commit/tree/c724fa666e935bbba8db5a1421603bab542e15ab/poly-commit/src/kzg10/mod.rs#L238
/// Compute witness polynomial.
///
/// The witness polynomial w(x) the quotient of the division (p(x) - p(z)) / (x - z)
/// Observe that this quotient does not change with z because
/// p(z) is the remainder term. We can therefore omit p(z) when computing the quotient.
fn compute_witness_polynomial<F: PrimeField>(
    p: &DensePolynomial<F>,
    point: F,
) -> DensePolynomial<F> {
    let divisor = DensePolynomial::<F>::from_coefficients_vec(vec![-point, F::one()]);
    p / &divisor
}
/// method adapted from
/// https://github.com/arkworks-rs/poly-commit/tree/c724fa666e935bbba8db5a1421603bab542e15ab/poly-commit/src/kzg10/mod.rs#L263
fn open_with_witness_polynomial<C: CurveGroup>(
    powers: &Powers<C>,
    _point: C::ScalarField, // TODO rm? only used in the randomness case
    witness_polynomial: &DensePolynomial<C::ScalarField>,
) -> Result<C, Error> {
    check_degree_is_too_large(witness_polynomial.degree(), powers.powers_of_g.len())?;
    let (num_leading_zeros, witness_coeffs) =
        skip_leading_zeros_and_convert_to_bigints(witness_polynomial);

    let w = <C as VariableBaseMSM>::msm_bigint(
        &powers.powers_of_g[num_leading_zeros..],
        &witness_coeffs,
    );

    Ok(w)
}

fn poly_from_vec<F: PrimeField>(v: &Vec<F>) -> Result<DensePolynomial<F>, Error> {
    let D = GeneralEvaluationDomain::<F>::new(v.len()).ok_or(Error::NewDomainFail)?;
    Ok(Evaluations::from_vec_and_domain(v.clone(), D).interpolate()) // TODO rm clone
}
fn check_degree_is_too_large(
    degree: usize,
    num_powers: usize,
) -> Result<(), ark_poly_commit::error::Error> {
    let num_coefficients = degree + 1;
    if num_coefficients > num_powers {
        Err(ark_poly_commit::error::Error::TooManyCoefficients {
            num_coefficients,
            num_powers,
        })
    } else {
        Ok(())
    }
}
fn skip_leading_zeros_and_convert_to_bigints<F: PrimeField, P: DenseUVPolynomial<F>>(
    p: &P,
) -> (usize, Vec<F::BigInt>) {
    let mut num_leading_zeros = 0;
    while num_leading_zeros < p.coeffs().len() && p.coeffs()[num_leading_zeros].is_zero() {
        num_leading_zeros += 1;
    }
    let coeffs = convert_to_bigints(&p.coeffs()[num_leading_zeros..]);
    (num_leading_zeros, coeffs)
}
fn convert_to_bigints<F: PrimeField>(p: &[F]) -> Vec<F::BigInt> {
    ark_std::cfg_iter!(p)
        .map(|s| s.into_bigint())
        .collect::<Vec<_>>()
}

#[cfg(test)]
mod tests {
    use ark_bn254::{Bn254, Fr, G1Projective as G1};
    use ark_poly_commit::kzg10::{Commitment as KZG10Commitment, Proof as KZG10Proof, KZG10};
    use ark_std::Zero;
    use ark_std::{test_rng, UniformRand};

    use super::*;
    use crate::transcript::poseidon::{tests::poseidon_test_config, PoseidonTranscript};

    #[test]
    fn test_kzg_commitment_scheme() {
        let rng = &mut test_rng();
        let poseidon_config = poseidon_test_config::<Fr>();
        let transcript_p = &mut PoseidonTranscript::<G1>::new(&poseidon_config);
        let transcript_v = &mut PoseidonTranscript::<G1>::new(&poseidon_config);

        let n = 3;
        let params: KZGParams<Bn254> = KZGSetup::<Bn254>::setup(rng, n);

        let v: Vec<Fr> = std::iter::repeat_with(|| Fr::rand(rng)).take(n).collect();
        let cm = KZGProver::<G1>::commit(&params.powers, &v, &Fr::zero()).unwrap();

        let (eval, proof) =
            KZGProver::<G1>::prove(&params.powers, transcript_p, &cm, &v, &Fr::zero()).unwrap();

        // verify the proof:
        let vk = params.verifier_key();

        // get evaluation challenge
        transcript_v.absorb_point(&cm).unwrap();
        let challenge = transcript_v.get_challenge();

        // verify the KZG proof using arkworks method
        assert!(KZG10::<Bn254, DensePolynomial<Fr>>::check(
            &vk,
            &KZG10Commitment(cm.into_affine()),
            challenge,
            eval,
            &KZG10Proof::<Bn254> {
                w: proof.into_affine(),
                random_v: None,
            },
        )
        .unwrap());
    }
}
