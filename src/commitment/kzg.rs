/// This file is a wrapper over arkworks/poly-commit's KZG implementation, to adapt it to the
/// CommitmentScheme trait.
///
/// The motivation to do so, is that we want to be able to use KZG / Pedersen for committing to
/// vectors indistinctly, and the arkworks KZG10 implementation contains all the methods under the
/// same trait, which requires the Pairing trait, where the prover does not need access to the
/// Pairing but only to G1.
/// For our case, we want the folding schemes prover to be agnostic to pairings, since in the
/// non-ethereum cases we may use non-pairing-friendly curves with Pedersen commitments, so the
/// trait & types that we use should not depend on the Pairing type for the prover. Thus, we
/// separate the CommitmentSchemeProver from the setup and verify phases, so the prover can be
/// defined without depending on pairings.
use ark_ec::{pairing::Pairing, AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ff::PrimeField;
use ark_poly::{
    univariate::DensePolynomial, DenseUVPolynomial, EvaluationDomain, Evaluations,
    GeneralEvaluationDomain, Polynomial,
};
use ark_poly_commit::kzg10::{UniversalParams, VerifierKey, KZG10};
use ark_std::{borrow::Cow, fmt::Debug};
use ark_std::{ops::Mul, rand::Rng};
use core::marker::PhantomData;
use derivative::Derivative;
use rayon::iter::{IntoParallelRefIterator, ParallelIterator};

// use super::CommitmentScheme;
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

#[derive(Derivative)]
#[derivative(
    // Default(bound = ""),
    // Hash(bound = ""),
    Clone(bound = ""),
    Debug(bound = ""),
    PartialEq
)]
pub struct KZGParams<'a, P: Pairing> {
    universal_params: UniversalParams<P>,
    powers: Powers<'a, P::G1>,
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

impl<'a, P> CommitmentSetup<'a, P> for KZGSetup<P>
where
    P: Pairing,
{
    type Params = KZGParams<'a, P>;
    fn setup<R: Rng>(rng: &mut R, len: usize) -> Self::Params {
        let len = len.next_power_of_two();
        let universal_params = KZG10::<P, DensePolynomial<P::ScalarField>>::setup(len, false, rng)
            .expect("Setup failed");
        let powers_of_g = universal_params.powers_of_g[..=len].to_vec();
        let powers_of_gamma_g = (0..=len)
            .map(|i| universal_params.powers_of_gamma_g[&i])
            .collect();
        let powers = Powers::<P::G1> {
            powers_of_g: ark_std::borrow::Cow::Owned(powers_of_g),
            // powers_of_gamma_g: ark_std::borrow::Cow::Owned(powers_of_gamma_g),
            // powers_of_g: powers_of_g.clone(), // WIP
            powers_of_gamma_g: ark_std::borrow::Cow::Owned(powers_of_gamma_g),
        };
        KZGParams {
            universal_params,
            powers,
        }
    }
}

pub struct KZGProver<'a, C: CurveGroup> {
    _a: PhantomData<&'a ()>,
    _c: PhantomData<C>,
}
impl<'a, C> CommitmentProver<'a, C> for KZGProver<'a, C>
where
    C: CurveGroup,
{
    // type Params = KZGParams<P>;
    type Params = Powers<'a, C>;
    // type VerifierParams = Powers<P>; // WIP
    type Proof = C;
    // type UniPoly_F = DensePolynomial<C1::ScalarField>;

    /// commit implements the CommitmentProver commit interface, adapting the implementation from
    /// https://github.com/arkworks-rs/poly-commit/tree/c724fa666e935bbba8db5a1421603bab542e15ab/poly-commit/src/kzg10/mod.rs#L178
    /// with the main difference being the remove of the randomness and blinding factors.
    fn commit(params: &Self::Params, v: &Vec<C::ScalarField>) -> Result<C, Error> {
        let polynomial = poly_from_vec(v)?;
        check_degree_is_too_large(polynomial.degree(), params.powers_of_g.len())?;

        let (num_leading_zeros, plain_coeffs) =
            skip_leading_zeros_and_convert_to_bigints(&polynomial);
        let commitment = <C as VariableBaseMSM>::msm_bigint(
            &params.powers_of_g[num_leading_zeros..],
            &plain_coeffs,
        );
        Ok(commitment)
    }
    fn prove(
        params: &Self::Params,
        v: &Vec<C::ScalarField>,
        challenge: C::ScalarField,
    ) -> Result<Self::Proof, Error> {
        let polynomial = poly_from_vec(v)?;
        check_degree_is_too_large(polynomial.degree(), params.powers_of_g.len())?;

        let witness_poly = compute_witness_polynomial::<C::ScalarField>(&polynomial, challenge);

        let proof = open_with_witness_polynomial(params, challenge, &witness_poly)?;
        Ok(proof)
    }
}
pub fn verify_single<P: Pairing>(
    vk: VerifierKey<P>,
    cm: P::G1,
    proof: P::G1,
    challenge: P::ScalarField,
    y: P::ScalarField,
) -> Result<(), Error> {
    let inner = cm - &vk.g.mul(y);
    let lhs = P::pairing(inner, vk.h);

    let inner = vk.beta_h.into_group() - &vk.h.mul(challenge);
    let rhs = P::pairing(proof, inner);

    if lhs != rhs {
        return Err(Error::CommitmentVerificationFail);
    }
    Ok(())
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
fn open_with_witness_polynomial<'a, C: CurveGroup>(
    powers: &Powers<C>,
    point: C::ScalarField, // TODO rm? only used in the randomness case
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
    let coeffs = ark_std::cfg_iter!(p)
        .map(|s| s.into_bigint())
        .collect::<Vec<_>>();
    coeffs
}

pub trait CommitmentSetup<'a, P: Pairing> {
    type Params: Debug;

    fn setup<R: Rng>(rng: &mut R, len: usize) -> Self::Params;
}
pub trait CommitmentProver<'a, C: CurveGroup> {
    type Params: Debug;
    type Proof: Debug;

    fn commit(params: &Self::Params, v: &Vec<C::ScalarField>) -> Result<C, Error>;
    fn prove(
        params: &Self::Params,
        v: &Vec<C::ScalarField>,
        challenge: C::ScalarField,
    ) -> Result<Self::Proof, Error>;
}

#[cfg(test)]
mod tests {
    use ark_bn254::{Bn254, Fr, G1Projective as G1};
    use ark_std::test_rng;
    use ark_std::UniformRand;

    use super::*;

    #[test]
    fn test_kzg_commitment_scheme() {
        let rng = &mut test_rng();

        let n = 100;
        let params: KZGParams<Bn254> = KZGSetup::<Bn254>::setup(rng, n);

        let v: Vec<Fr> = std::iter::repeat_with(|| Fr::rand(rng)).take(n).collect();
        let cm = KZGProver::<G1>::commit(&params.powers, &v).unwrap();
        let challenge = Fr::rand(rng);

        let poly_v = poly_from_vec(&v).unwrap();
        let eval = poly_v.evaluate(&challenge);
        let proof = KZGProver::<G1>::prove(&params.powers, &v, challenge).unwrap();

        let vk = params.verifier_key();
        verify_single::<Bn254>(vk, cm, proof, challenge, eval).unwrap();
    }
}
