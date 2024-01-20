/// Adaptation of the prover methods and structs from arkworks/poly-commit's KZG10 implementation
/// into the CommitmentProver trait.
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
use ark_poly_commit::kzg10::{VerifierKey, KZG10};
use ark_std::rand::Rng;
use ark_std::{borrow::Cow, fmt::Debug};
use ark_std::{One, Zero};
use core::marker::PhantomData;
use rayon::iter::{IntoParallelRefIterator, ParallelIterator};

use super::CommitmentProver;
use crate::transcript::Transcript;
use crate::Error;

/// ProverKey defines a similar struct as in ark_poly_commit::kzg10::Powers, but instead of
/// depending on the Pairing trait it depends on the CurveGroup trait.
#[derive(Debug, Clone, Default, Eq, PartialEq)]
pub struct ProverKey<'a, C: CurveGroup> {
    /// Group elements of the form `β^i G`, for different values of `i`.
    pub powers_of_g: Cow<'a, [C::Affine]>,
}

pub struct KZGSetup<P: Pairing> {
    _p: PhantomData<P>,
}
impl<'a, P> KZGSetup<P>
where
    P: Pairing,
{
    /// setup returns the tuple (ProverKey, VerifierKey). For real world deployments the setup must
    /// be computed in the most trustless way possible, usually through a MPC ceremony.
    pub fn setup<R: Rng>(rng: &mut R, len: usize) -> (ProverKey<'a, P::G1>, VerifierKey<P>) {
        let len = len.next_power_of_two();
        let universal_params = KZG10::<P, DensePolynomial<P::ScalarField>>::setup(len, false, rng)
            .expect("Setup failed");
        let powers_of_g = universal_params.powers_of_g[..=len].to_vec();
        let powers = ProverKey::<P::G1> {
            powers_of_g: ark_std::borrow::Cow::Owned(powers_of_g),
        };
        let vk = VerifierKey {
            g: universal_params.powers_of_g[0],
            gamma_g: universal_params.powers_of_gamma_g[&0],
            h: universal_params.h,
            beta_h: universal_params.beta_h,
            prepared_h: universal_params.prepared_h.clone(),
            prepared_beta_h: universal_params.prepared_beta_h.clone(),
        };
        (powers, vk)
    }
}

/// KZGProver implements the CommitmentProver trait for the KZG commitment scheme.
pub struct KZGProver<'a, C: CurveGroup> {
    _a: PhantomData<&'a ()>,
    _c: PhantomData<C>,
}
impl<'a, C> CommitmentProver<C> for KZGProver<'a, C>
where
    C: CurveGroup,
{
    type Params = ProverKey<'a, C>;
    /// Proof is a tuple containing (evaluation, proof)
    type Proof = (C::ScalarField, C);

    /// commit implements the CommitmentProver commit interface, adapting the implementation from
    /// https://github.com/arkworks-rs/poly-commit/tree/c724fa666e935bbba8db5a1421603bab542e15ab/poly-commit/src/kzg10/mod.rs#L178
    /// with the main difference being the removal of the blinding factors and the no-dependancy to
    /// the Pairing trait.
    fn commit(
        params: &Self::Params,
        v: &[C::ScalarField],
        _blind: &C::ScalarField,
    ) -> Result<C, Error> {
        if !_blind.is_zero() {
            return Err(Error::NotSupportedYet("blinding factors".to_string()));
        }

        let polynomial = poly_from_vec(v.to_vec())?;
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
        if !_blind.is_zero() {
            return Err(Error::NotSupportedYet("blinding factors".to_string()));
        }

        let polynomial = poly_from_vec(v.to_vec())?;
        check_degree_is_too_large(polynomial.degree(), params.powers_of_g.len())?;

        transcript.absorb_point(cm)?;
        let challenge = transcript.get_challenge();

        // Compute q(x) = (p(x) - p(z)) / (x-z). Observe that this quotient does not change with z
        // because p(z) is the remainder term. We can therefore omit p(z) when computing the
        // quotient.
        let divisor = DensePolynomial::<C::ScalarField>::from_coefficients_vec(vec![
            -challenge,
            C::ScalarField::one(),
        ]);
        let witness_poly: DensePolynomial<C::ScalarField> = &polynomial / &divisor;

        check_degree_is_too_large(witness_poly.degree(), params.powers_of_g.len())?;
        let (num_leading_zeros, witness_coeffs) =
            skip_leading_zeros_and_convert_to_bigints(&witness_poly);
        let proof = <C as VariableBaseMSM>::msm_bigint(
            &params.powers_of_g[num_leading_zeros..],
            &witness_coeffs,
        );

        Ok((polynomial.evaluate(&challenge), proof))
    }
}

/// returns the unique polynomial of degree=v.len().next_power_of_two(), which passes through all
/// the given elements of v
fn poly_from_vec<F: PrimeField>(v: Vec<F>) -> Result<DensePolynomial<F>, Error> {
    let D = GeneralEvaluationDomain::<F>::new(v.len()).ok_or(Error::NewDomainFail)?;
    Ok(Evaluations::from_vec_and_domain(v, D).interpolate())
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
    use ark_std::{test_rng, UniformRand};

    use super::*;
    use crate::transcript::poseidon::{tests::poseidon_test_config, PoseidonTranscript};

    #[test]
    fn test_kzg_commitment_scheme() {
        let rng = &mut test_rng();
        let poseidon_config = poseidon_test_config::<Fr>();
        let transcript_p = &mut PoseidonTranscript::<G1>::new(&poseidon_config);
        let transcript_v = &mut PoseidonTranscript::<G1>::new(&poseidon_config);

        let n = 10;
        let (pk, vk): (ProverKey<G1>, VerifierKey<Bn254>) = KZGSetup::<Bn254>::setup(rng, n);

        let v: Vec<Fr> = std::iter::repeat_with(|| Fr::rand(rng)).take(n).collect();
        let cm = KZGProver::<G1>::commit(&pk, &v, &Fr::zero()).unwrap();

        let (eval, proof) =
            KZGProver::<G1>::prove(&pk, transcript_p, &cm, &v, &Fr::zero()).unwrap();

        // verify the proof:
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
