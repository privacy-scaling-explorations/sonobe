//! Pedersen commitment scheme implementation.
//!
//! A Pedersen commitment allows committing to a vector of values with properties like:
//! - **Binding**: The committer cannot change the committed values after committing
//! - **Hiding** (optional): The commitment reveals no information about the committed values
//!
//! This module provides both a basic commitment scheme implementation and circuit-friendly gadgets
//! for verifying commitments inside other proofs.

use ark_ec::CurveGroup;
use ark_r1cs_std::{boolean::Boolean, convert::ToBitsGadget, prelude::CurveVar};
use ark_relations::r1cs::SynthesisError;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{marker::PhantomData, rand::RngCore, UniformRand, Zero};

use super::CommitmentScheme;
use crate::folding::circuits::CF2;
use crate::transcript::Transcript;
use crate::utils::vec::{vec_add, vec_scalar_mul};
use crate::Error;

/// Pedersen proof structure containing commitment opening information
#[derive(Debug, Clone, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct Proof<C: CurveGroup> {
    /// The R commitment value computed during the proof
    pub R: C,
    /// Opening values u = d + v⋅e
    pub u: Vec<C::ScalarField>,
    /// Blinding factor for hiding
    pub r_u: C::ScalarField,
}

/// Parameters for the Pedersen commitment scheme
#[derive(Debug, Clone, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct Params<C: CurveGroup> {
    /// Generator for blinding factor
    pub h: C,
    /// Generators for committing to values
    pub generators: Vec<C::Affine>,
}

/// Pedersen commitment scheme with optional hiding
///
/// The type parameter H controls whether commitments are hiding:
/// - When H=true, commitments are hiding and use randomness
/// - When H=false, commitments are not hiding and use no randomness
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Pedersen<C: CurveGroup, const H: bool = false> {
    /// The inner [`CurveGroup`]
    _c: PhantomData<C>,
}

/// Implements the [`CommitmentScheme`] trait for Pedersen commitments
impl<C: CurveGroup, const H: bool> CommitmentScheme<C, H> for Pedersen<C, H> {
    type ProverParams = Params<C>;
    type VerifierParams = Params<C>;
    type Proof = Proof<C>;
    type ProverChallenge = (C::ScalarField, Vec<C::ScalarField>, C, C::ScalarField);
    type Challenge = C::ScalarField;

    fn setup(
        mut rng: impl RngCore,
        len: usize,
    ) -> Result<(Self::ProverParams, Self::VerifierParams), Error> {
        let generators: Vec<C::Affine> = std::iter::repeat_with(|| C::Affine::rand(&mut rng))
            .take(len.next_power_of_two())
            .collect();
        let p = Params::<C> {
            h: C::rand(&mut rng),
            generators,
        };
        Ok((p.clone(), p))
    }

    fn commit(
        params: &Self::ProverParams,
        v: &[C::ScalarField],
        r: &C::ScalarField, // blinding factor
    ) -> Result<C, Error> {
        if params.generators.len() < v.len() {
            return Err(Error::PedersenParamsLen(params.generators.len(), v.len()));
        }
        if !H && (!r.is_zero()) {
            return Err(Error::BlindingNotZero);
        }

        // h⋅r + <g, v>
        // use msm_unchecked because we already ensured at the if that lengths match
        if !H {
            return Ok(C::msm_unchecked(&params.generators[..v.len()], v));
        }
        Ok(params.h.mul(r) + C::msm_unchecked(&params.generators[..v.len()], v))
    }

    // TODO (autoparallel): I'm guessing `_rng` is marked with prefix `_` because it goes unused always and it is planned for the future? Otherwise we should remove that prefix.
    fn prove(
        params: &Self::ProverParams,
        transcript: &mut impl Transcript<C::ScalarField>,
        cm: &C,
        v: &[C::ScalarField],
        r: &C::ScalarField, // blinding factor
        _rng: Option<&mut dyn RngCore>,
    ) -> Result<Self::Proof, Error> {
        transcript.absorb_nonnative(cm);
        let r1 = transcript.get_challenge();
        let d = transcript.get_challenges(v.len());

        // R = h⋅r_1 + <g, d>
        // use msm_unchecked because we already ensured at the if that lengths match
        let mut R: C = C::msm_unchecked(&params.generators[..d.len()], &d);
        if H {
            R += params.h.mul(r1);
        }

        transcript.absorb_nonnative(&R);
        let e = transcript.get_challenge();

        let challenge = (r1, d, R, e);
        Self::prove_with_challenge(params, challenge, v, r, _rng)
    }

    fn prove_with_challenge(
        params: &Self::ProverParams,
        challenge: Self::ProverChallenge,
        v: &[C::ScalarField], // vector
        r: &C::ScalarField,   // blinding factor
        _rng: Option<&mut dyn RngCore>,
    ) -> Result<Self::Proof, Error> {
        if params.generators.len() < v.len() {
            return Err(Error::PedersenParamsLen(params.generators.len(), v.len()));
        }
        if !H && (!r.is_zero()) {
            return Err(Error::BlindingNotZero);
        }
        let (r1, d, R, e): (C::ScalarField, Vec<C::ScalarField>, C, C::ScalarField) = challenge;

        // u = d + v⋅e
        let u = vec_add(&vec_scalar_mul(v, &e), &d)?;
        // r_u = e⋅r + r_1
        let mut r_u = C::ScalarField::zero();
        if H {
            r_u = e * r + r1;
        }

        Ok(Self::Proof { R, u, r_u })
    }

    fn verify(
        params: &Self::VerifierParams,
        transcript: &mut impl Transcript<C::ScalarField>,
        cm: &C,
        proof: &Proof<C>,
    ) -> Result<(), Error> {
        transcript.absorb_nonnative(cm);
        transcript.get_challenge(); // r_1
        transcript.get_challenges(proof.u.len()); // d
        transcript.absorb_nonnative(&proof.R);
        let e = transcript.get_challenge();
        Self::verify_with_challenge(params, e, cm, proof)
    }

    fn verify_with_challenge(
        params: &Self::VerifierParams,
        challenge: Self::Challenge,
        cm: &C,
        proof: &Proof<C>,
    ) -> Result<(), Error> {
        if params.generators.len() < proof.u.len() {
            return Err(Error::PedersenParamsLen(
                params.generators.len(),
                proof.u.len(),
            ));
        }
        if !H && (!proof.r_u.is_zero()) {
            return Err(Error::BlindingNotZero);
        }

        let e = challenge;

        // check that: R + cm⋅e == h⋅r_u + <g, u>
        let lhs = proof.R + cm.mul(e);
        // use msm_unchecked because we already ensured at the if that lengths match
        let mut rhs = C::msm_unchecked(&params.generators[..proof.u.len()], &proof.u);
        if H {
            rhs += params.h.mul(proof.r_u);
        }
        if lhs != rhs {
            return Err(Error::CommitmentVerificationFail);
        }
        Ok(())
    }
}

/// Gadget for verifying Pedersen commitments in circuits
pub struct PedersenGadget<C, GC, const H: bool = false>
where
    C: CurveGroup,
    GC: CurveVar<C, CF2<C>>,
{
    /// The inner constraint field [`CF2`]
    _cf: PhantomData<CF2<C>>,
    /// The inner [`CurveGroup`]
    _c: PhantomData<C>,
    /// The inner [`CurveVar`]
    _gc: PhantomData<GC>,
}

impl<C, GC, const H: bool> PedersenGadget<C, GC, H>
where
    C: CurveGroup,
    GC: CurveVar<C, CF2<C>>,
{
    /// Creates a Pedersen commitment inside a circuit
    ///
    /// # Arguments
    ///
    /// * `h` - Generator for blinding factor
    /// * `g` - Generators for values
    /// * `v` - Values to commit to, as boolean vectors
    /// * `r` - Blinding factor as boolean vector
    ///
    /// # Errors
    ///
    /// Returns a `SynthesisError` if:
    /// - Converting any vectors to field elements fails
    /// - Scalar multiplication fails
    pub fn commit(
        h: &GC,
        g: &[GC],
        v: &[Vec<Boolean<CF2<C>>>],
        r: &[Boolean<CF2<C>>],
    ) -> Result<GC, SynthesisError> {
        let mut res = GC::zero();
        if H {
            res += h.scalar_mul_le(r.iter())?;
        }
        for (i, v_i) in v.iter().enumerate() {
            res += g[i].scalar_mul_le(v_i.to_bits_le()?.iter())?;
        }
        Ok(res)
    }
}

#[cfg(test)]
mod tests {
    use ark_crypto_primitives::sponge::{poseidon::PoseidonSponge, CryptographicSponge};
    use ark_ff::{BigInteger, PrimeField};
    use ark_pallas::{constraints::GVar, Fq, Fr, Projective};
    use ark_r1cs_std::{alloc::AllocVar, eq::EqGadget};
    use ark_relations::r1cs::ConstraintSystem;

    use super::*;
    use crate::transcript::poseidon::poseidon_canonical_config;

    #[test]
    fn test_pedersen() -> Result<(), Error> {
        test_pedersen_opt::<false>()?;
        test_pedersen_opt::<true>()?;
        Ok(())
    }
    fn test_pedersen_opt<const hiding: bool>() -> Result<(), Error> {
        let mut rng = ark_std::test_rng();

        let n: usize = 10;
        // setup params
        let (params, _) = Pedersen::<Projective>::setup(&mut rng, n)?;
        let poseidon_config = poseidon_canonical_config::<Fr>();

        // init Prover's transcript
        let mut transcript_p = PoseidonSponge::<Fr>::new(&poseidon_config);
        // init Verifier's transcript
        let mut transcript_v = PoseidonSponge::<Fr>::new(&poseidon_config);

        let v: Vec<Fr> = std::iter::repeat_with(|| Fr::rand(&mut rng))
            .take(n)
            .collect();
        // blinding factor
        let r: Fr = if hiding {
            Fr::rand(&mut rng)
        } else {
            Fr::zero()
        };
        let cm = Pedersen::<Projective, hiding>::commit(&params, &v, &r)?;
        let proof =
            Pedersen::<Projective, hiding>::prove(&params, &mut transcript_p, &cm, &v, &r, None)?;
        Pedersen::<Projective, hiding>::verify(&params, &mut transcript_v, &cm, &proof)?;
        Ok(())
    }

    #[test]
    fn test_pedersen_circuit() -> Result<(), Error> {
        test_pedersen_circuit_opt::<false>()?;
        test_pedersen_circuit_opt::<true>()?;
        Ok(())
    }
    fn test_pedersen_circuit_opt<const hiding: bool>() -> Result<(), Error> {
        let mut rng = ark_std::test_rng();

        let n: usize = 8;
        // setup params
        let (params, _) = Pedersen::<Projective, hiding>::setup(&mut rng, n)?;

        let v: Vec<Fr> = std::iter::repeat_with(|| Fr::rand(&mut rng))
            .take(n)
            .collect();
        // blinding factor
        let r: Fr = if hiding {
            Fr::rand(&mut rng)
        } else {
            Fr::zero()
        };
        let cm = Pedersen::<Projective, hiding>::commit(&params, &v, &r)?;

        let v_bits: Vec<Vec<bool>> = v.iter().map(|val| val.into_bigint().to_bits_le()).collect();
        let r_bits: Vec<bool> = r.into_bigint().to_bits_le();

        // circuit
        let cs = ConstraintSystem::<Fq>::new_ref();

        // prepare inputs
        let vVar: Vec<Vec<Boolean<Fq>>> = v_bits
            .iter()
            .map(|val_bits| Vec::<Boolean<Fq>>::new_witness(cs.clone(), || Ok(val_bits.clone())))
            .collect::<Result<_, _>>()?;
        let rVar = Vec::<Boolean<Fq>>::new_witness(cs.clone(), || Ok(r_bits))?;
        let gVar = Vec::<GVar>::new_witness(cs.clone(), || Ok(params.generators))?;
        let hVar = GVar::new_witness(cs.clone(), || Ok(params.h))?;
        let expected_cmVar = GVar::new_witness(cs, || Ok(cm))?;

        // use the gadget
        let cmVar = PedersenGadget::<Projective, GVar, hiding>::commit(&hVar, &gVar, &vVar, &rVar)?;
        cmVar.enforce_equal(&expected_cmVar)?;
        Ok(())
    }
}
