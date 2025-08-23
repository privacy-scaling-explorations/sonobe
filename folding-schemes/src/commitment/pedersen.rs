use ark_r1cs_std::{boolean::Boolean, convert::ToBitsGadget, groups::CurveVar};
use ark_relations::gr1cs::SynthesisError;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{marker::PhantomData, rand::RngCore, UniformRand, Zero};

use super::CommitmentScheme;
use crate::folding::circuits::CF2;
use crate::transcript::Transcript;
use crate::utils::vec::{vec_add, vec_scalar_mul};
use crate::{Curve, Error};

#[derive(Debug, Clone, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct Proof<C: Curve> {
    pub R: C,
    pub u: Vec<C::ScalarField>,
    pub r_u: C::ScalarField, // blind
}

#[derive(Debug, Clone, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct Params<C: Curve> {
    pub h: C,
    pub generators: Vec<C::Affine>,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Pedersen<C: Curve, const H: bool = false> {
    _c: PhantomData<C>,
}

/// Implements the CommitmentScheme trait for Pedersen commitments
impl<C: Curve, const H: bool> CommitmentScheme<C, H> for Pedersen<C, H> {
    type ProverParams = Params<C>;
    type VerifierParams = Params<C>;
    type Proof = Proof<C>;
    type ProverChallenge = (C::ScalarField, Vec<C::ScalarField>, C, C::ScalarField);
    type Challenge = C::ScalarField;

    fn is_hiding() -> bool {
        if H {
            return true;
        }
        false
    }

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

pub struct PedersenGadget<C: Curve, const H: bool = false> {
    _c: PhantomData<C>,
}

impl<C: Curve, const H: bool> PedersenGadget<C, H> {
    pub fn commit(
        h: &C::Var,
        g: &[C::Var],
        v: &[Vec<Boolean<CF2<C>>>],
        r: &[Boolean<CF2<C>>],
    ) -> Result<C::Var, SynthesisError> {
        let mut res = C::Var::zero();
        if H {
            res += h.scalar_mul_le(r.iter())?;
        }
        let n = v.len();
        if n % 2 == 1 {
            res += g[n - 1].scalar_mul_le(v[n - 1].to_bits_le()?.iter())?;
        } else {
            res += g[n - 1].joint_scalar_mul_be(
                &g[n - 2],
                v[n - 1].to_bits_le()?.iter(),
                v[n - 2].to_bits_le()?.iter(),
            )?;
        }
        for i in (1..n - 1).step_by(2) {
            res += g[i - 1].joint_scalar_mul_be(
                &g[i],
                v[i - 1].to_bits_le()?.iter(),
                v[i].to_bits_le()?.iter(),
            )?;
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
    use ark_relations::gr1cs::ConstraintSystem;

    use super::*;
    use crate::transcript::poseidon::poseidon_canonical_config;

    #[test]
    fn test_pedersen() -> Result<(), Error> {
        let _ = test_pedersen_opt::<false>()?;
        let _ = test_pedersen_opt::<true>()?;
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
        let _ = test_pedersen_circuit_opt::<false>(8)?;
        let _ = test_pedersen_circuit_opt::<true>(8)?;
        let _ = test_pedersen_circuit_opt::<false>(9)?;
        let _ = test_pedersen_circuit_opt::<true>(9)?;
        Ok(())
    }
    fn test_pedersen_circuit_opt<const hiding: bool>(n: usize) -> Result<(), Error> {
        let mut rng = ark_std::test_rng();

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
        let expected_cmVar = GVar::new_witness(cs.clone(), || Ok(cm))?;

        // use the gadget
        let cmVar = PedersenGadget::<Projective, hiding>::commit(&hVar, &gVar, &vVar, &rVar)?;
        cmVar.enforce_equal(&expected_cmVar)?;

        assert!(cs.is_satisfied()?);

        Ok(())
    }
}
