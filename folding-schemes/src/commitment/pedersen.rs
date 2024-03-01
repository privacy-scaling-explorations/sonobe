use ark_ec::CurveGroup;
use ark_ff::Field;
use ark_r1cs_std::{boolean::Boolean, groups::GroupOpsBounds, prelude::CurveVar};
use ark_relations::r1cs::SynthesisError;
use ark_std::Zero;
use ark_std::{
    rand::{Rng, RngCore},
    UniformRand,
};
use core::marker::PhantomData;

use super::CommitmentProver;
use crate::transcript::Transcript;
use crate::utils::vec::{vec_add, vec_scalar_mul};
use crate::Error;

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Proof<C: CurveGroup> {
    pub R: C,
    pub u: Vec<C::ScalarField>,
    pub r_u: C::ScalarField,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Params<C: CurveGroup> {
    pub h: C,
    pub generators: Vec<C::Affine>,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Pedersen<C: CurveGroup, const H: bool = false> {
    _c: PhantomData<C>,
}

impl<C: CurveGroup, const H: bool> Pedersen<C, H> {
    pub fn new_params<R: Rng>(rng: &mut R, max: usize) -> Params<C> {
        let generators: Vec<C::Affine> = std::iter::repeat_with(|| C::Affine::rand(rng))
            .take(max.next_power_of_two())
            .collect();
        Params::<C> {
            h: C::rand(rng),
            generators,
        }
    }
}

// implement the CommitmentProver trait for Pedersen
impl<C: CurveGroup, const H: bool> CommitmentProver<C, H> for Pedersen<C, H> {
    type Params = Params<C>;
    type Proof = Proof<C>;
    fn commit(
        params: &Self::Params,
        v: &[C::ScalarField],
        r: &C::ScalarField, // blinding factor
    ) -> Result<C, Error> {
        if params.generators.len() < v.len() {
            return Err(Error::PedersenParamsLen(params.generators.len(), v.len()));
        }
        // h⋅r + <g, v>
        // use msm_unchecked because we already ensured at the if that lengths match
        if !H {
            return Ok(C::msm_unchecked(&params.generators[..v.len()], v));
        }
        Ok(params.h.mul(r) + C::msm_unchecked(&params.generators[..v.len()], v))
    }

    fn prove(
        params: &Params<C>,
        transcript: &mut impl Transcript<C>,
        cm: &C,
        v: &[C::ScalarField],
        r: &C::ScalarField, // blinding factor
        _rng: Option<&mut dyn RngCore>,
    ) -> Result<Self::Proof, Error> {
        if params.generators.len() < v.len() {
            return Err(Error::PedersenParamsLen(params.generators.len(), v.len()));
        }

        transcript.absorb_point(cm)?;
        let r1 = transcript.get_challenge();
        let d = transcript.get_challenges(v.len());

        // R = h⋅r_1 + <g, d>
        // use msm_unchecked because we already ensured at the if that lengths match
        let mut R: C = C::msm_unchecked(&params.generators[..d.len()], &d);
        if H {
            R += params.h.mul(r1);
        }

        transcript.absorb_point(&R)?;
        let e = transcript.get_challenge();

        // u = d + v⋅e
        let u = vec_add(&vec_scalar_mul(v, &e), &d)?;
        // r_u = e⋅r + r_1
        let mut r_u = C::ScalarField::zero();
        if H {
            r_u = e * r + r1;
        }

        Ok(Self::Proof { R, u, r_u })
    }
}

impl<C: CurveGroup, const H: bool> Pedersen<C, H> {
    pub fn verify(
        params: &Params<C>,
        transcript: &mut impl Transcript<C>,
        cm: C,
        proof: Proof<C>,
    ) -> Result<(), Error> {
        if params.generators.len() < proof.u.len() {
            return Err(Error::PedersenParamsLen(
                params.generators.len(),
                proof.u.len(),
            ));
        }

        transcript.absorb_point(&cm)?;
        transcript.get_challenge(); // r_1
        transcript.get_challenges(proof.u.len()); // d
        transcript.absorb_point(&proof.R)?;
        let e = transcript.get_challenge();

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

pub type CF<C> = <<C as CurveGroup>::BaseField as Field>::BasePrimeField;

pub struct PedersenGadget<C, GC, const H: bool = false>
where
    C: CurveGroup,
    GC: CurveVar<C, CF<C>>,
{
    _cf: PhantomData<CF<C>>,
    _c: PhantomData<C>,
    _gc: PhantomData<GC>,
}

use ark_r1cs_std::ToBitsGadget;
impl<C, GC, const H: bool> PedersenGadget<C, GC, H>
where
    C: CurveGroup,
    GC: CurveVar<C, CF<C>>,

    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
    for<'a> &'a GC: GroupOpsBounds<'a, C, GC>,
{
    pub fn commit(
        h: GC,
        g: Vec<GC>,
        v: Vec<Vec<Boolean<CF<C>>>>,
        r: Vec<Boolean<CF<C>>>,
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
    use ark_ff::{BigInteger, PrimeField};
    use ark_pallas::{constraints::GVar, Fq, Fr, Projective};
    use ark_r1cs_std::{alloc::AllocVar, eq::EqGadget};
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::UniformRand;

    use super::*;
    use crate::transcript::poseidon::{poseidon_test_config, PoseidonTranscript};

    #[test]
    fn test_pedersen_vector() {
        let mut rng = ark_std::test_rng();

        let n: usize = 10;
        // setup params
        let params = Pedersen::<Projective>::new_params(&mut rng, n);
        let poseidon_config = poseidon_test_config::<Fr>();

        // init Prover's transcript
        let mut transcript_p = PoseidonTranscript::<Projective>::new(&poseidon_config);
        // init Verifier's transcript
        let mut transcript_v = PoseidonTranscript::<Projective>::new(&poseidon_config);

        let v: Vec<Fr> = std::iter::repeat_with(|| Fr::rand(&mut rng))
            .take(n)
            .collect();
        let r: Fr = Fr::rand(&mut rng);
        let cm = Pedersen::<Projective>::commit(&params, &v, &r).unwrap();
        let proof =
            Pedersen::<Projective>::prove(&params, &mut transcript_p, &cm, &v, &r, None).unwrap();
        Pedersen::<Projective>::verify(&params, &mut transcript_v, cm, proof).unwrap();
    }

    #[test]
    fn test_pedersen_circuit() {
        test_pedersen_circuit_opt::<false>();
        test_pedersen_circuit_opt::<true>();
    }
    fn test_pedersen_circuit_opt<const hiding: bool>() {
        let mut rng = ark_std::test_rng();

        let n: usize = 16;
        // setup params
        let params = Pedersen::<Projective>::new_params(&mut rng, n);

        let v: Vec<Fr> = std::iter::repeat_with(|| Fr::rand(&mut rng))
            .take(n)
            .collect();
        let r: Fr = Fr::rand(&mut rng);
        let cm = Pedersen::<Projective>::commit(&params, &v, &r).unwrap();

        let v_bits: Vec<Vec<bool>> = v.iter().map(|val| val.into_bigint().to_bits_le()).collect();
        let r_bits: Vec<bool> = r.into_bigint().to_bits_le();

        // circuit
        let cs = ConstraintSystem::<Fq>::new_ref();

        // prepare inputs
        let vVar: Vec<Vec<Boolean<Fq>>> = v_bits
            .iter()
            .map(|val_bits| {
                Vec::<Boolean<Fq>>::new_witness(cs.clone(), || Ok(val_bits.clone())).unwrap()
            })
            .collect();
        let rVar = Vec::<Boolean<Fq>>::new_witness(cs.clone(), || Ok(r_bits)).unwrap();
        let gVar = Vec::<GVar>::new_witness(cs.clone(), || Ok(params.generators)).unwrap();
        let hVar = GVar::new_witness(cs.clone(), || Ok(params.h)).unwrap();
        let expected_cmVar = GVar::new_witness(cs.clone(), || Ok(cm)).unwrap();

        // use the gadget
        let cmVar = PedersenGadget::<Projective, GVar>::commit(hVar, gVar, vVar, rVar).unwrap();
        cmVar.enforce_equal(&expected_cmVar).unwrap();
    }
}
