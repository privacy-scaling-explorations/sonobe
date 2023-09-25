use ark_ec::CurveGroup;
use ark_std::{rand::Rng, UniformRand};
use std::marker::PhantomData;

use crate::utils::vec::{vec_add, vec_scalar_mul};

use crate::transcript::Transcript;

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Proof<C: CurveGroup> {
    R: C,
    u: Vec<C::ScalarField>,
    r_u: C::ScalarField,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Params<C: CurveGroup> {
    h: C,
    pub generators: Vec<C::Affine>,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Pedersen<C: CurveGroup> {
    _c: PhantomData<C>,
}

impl<C: CurveGroup> Pedersen<C> {
    pub fn new_params<R: Rng>(rng: &mut R, max: usize) -> Params<C> {
        let generators: Vec<C::Affine> = std::iter::repeat_with(|| C::Affine::rand(rng))
            .take(max.next_power_of_two())
            .collect();
        let params: Params<C> = Params::<C> {
            h: C::rand(rng),
            generators,
        };
        params
    }

    pub fn commit(params: &Params<C>, v: &Vec<C::ScalarField>, r: &C::ScalarField) -> C {
        // h⋅r + <g, v>
        params.h.mul(r) + C::msm(&params.generators[..v.len()], v).unwrap()
    }

    pub fn prove(
        params: &Params<C>,
        transcript: &mut impl Transcript<C>,
        cm: &C,
        v: &Vec<C::ScalarField>,
        r: &C::ScalarField,
    ) -> Proof<C> {
        transcript.absorb_point(cm);
        let r1 = transcript.get_challenge();
        let d = transcript.get_challenges(v.len());

        // R = h⋅r_1 + <g, d>
        let R: C = params.h.mul(r1) + C::msm(&params.generators[..d.len()], &d).unwrap();

        transcript.absorb_point(&R);
        let e = transcript.get_challenge();

        // u = d + v⋅e
        let u = vec_add(&vec_scalar_mul(v, &e), &d);
        // r_u = e⋅r + r_1
        let r_u = e * r + r1;

        Proof::<C> { R, u, r_u }
    }

    pub fn verify(
        params: &Params<C>,
        transcript: &mut impl Transcript<C>,
        cm: C,
        proof: Proof<C>,
    ) -> bool {
        transcript.absorb_point(&cm);
        transcript.get_challenge(); // r_1
        transcript.get_challenges(proof.u.len()); // d
        transcript.absorb_point(&proof.R);
        let e = transcript.get_challenge();

        // check that: R + cm == h⋅r_u + <g, u>
        let lhs = proof.R + cm.mul(e);
        let rhs = params.h.mul(proof.r_u)
            + C::msm(&params.generators[..proof.u.len()], &proof.u).unwrap();
        if lhs != rhs {
            return false;
        }
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::transcript::poseidon::{tests::poseidon_test_config, PoseidonTranscript};
    use crate::transcript::keccak::{tests::keccak_test_config, KeccakTranscript};
    use crate::transcript::sha3::{tests::sha3_test_config, SHA3Transcript};
    use crate::transcript::Transcript;

    use ark_pallas::{Fr, Projective};

    fn test_pedersen_vector_with<T: Transcript<Projective>>(config: T::TranscriptConfig) {
        let mut transcript_p: T = Transcript::<Projective>::new(&config);
        let mut transcript_v: T = Transcript::<Projective>::new(&config);
        let mut rng = ark_std::test_rng();

        const n: usize = 10;
        // setup params
        let params = Pedersen::<Projective>::new_params(&mut rng, n);

        let v: Vec<Fr> = vec![Fr::rand(&mut rng); n];
        let r: Fr = Fr::rand(&mut rng);
        let cm = Pedersen::<Projective>::commit(&params, &v, &r);
        let proof = Pedersen::<Projective>::prove(&params, &mut transcript_p, &cm, &v, &r);
        let v = Pedersen::<Projective>::verify(&params, &mut transcript_v, cm, proof);
        assert!(v);
    }

    #[test]
    fn test_pedersen_vector() {
        // Test for Poseidon
        test_pedersen_vector_with::<PoseidonTranscript<Projective>>(poseidon_test_config::<Fr>());
        // Test for Keccak
        test_pedersen_vector_with::<KeccakTranscript<Projective>>(keccak_test_config::<Fr>());
        // Test for SHA3
        test_pedersen_vector_with::<SHA3Transcript<Projective>>(sha3_test_config::<Fr>());
    }
}
