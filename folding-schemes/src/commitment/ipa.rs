use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{Field, PrimeField};
use ark_r1cs_std::{
    boolean::Boolean, fields::fp::FpVar, groups::GroupOpsBounds, prelude::CurveVar,
};
use ark_relations::r1cs::SynthesisError;
use ark_std::{UniformRand, Zero};
use core::marker::PhantomData;

use super::pedersen::Params as PedersenParams;
use crate::utils::vec::{vec_add, vec_scalar_mul};
use crate::Error;

pub struct IPA<C: CurveGroup> {
    _c: PhantomData<C>,
    d: u64,
    H: C,
    Gs: Vec<C>,
}

pub struct Proof<C: CurveGroup> {
    a: C::ScalarField,
    l: Vec<C::ScalarField>,
    r: Vec<C::ScalarField>,
    L: Vec<C>,
    R: Vec<C>,
}

impl<C: CurveGroup> IPA<C> {
    // pub fn new(params: &PedersenParams<C>, d: u32) -> Self {
    //     let mut rng = ark_std::rand::thread_rng();
    //
    //     let mut gs: Vec<C> = Vec::new();
    //     for _ in 0..d {
    //         gs.push(C::rand(&mut rng));
    //     }
    //
    //     IPA {
    //         d,
    //         H: C::rand(&mut rng),
    //         Gs: gs,
    //     }
    // }

    pub fn commit(
        params: &PedersenParams<C>,
        a: &[C::ScalarField],
        r: &C::ScalarField, // blinding factor
    ) -> Result<C, Error> {
        if params.generators.len() < a.len() {
            return Err(Error::PedersenParamsLen(params.generators.len(), a.len()));
        }
        // h⋅r + <g, v>
        // use msm_unchecked because we already ensured at the if that lengths match
        Ok(params.h.mul(r) + C::msm_unchecked(&params.generators[..a.len()], a))
    }

    pub fn prove(
        params: &PedersenParams<C>,
        a: &[C::ScalarField],
        // b: &[C::ScalarField],
        x: &C::ScalarField,
        u: &[C::ScalarField],
        U: &C,
        l: &Vec<C::ScalarField>, // blinding factor
        r: &Vec<C::ScalarField>, // blinding factor
    ) -> Result<Proof<C>, Error> {
        // TODO 'a' must be a power of two
        let d = a.len();
        let k = (f64::from(d as u32).log2()) as usize;

        if params.generators.len() < a.len() {
            return Err(Error::PedersenParamsLen(params.generators.len(), a.len()));
        }
        // if a.len() != b.len() {
        //     return Err(Error::NotSameLength(
        //         "a".to_string(),
        //         a.len(),
        //         "b".to_string(),
        //         b.len(),
        //     ));
        // }
        if l.len() != k {
            return Err(Error::NotExpectedLength(l.len(), k));
        }
        if r.len() != k {
            return Err(Error::NotExpectedLength(r.len(), k));
        }

        let mut a = a.to_owned();
        // let mut b = b.to_owned();
        let mut b = powers_of(*x, d);
        let mut G = params.generators.clone();

        let mut L: Vec<C> = vec![C::zero(); k];
        let mut R: Vec<C> = vec![C::zero(); k];

        for j in (0..k).rev() {
            let m = a.len() / 2;
            let a_lo = a[..m].to_vec();
            let a_hi = a[m..].to_vec();
            let b_lo = b[..m].to_vec();
            let b_hi = b[m..].to_vec();
            let G_lo = G[..m].to_vec();
            let G_hi = G[m..].to_vec();

            L[j] = C::msm_unchecked(&G_hi, &a_lo)
                + params.h.mul(l[j])
                + U.mul(inner_prod(&a_lo, &b_hi)?);
            R[j] = C::msm_unchecked(&G_lo, &a_hi)
                + params.h.mul(r[j])
                + U.mul(inner_prod(&a_hi, &b_lo)?);

            let uj = u[j];
            let uj_inv = u[j].inverse().unwrap();

            // a_hi * uj^-1 + a_lo * uj
            a = vec_add(&vec_scalar_mul(&a_lo, &uj), &vec_scalar_mul(&a_hi, &uj_inv))?;
            // b_lo * uj^-1 + b_hi * uj
            b = vec_add(&vec_scalar_mul(&b_lo, &uj_inv), &vec_scalar_mul(&b_hi, &uj))?;
            // G_lo * uj^-1 + G_hi * uj
            G = G_lo
                .iter()
                .map(|e| e.into_group().mul(uj_inv))
                .collect::<Vec<C>>()
                .iter()
                .zip(
                    G_hi.iter()
                        .map(|e| e.into_group().mul(uj))
                        .collect::<Vec<C>>()
                        .iter(),
                )
                .map(|(a, b)| (*a + *b).into_affine())
                .collect::<Vec<C::Affine>>();
        }

        if a.len() != 1 {
            return Err(Error::NotExpectedLength(a.len(), 1));
        }
        if b.len() != 1 {
            return Err(Error::NotExpectedLength(b.len(), 1));
        }
        if G.len() != 1 {
            return Err(Error::NotExpectedLength(G.len(), 1));
        }

        Ok(Proof {
            a: a[0],
            l: l.clone(), // TODO rm clone
            r: r.clone(),
            L,
            R,
        })
    }
    pub fn verify(
        params: &PedersenParams<C>,
        x: &C::ScalarField, // evaluation point
        v: &C::ScalarField, // value at evaluation point
        P: &C,              // commitment
        p: &Proof<C>,
        r: &C::ScalarField,   // blinding factor
        u: &[C::ScalarField], // challenges
        U: &C,                // challenge
        d: usize,
    ) -> Result<bool, Error> {
        let P = *P + U.mul(v);

        let mut q_0 = P;
        let mut r = *r;

        // compute b & G from s
        let s = build_s(u, d);
        let bs = powers_of(*x, d);
        let b = inner_prod(&s, &bs)?;
        if params.generators.len() < s.len() {
            // TODO check if maybe use msm (no-unchecked) and avoid this if
            return Err(Error::PedersenParamsLen(params.generators.len(), s.len()));
        }
        let G = C::msm_unchecked(&params.generators, &s);

        #[allow(clippy::needless_range_loop)]
        for j in 0..u.len() {
            let uj2 = u[j].square();
            let uj_inv2 = u[j].inverse().unwrap().square();

            q_0 = q_0 + p.L[j].mul(uj2) + p.R[j].mul(uj_inv2);
            r = r + p.l[j] * uj2 + p.r[j] * uj_inv2;
        }

        let q_1 = G.mul(p.a) + params.h.mul(r) + U.mul(p.a * b);

        Ok(q_0 == q_1)
    }
}

// s = (
//   u₁⁻¹ u₂⁻¹ … uₖ⁻¹,
//   u₁   u₂⁻¹ … uₖ⁻¹,
//   u₁⁻¹ u₂   … uₖ⁻¹,
//   u₁   u₂   … uₖ⁻¹,
//   ⋮    ⋮      ⋮
//   u₁   u₂   … uₖ
// )
fn build_s<F: PrimeField>(u: &[F], d: usize) -> Vec<F> {
    let k = (f64::from(d as u32).log2()) as usize;
    let mut s: Vec<F> = vec![F::one(); d];
    let mut t = d;
    for j in (0..k).rev() {
        t /= 2;
        let mut c = 0;
        for i in 0..d {
            if c < t {
                s[i] *= u[j].inverse().unwrap();
            } else {
                s[i] *= u[j];
            }
            c += 1;
            if c >= t * 2 {
                c = 0;
            }
        }
    }
    s
}

// TODO next 3 are WIP
fn inner_prod<F: PrimeField>(a: &[F], b: &[F]) -> Result<F, Error> {
    if a.len() != b.len() {
        return Err(Error::NotSameLength(
            "a".to_string(),
            a.len(),
            "b".to_string(),
            b.len(),
        ));
    }
    let mut c: F = F::zero();
    for i in 0..a.len() {
        c += a[i] * b[i];
    }
    Ok(c)
}
fn powers_of<F: PrimeField>(x: F, d: usize) -> Vec<F> {
    // TODO do the efficient way
    let mut c: Vec<F> = vec![F::zero(); d];
    c[0] = x;
    for i in 1..d {
        c[i] = c[i - 1] * x;
    }
    c
}

#[cfg(test)]
mod tests {
    use ark_pallas::{constraints::GVar, Fq, Fr, Projective};
    use ark_r1cs_std::{alloc::AllocVar, bits::boolean::Boolean, eq::EqGadget};
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::UniformRand;

    use super::*;
    use crate::commitment::pedersen::Pedersen;
    // use crate::transcript::poseidon::{poseidon_test_config, PoseidonTranscript};

    #[test]
    fn test_ipa() {
        let mut rng = ark_std::test_rng();

        let d: usize = 16;
        let k = (f64::from(d as u32).log2()) as usize;
        // setup params
        let params = Pedersen::<Projective>::new_params(&mut rng, d); // TODO move to IPA::new_params

        // let poseidon_config = poseidon_test_config::<Fr>();
        // // init Prover's transcript
        // let mut transcript_p = PoseidonTranscript::<Projective>::new(&poseidon_config);
        // // init Verifier's transcript
        // let mut transcript_v = PoseidonTranscript::<Projective>::new(&poseidon_config);

        let a: Vec<Fr> = std::iter::repeat_with(|| Fr::rand(&mut rng))
            .take(d)
            .collect();
        let r_blind: Fr = Fr::rand(&mut rng);
        let cm = IPA::<Projective>::commit(&params, &a, &r_blind).unwrap();

        // blinding factors
        let l: Vec<Fr> = std::iter::repeat_with(|| Fr::rand(&mut rng))
            .take(k)
            .collect();
        let r: Vec<Fr> = std::iter::repeat_with(|| Fr::rand(&mut rng))
            .take(k)
            .collect();

        // random challenges
        let u: Vec<Fr> = std::iter::repeat_with(|| Fr::rand(&mut rng))
            .take(k)
            .collect();
        let U = Projective::rand(&mut rng);

        // evaluation point
        let x = Fr::rand(&mut rng);

        let proof = IPA::<Projective>::prove(&params, &a, &x, &u, &U, &l, &r).unwrap();

        let b = powers_of(x, d); // WIP
        let v = inner_prod(&a, &b).unwrap(); // WIP
        assert!(
            IPA::<Projective>::verify(&params, &x, &v, &cm, &proof, &r_blind, &u, &U, d).unwrap()
        );
    }
}
