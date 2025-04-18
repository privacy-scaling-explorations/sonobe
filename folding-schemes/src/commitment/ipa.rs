/// IPA implements the modified Inner Product Argument described in
/// [Halo](https://eprint.iacr.org/2019/1021.pdf). The variable names used follow the paper
/// notation in order to make it more readable.
///
/// The implementation does the following optimizations in order to reduce the amount of
/// constraints in the circuit:
/// i. <s, b> computation is done in log time following a modification of the equation 3 in section
/// 3.2 from the paper.
/// ii. s computation is done in 2^{k+1}-2 instead of k*2^k.
use ark_ec::AffineRepr;
use ark_ff::{Field, PrimeField};
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    boolean::Boolean,
    convert::ToBitsGadget,
    eq::EqGadget,
    fields::{emulated_fp::EmulatedFpVar, FieldVar},
    prelude::CurveVar,
};
use ark_relations::r1cs::{Namespace, SynthesisError};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{cfg_iter, rand::RngCore, UniformRand, Zero};
use core::{borrow::Borrow, marker::PhantomData};
use rayon::iter::{IndexedParallelIterator, IntoParallelRefIterator, ParallelIterator};

use super::{pedersen::Params as PedersenParams, CommitmentScheme};
use crate::folding::circuits::CF2;
use crate::transcript::Transcript;
use crate::utils::{
    powers_of,
    vec::{vec_add, vec_scalar_mul},
};
use crate::{Curve, Error};

#[derive(Debug, Clone, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct Proof<C: Curve> {
    a: C::ScalarField,
    l: Vec<C::ScalarField>,
    r: Vec<C::ScalarField>,
    L: Vec<C>,
    R: Vec<C>,
}

/// IPA implements the Inner Product Argument protocol following the CommitmentScheme trait. The
/// `H` parameter indicates if to use the commitment in hiding mode or not.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct IPA<C: Curve, const H: bool = false> {
    _c: PhantomData<C>,
}

/// Implements the CommitmentScheme trait for IPA
impl<C: Curve, const H: bool> CommitmentScheme<C, H> for IPA<C, H> {
    type ProverParams = PedersenParams<C>;
    type VerifierParams = PedersenParams<C>;
    type Proof = (Proof<C>, C::ScalarField, C::ScalarField); // (proof, v=p(x), r=blinding factor)
    type ProverChallenge = (C::ScalarField, C, Vec<C::ScalarField>);
    type Challenge = (C::ScalarField, C, Vec<C::ScalarField>);

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
        let p = PedersenParams::<C> {
            h: C::rand(&mut rng),
            generators,
        };
        Ok((p.clone(), p))
    }

    fn commit(
        params: &PedersenParams<C>,
        a: &[C::ScalarField],
        r: &C::ScalarField, // blinding factor
    ) -> Result<C, Error> {
        if params.generators.len() < a.len() {
            return Err(Error::PedersenParamsLen(params.generators.len(), a.len()));
        }
        if !H && (!r.is_zero()) {
            return Err(Error::BlindingNotZero);
        }

        // h⋅r + <g, a>
        // use msm_unchecked because we already ensured at the if that lengths match
        if !H {
            return Ok(C::msm_unchecked(&params.generators[..a.len()], a));
        }
        Ok(params.h.mul(r) + C::msm_unchecked(&params.generators[..a.len()], a))
    }

    fn prove(
        params: &Self::ProverParams,
        transcript: &mut impl Transcript<C::ScalarField>,
        P: &C,                // commitment
        a: &[C::ScalarField], // vector
        blind: &C::ScalarField,
        rng: Option<&mut dyn RngCore>,
    ) -> Result<Self::Proof, Error> {
        if !a.len().is_power_of_two() {
            return Err(Error::NotPowerOfTwo("a".to_string(), a.len()));
        }
        if !H && (!blind.is_zero()) {
            return Err(Error::BlindingNotZero);
        }
        let d = a.len();
        let k = (f64::from(d as u32).log2()) as usize;

        if params.generators.len() < a.len() {
            return Err(Error::PedersenParamsLen(params.generators.len(), a.len()));
        }
        // blinding factors
        let l: Vec<C::ScalarField>;
        let r: Vec<C::ScalarField>;
        if H {
            let rng = rng.ok_or(Error::MissingRandomness)?;
            l = std::iter::repeat_with(|| C::ScalarField::rand(rng))
                .take(k)
                .collect();
            r = std::iter::repeat_with(|| C::ScalarField::rand(rng))
                .take(k)
                .collect();
        } else {
            l = vec![];
            r = vec![];
        }

        transcript.absorb_nonnative(P);
        let x = transcript.get_challenge(); // challenge value at which we evaluate
        let s = transcript.get_challenge();
        let U = C::generator().mul(s);

        let mut a = a.to_owned();
        let mut b = powers_of(x, d);
        let v = inner_prod(&a, &b)?;

        let mut G = params.generators.clone();

        let mut L: Vec<C> = vec![C::zero(); k];
        let mut R: Vec<C> = vec![C::zero(); k];

        // u challenges
        let mut u: Vec<C::ScalarField> = vec![C::ScalarField::zero(); k];
        for j in (0..k).rev() {
            let m = a.len() / 2;

            if H {
                L[j] = C::msm_unchecked(&G[m..], &a[..m])
                    + params.h.mul(l[j])
                    + U.mul(inner_prod(&a[..m], &b[m..])?);
                R[j] = C::msm_unchecked(&G[..m], &a[m..])
                    + params.h.mul(r[j])
                    + U.mul(inner_prod(&a[m..], &b[..m])?);
            } else {
                L[j] = C::msm_unchecked(&G[m..], &a[..m]) + U.mul(inner_prod(&a[..m], &b[m..])?);
                R[j] = C::msm_unchecked(&G[..m], &a[m..]) + U.mul(inner_prod(&a[m..], &b[..m])?);
            }
            // get challenge for the j-th round
            transcript.absorb_nonnative(&L[j]);
            transcript.absorb_nonnative(&R[j]);
            u[j] = transcript.get_challenge();

            let uj = u[j];
            let uj_inv = u[j]
                .inverse()
                .ok_or(Error::Other("error on computing inverse".to_string()))?;

            // a_hi * uj^-1 + a_lo * uj
            a = vec_add(
                &vec_scalar_mul(&a[..m], &uj),
                &vec_scalar_mul(&a[m..], &uj_inv),
            )?;
            // b_lo * uj^-1 + b_hi * uj
            b = vec_add(
                &vec_scalar_mul(&b[..m], &uj_inv),
                &vec_scalar_mul(&b[m..], &uj),
            )?;
            // G_lo * uj^-1 + G_hi * uj
            G = cfg_iter!(G[..m])
                .map(|e| e.into_group().mul(uj_inv))
                .zip(cfg_iter!(G[m..]).map(|e| e.into_group().mul(uj)))
                .map(|(a, b)| (a + b).into_affine())
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

        Ok((
            Proof {
                a: a[0],
                l: l.clone(),
                r: r.clone(),
                L,
                R,
            },
            v,      // evaluation at challenge, v=p(x)
            *blind, // blind factor
        ))
    }

    fn prove_with_challenge(
        _params: &Self::ProverParams,
        _challenge: Self::ProverChallenge,
        _a: &[C::ScalarField], // vector
        _blind: &C::ScalarField,
        _rng: Option<&mut dyn RngCore>,
    ) -> Result<Self::Proof, Error> {
        // not supported because the prover logic computes challenges as it advances on the logic
        Err(Error::NotSupported("IPA::prove_with_challenge".to_string()))
    }

    fn verify(
        params: &Self::VerifierParams,
        transcript: &mut impl Transcript<C::ScalarField>,
        P: &C, // commitment
        proof: &Self::Proof,
    ) -> Result<(), Error> {
        let (p, _r) = (proof.0.clone(), proof.1);
        let k = p.L.len();

        transcript.absorb_nonnative(P);
        let x = transcript.get_challenge(); // challenge value at which we evaluate
        let s = transcript.get_challenge();
        let U = C::generator().mul(s);
        let mut u: Vec<C::ScalarField> = vec![C::ScalarField::zero(); k];
        for i in (0..k).rev() {
            transcript.absorb_nonnative(&p.L[i]);
            transcript.absorb_nonnative(&p.R[i]);
            u[i] = transcript.get_challenge();
        }
        let challenge = (x, U, u);

        Self::verify_with_challenge(params, challenge, P, proof)
    }

    fn verify_with_challenge(
        params: &Self::VerifierParams,
        challenge: Self::Challenge,
        P: &C, // commitment
        proof: &Self::Proof,
    ) -> Result<(), Error> {
        let (p, v, r) = (proof.0.clone(), proof.1, proof.2);
        let (x, U, u) = challenge;

        let k = p.L.len();
        if p.R.len() != k {
            return Err(Error::CommitmentVerificationFail);
        }
        if !H && (!r.is_zero()) {
            return Err(Error::BlindingNotZero);
        }
        if !H && (!p.l.is_empty() || !p.r.is_empty()) {
            return Err(Error::CommitmentVerificationFail);
        }
        if H && (p.l.len() != k || p.r.len() != k) {
            return Err(Error::CommitmentVerificationFail);
        }

        let P = *P + U.mul(v); // where v=p(x)

        let mut q_0 = P;
        let mut r = r;

        // compute u[i]^-1 once
        let mut u_invs = vec![C::ScalarField::zero(); u.len()];
        for (j, u_j) in u.iter().enumerate() {
            u_invs[j] = u_j
                .inverse()
                .ok_or(Error::Other("error on computing inverse".to_string()))?;
        }

        // compute b & G from s
        let s = build_s(&u, &u_invs, k)?;
        // b = <s, b_vec> = <s, [1, x, x^2, ..., x^d-1]>
        let b = s_b_inner(&u, &x)?;
        let d: usize = 2_u64.pow(k as u32) as usize;
        if params.generators.len() < d {
            return Err(Error::PedersenParamsLen(params.generators.len(), d));
        }
        let G = C::msm_unchecked(&params.generators, &s);

        for (j, u_j) in u.iter().enumerate() {
            let uj2 = u_j.square();
            let uj_inv2 = u_invs[j].square();

            q_0 = q_0 + p.L[j].mul(uj2) + p.R[j].mul(uj_inv2);
            if H {
                r = r + p.l[j] * uj2 + p.r[j] * uj_inv2;
            }
        }

        let q_1 = if H {
            G.mul(p.a) + params.h.mul(r) + U.mul(p.a * b)
        } else {
            G.mul(p.a) + U.mul(p.a * b)
        };

        if q_0 != q_1 {
            return Err(Error::CommitmentVerificationFail);
        }
        Ok(())
    }
}

/// Computes s such that
/// s = (
///   u₁⁻¹ u₂⁻¹ … uₖ⁻¹,
///   u₁   u₂⁻¹ … uₖ⁻¹,
///   u₁⁻¹ u₂   … uₖ⁻¹,
///   u₁   u₂   … uₖ⁻¹,
///   ⋮    ⋮      ⋮
///   u₁   u₂   … uₖ
/// )
/// Uses Halo2 approach computing $g(X) = \prod\limits_{i=0}^{k-1} (1 + u_{k - 1 - i} X^{2^i})$,
/// taking 2^{k+1}-2.
/// src: https://github.com/zcash/halo2/blob/81729eca91ba4755e247f49c3a72a4232864ec9e/halo2_proofs/src/poly/commitment/verifier.rs#L156
fn build_s<F: PrimeField>(u: &[F], u_invs: &[F], k: usize) -> Result<Vec<F>, Error> {
    let d: usize = 2_u64.pow(k as u32) as usize;
    let mut s: Vec<F> = vec![F::one(); d];
    for (len, (u_j, u_j_inv)) in u
        .iter()
        .zip(u_invs)
        .enumerate()
        .map(|(i, u_j)| (1 << i, u_j))
    {
        let (left, right) = s.split_at_mut(len);
        let right = &mut right[0..len];
        right.copy_from_slice(left);
        for s in left {
            *s *= u_j_inv;
        }
        for s in right {
            *s *= u_j;
        }
    }
    Ok(s)
}

/// Computes (in-circuit) s such that
/// s = (
///   u₁⁻¹ u₂⁻¹ … uₖ⁻¹,
///   u₁   u₂⁻¹ … uₖ⁻¹,
///   u₁⁻¹ u₂   … uₖ⁻¹,
///   u₁   u₂   … uₖ⁻¹,
///   ⋮    ⋮      ⋮
///   u₁   u₂   … uₖ
/// )
/// Uses Halo2 approach computing $g(X) = \prod\limits_{i=0}^{k-1} (1 + u_{k - 1 - i} X^{2^i})$,
/// taking 2^{k+1}-2.
/// src: https://github.com/zcash/halo2/blob/81729eca91ba4755e247f49c3a72a4232864ec9e/halo2_proofs/src/poly/commitment/verifier.rs#L156
fn build_s_gadget<F: PrimeField, CF: PrimeField>(
    u: &[EmulatedFpVar<F, CF>],
    u_invs: &[EmulatedFpVar<F, CF>],
    k: usize,
) -> Result<Vec<EmulatedFpVar<F, CF>>, SynthesisError> {
    let d: usize = 2_u64.pow(k as u32) as usize;
    let mut s: Vec<EmulatedFpVar<F, CF>> = vec![EmulatedFpVar::one(); d];
    for (len, (u_j, u_j_inv)) in u
        .iter()
        .zip(u_invs)
        .enumerate()
        .map(|(i, u_j)| (1 << i, u_j))
    {
        let (left, right) = s.split_at_mut(len);
        let right = &mut right[0..len];
        right.clone_from_slice(left);
        for s in left {
            *s *= u_j_inv;
        }
        for s in right {
            *s *= u_j;
        }
    }
    Ok(s)
}

fn inner_prod<F: PrimeField>(a: &[F], b: &[F]) -> Result<F, Error> {
    if a.len() != b.len() {
        return Err(Error::NotSameLength(
            "a".to_string(),
            a.len(),
            "b".to_string(),
            b.len(),
        ));
    }
    let c = cfg_iter!(a)
        .zip(cfg_iter!(b))
        .map(|(a_i, b_i)| *a_i * b_i)
        .sum();
    Ok(c)
}

// g(x, u_1, u_2, ..., u_k) = <s, b>, naively takes linear, but can compute in log time through
// g(x, u_1, u_2, ..., u_k) = \Prod u_i x^{2^i} + u_i^-1
fn s_b_inner<F: PrimeField>(u: &[F], x: &F) -> Result<F, Error> {
    let mut c: F = F::one();
    let mut x_2_i = *x; // x_2_i is x^{2^i}, starting from x^{2^0}=x
    for u_i in u.iter() {
        c *= (*u_i * x_2_i)
            + u_i
                .inverse()
                .ok_or(Error::Other("error on computing inverse".to_string()))?;
        x_2_i *= x_2_i;
    }
    Ok(c)
}

// g(x, u_1, u_2, ..., u_k) = <s, b>, naively takes linear, but can compute in log time through
// g(x, u_1, u_2, ..., u_k) = \Prod u_i x^{2^i} + u_i^-1
fn s_b_inner_gadget<F: PrimeField, CF: PrimeField>(
    u: &[EmulatedFpVar<F, CF>],
    x: &EmulatedFpVar<F, CF>,
) -> Result<EmulatedFpVar<F, CF>, SynthesisError> {
    let mut c: EmulatedFpVar<F, CF> = EmulatedFpVar::<F, CF>::one();
    let mut x_2_i = x.clone(); // x_2_i is x^{2^i}, starting from x^{2^0}=x
    for u_i in u.iter() {
        c *= u_i.clone() * x_2_i.clone() + u_i.inverse()?;
        x_2_i *= x_2_i.clone();
    }
    Ok(c)
}

pub struct ProofVar<C: Curve> {
    a: EmulatedFpVar<C::ScalarField, CF2<C>>,
    l: Vec<EmulatedFpVar<C::ScalarField, CF2<C>>>,
    r: Vec<EmulatedFpVar<C::ScalarField, CF2<C>>>,
    L: Vec<C::Var>,
    R: Vec<C::Var>,
}
impl<C: Curve> AllocVar<Proof<C>, CF2<C>> for ProofVar<C> {
    fn new_variable<T: Borrow<Proof<C>>>(
        cs: impl Into<Namespace<CF2<C>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|val| {
            let cs = cs.into();

            let a = EmulatedFpVar::<C::ScalarField, CF2<C>>::new_variable(
                cs.clone(),
                || Ok(val.borrow().a),
                mode,
            )?;
            let l: Vec<EmulatedFpVar<C::ScalarField, CF2<C>>> =
                Vec::new_variable(cs.clone(), || Ok(val.borrow().l.clone()), mode)?;
            let r: Vec<EmulatedFpVar<C::ScalarField, CF2<C>>> =
                Vec::new_variable(cs.clone(), || Ok(val.borrow().r.clone()), mode)?;
            let L: Vec<C::Var> =
                Vec::new_variable(cs.clone(), || Ok(val.borrow().L.clone()), mode)?;
            let R: Vec<C::Var> =
                Vec::new_variable(cs.clone(), || Ok(val.borrow().R.clone()), mode)?;

            Ok(Self { a, l, r, L, R })
        })
    }
}

/// IPAGadget implements the circuit that verifies an IPA Proof. The `H` parameter indicates if to
/// use the commitment in hiding mode or not, reducing a bit the number of constraints needed in
/// the later case.
pub struct IPAGadget<C: Curve, const H: bool = false> {
    _c: PhantomData<C>,
}

impl<C: Curve, const H: bool> IPAGadget<C, H> {
    /// Verify the IPA opening proof, K=log2(d), where d is the degree of the committed polynomial,
    /// and H indicates if the commitment is in hiding mode and thus uses blinding factors, if not,
    /// there are some constraints saved.
    #[allow(clippy::too_many_arguments)]
    pub fn verify<const K: usize>(
        g: &[C::Var],                              // params.generators
        h: &C::Var,                                // params.h
        x: &EmulatedFpVar<C::ScalarField, CF2<C>>, // evaluation point, challenge
        v: &EmulatedFpVar<C::ScalarField, CF2<C>>, // value at evaluation point
        P: &C::Var,                                // commitment
        p: &ProofVar<C>,
        r: &EmulatedFpVar<C::ScalarField, CF2<C>>, // blinding factor
        u: &[EmulatedFpVar<C::ScalarField, CF2<C>>; K], // challenges
        U: &C::Var,                                // challenge
    ) -> Result<Boolean<CF2<C>>, SynthesisError> {
        if p.L.len() != K || p.R.len() != K {
            return Err(SynthesisError::Unsatisfiable);
        }

        let P_ = U.scalar_mul_le(v.to_bits_le()?.iter())? + P;
        let mut q_0 = P_;
        let mut r = r.clone();

        // compute u[i]^-1 once
        let mut u_invs = vec![EmulatedFpVar::<C::ScalarField, CF2<C>>::zero(); u.len()];
        for (j, u_j) in u.iter().enumerate() {
            u_invs[j] = u_j.inverse()?;
        }

        // compute b & G from s
        let s = build_s_gadget(u, &u_invs, K)?;
        // b = <s, b_vec> = <s, [1, x, x^2, ..., x^K-1]>
        let b = s_b_inner_gadget(u, x)?;
        // ensure that generators.len() === s.len():
        if g.len() < K {
            return Err(SynthesisError::Unsatisfiable);
        }

        // msm: G=<G, s>
        let mut G = C::Var::zero();
        for (i, s_i) in s.iter().enumerate() {
            G += g[i].scalar_mul_le(s_i.to_bits_le()?.iter())?;
        }

        for (j, u_j) in u.iter().enumerate() {
            let uj2 = u_j.square()?;
            let uj_inv2 = u_invs[j].square()?; // cheaper square than inversing the uj2

            q_0 = q_0
                + p.L[j].scalar_mul_le(uj2.to_bits_le()?.iter())?
                + p.R[j].scalar_mul_le(uj_inv2.to_bits_le()?.iter())?;
            if H {
                r = r + &p.l[j] * &uj2 + &p.r[j] * &uj_inv2;
            }
        }

        let q_1 = if H {
            G.scalar_mul_le(p.a.to_bits_le()?.iter())?
                + h.scalar_mul_le(r.to_bits_le()?.iter())?
                + U.scalar_mul_le((p.a.clone() * b).to_bits_le()?.iter())?
        } else {
            G.scalar_mul_le(p.a.to_bits_le()?.iter())?
                + U.scalar_mul_le((p.a.clone() * b).to_bits_le()?.iter())?
        };
        // q_0 == q_1
        q_0.is_eq(&q_1)
    }
}

#[cfg(test)]
mod tests {
    use ark_crypto_primitives::sponge::{poseidon::PoseidonSponge, CryptographicSponge};
    use ark_ec::PrimeGroup;
    use ark_pallas::{constraints::GVar, Fq, Fr, Projective};
    use ark_r1cs_std::eq::EqGadget;
    use ark_relations::r1cs::ConstraintSystem;

    use super::*;
    use crate::transcript::poseidon::poseidon_canonical_config;

    #[test]
    fn test_ipa() -> Result<(), Error> {
        let _ = test_ipa_opt::<false>()?;
        let _ = test_ipa_opt::<true>()?;
        Ok(())
    }
    fn test_ipa_opt<const hiding: bool>() -> Result<(), Error> {
        let mut rng = ark_std::test_rng();

        const k: usize = 4;
        const d: usize = 2_u64.pow(k as u32) as usize;

        // setup params
        let (params, _) = IPA::<Projective, hiding>::setup(&mut rng, d)?;

        let poseidon_config = poseidon_canonical_config::<Fr>();
        // init Prover's transcript
        let mut transcript_p = PoseidonSponge::<Fr>::new(&poseidon_config);
        // init Verifier's transcript
        let mut transcript_v = PoseidonSponge::<Fr>::new(&poseidon_config);

        // a is the vector that we're committing
        let a: Vec<Fr> = std::iter::repeat_with(|| Fr::rand(&mut rng))
            .take(d)
            .collect();
        let r_blind: Fr = if hiding {
            Fr::rand(&mut rng)
        } else {
            Fr::zero()
        };
        let cm = IPA::<Projective, hiding>::commit(&params, &a, &r_blind)?;

        let proof = IPA::<Projective, hiding>::prove(
            &params,
            &mut transcript_p,
            &cm,
            &a,
            &r_blind,
            Some(&mut rng),
        )?;

        IPA::<Projective, hiding>::verify(&params, &mut transcript_v, &cm, &proof)?;
        Ok(())
    }

    #[test]
    fn test_ipa_gadget() -> Result<(), Error> {
        let _ = test_ipa_gadget_opt::<false>()?;
        let _ = test_ipa_gadget_opt::<true>()?;
        Ok(())
    }
    fn test_ipa_gadget_opt<const hiding: bool>() -> Result<(), Error> {
        let mut rng = ark_std::test_rng();

        const k: usize = 3;
        const d: usize = 2_u64.pow(k as u32) as usize;

        // setup params
        let (params, _) = IPA::<Projective, hiding>::setup(&mut rng, d)?;

        let poseidon_config = poseidon_canonical_config::<Fr>();
        // init Prover's transcript
        let mut transcript_p = PoseidonSponge::<Fr>::new(&poseidon_config);
        // init Verifier's transcript
        let mut transcript_v = PoseidonSponge::<Fr>::new(&poseidon_config);

        let mut a: Vec<Fr> = std::iter::repeat_with(|| Fr::rand(&mut rng))
            .take(d / 2)
            .collect();
        a.extend(vec![Fr::zero(); d / 2]);
        let r_blind: Fr = if hiding {
            Fr::rand(&mut rng)
        } else {
            Fr::zero()
        };
        let cm = IPA::<Projective, hiding>::commit(&params, &a, &r_blind)?;

        let proof = IPA::<Projective, hiding>::prove(
            &params,
            &mut transcript_p,
            &cm,
            &a,
            &r_blind,
            Some(&mut rng),
        )?;

        IPA::<Projective, hiding>::verify(&params, &mut transcript_v, &cm, &proof)?;

        // circuit
        let cs = ConstraintSystem::<Fq>::new_ref();

        let mut transcript_v = PoseidonSponge::<Fr>::new(&poseidon_config);
        transcript_v.absorb_nonnative(&cm);
        let challenge = transcript_v.get_challenge(); // challenge value at which we evaluate
        let s = transcript_v.get_challenge();
        let U = Projective::generator() * s;
        let mut u: Vec<Fr> = vec![Fr::zero(); k];
        for i in (0..k).rev() {
            transcript_v.absorb_nonnative(&proof.0.L[i]);
            transcript_v.absorb_nonnative(&proof.0.R[i]);
            u[i] = transcript_v.get_challenge();
        }

        // prepare inputs
        let gVar = Vec::<GVar>::new_constant(cs.clone(), params.generators)?;
        let hVar = GVar::new_constant(cs.clone(), params.h)?;
        let challengeVar = EmulatedFpVar::<Fr, Fq>::new_witness(cs.clone(), || Ok(challenge))?;
        let vVar = EmulatedFpVar::<Fr, Fq>::new_witness(cs.clone(), || Ok(proof.1))?;
        let cmVar = GVar::new_witness(cs.clone(), || Ok(cm))?;
        let proofVar = ProofVar::<Projective>::new_witness(cs.clone(), || Ok(proof.0))?;
        let r_blindVar = EmulatedFpVar::<Fr, Fq>::new_witness(cs.clone(), || Ok(r_blind))?;
        let uVar_vec = Vec::<EmulatedFpVar<Fr, Fq>>::new_witness(cs.clone(), || Ok(u))?;
        let uVar: [EmulatedFpVar<Fr, Fq>; k] = uVar_vec.try_into().map_err(|_| {
            Error::ConversionError(
                "Vec<_>".to_string(),
                "[_; 1]".to_string(),
                "variable name: uVar".to_string(),
            )
        })?;
        let UVar = GVar::new_witness(cs.clone(), || Ok(U))?;

        let v = IPAGadget::<Projective, hiding>::verify::<k>(
            &gVar,
            &hVar,
            &challengeVar,
            &vVar,
            &cmVar,
            &proofVar,
            &r_blindVar,
            &uVar,
            &UVar,
        )?;
        v.enforce_equal(&Boolean::TRUE)?;
        assert!(cs.is_satisfied()?);
        Ok(())
    }
}
