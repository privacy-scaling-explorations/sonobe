/// IPA implements the modified Inner Product Argument described in
/// [Halo](https://eprint.iacr.org/2019/1021.pdf). The variable names used follow the paper
/// notation in order to make it more readable.
///
/// The implementation does the following optimizations in order to reduce the amount of
/// constraints in the circuit:
/// i. <s, b> computation is done in log time following a modification of the equation 3 in section
/// 3.2 from the paper.
/// ii. s computation is done in k*(2^k)/2 instead of k*2^k by taking advantadge of the symmetric
/// nature of s.
/// iii. verifier delegates the computation of u_i^-1 to the prover, just checking that
/// u_i*u_i^-1==1 in circuit.
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{Field, PrimeField};
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    boolean::Boolean,
    eq::EqGadget,
    fields::{nonnative::NonNativeFieldVar, FieldVar},
    groups::GroupOpsBounds,
    prelude::CurveVar,
    ToBitsGadget,
};
use ark_relations::r1cs::{Namespace, SynthesisError};
use ark_std::{rand::Rng, One, UniformRand, Zero};
use core::{borrow::Borrow, marker::PhantomData};

use super::pedersen::Params as PedersenParams;
use crate::transcript::{Transcript, TranscriptVar};
use crate::utils::espresso::virtual_polynomial::bit_decompose;
use crate::utils::vec::{vec_add, vec_scalar_mul};
use crate::Error;

// IPA implements the Inner Product Argument protocol.
pub struct IPA<const BLIND: bool, C: CurveGroup> {
    _c: PhantomData<C>,
}

pub struct Proof<C: CurveGroup> {
    a: C::ScalarField,
    l: Vec<C::ScalarField>,
    r: Vec<C::ScalarField>,
    L: Vec<C>,
    R: Vec<C>,
    u_invs: Vec<C::ScalarField>, // {u_i^-1} \forall k
}

impl<const BLIND: bool, C: CurveGroup> IPA<BLIND, C> {
    pub fn new_params<R: Rng>(rng: &mut R, max: usize) -> PedersenParams<C> {
        let generators: Vec<C::Affine> = std::iter::repeat_with(|| C::Affine::rand(rng))
            .take(max.next_power_of_two())
            .collect();
        let params = PedersenParams::<C> {
            h: C::rand(rng),
            generators,
        };
        params
    }
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
        if !BLIND {
            return Ok(C::msm_unchecked(&params.generators[..a.len()], a));
        }
        Ok(params.h.mul(r) + C::msm_unchecked(&params.generators[..a.len()], a))
    }

    pub fn prove<R: Rng>(
        rng: &mut R,
        params: &PedersenParams<C>,
        transcript: &mut impl Transcript<C>,
        P: &C, // commitment
        a: &[C::ScalarField],
        x: &C::ScalarField,
    ) -> Result<Proof<C>, Error> {
        if !a.len().is_power_of_two() {
            return Err(Error::NotPowerOfTwo("a".to_string(), a.len()));
        }
        let d = a.len();
        let k = (f64::from(d as u32).log2()) as usize;

        if params.generators.len() < a.len() {
            return Err(Error::PedersenParamsLen(params.generators.len(), a.len()));
        }
        // blinding factors
        // let mut l: Vec<C::ScalarField> = vec![C::ScalarField::zero(); k];
        // let mut r: Vec<C::ScalarField> = vec![C::ScalarField::zero(); k];
        let l: Vec<C::ScalarField>; // = Vec::new();
        let r: Vec<C::ScalarField>; // = Vec::new();
        if BLIND {
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

        transcript.absorb_point(&P)?;
        let s = transcript.get_challenge();
        let U = C::generator().mul(s);

        let mut a = a.to_owned();
        let mut b = powers_of(*x, d);
        let mut G = params.generators.clone();

        let mut L: Vec<C> = vec![C::zero(); k];
        let mut R: Vec<C> = vec![C::zero(); k];

        // u challenges
        let mut u: Vec<C::ScalarField> = vec![C::ScalarField::zero(); k];
        let mut u_invs: Vec<C::ScalarField> = vec![C::ScalarField::zero(); k];
        for j in (0..k).rev() {
            let m = a.len() / 2;
            let a_lo = a[..m].to_vec();
            let a_hi = a[m..].to_vec();
            let b_lo = b[..m].to_vec();
            let b_hi = b[m..].to_vec();
            let G_lo = G[..m].to_vec();
            let G_hi = G[m..].to_vec();

            if BLIND {
                L[j] = C::msm_unchecked(&G_hi, &a_lo)
                    + params.h.mul(l[j])
                    + U.mul(inner_prod(&a_lo, &b_hi)?);
                R[j] = C::msm_unchecked(&G_lo, &a_hi)
                    + params.h.mul(r[j])
                    + U.mul(inner_prod(&a_hi, &b_lo)?);
            } else {
                L[j] = C::msm_unchecked(&G_hi, &a_lo) + U.mul(inner_prod(&a_lo, &b_hi)?);
                R[j] = C::msm_unchecked(&G_lo, &a_hi) + U.mul(inner_prod(&a_hi, &b_lo)?);
            }
            // get challenge for the j-th round
            transcript.absorb_point(&L[j])?;
            transcript.absorb_point(&R[j])?;
            u[j] = transcript.get_challenge();

            let uj = u[j];
            let uj_inv = u[j]
                .inverse()
                .ok_or(Error::Other("error on computing inverse".to_string()))?;
            u_invs[j] = uj_inv.clone();

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
            l: l.clone(),
            r: r.clone(),
            L,
            R,
            u_invs,
        })
    }

    pub fn verify(
        params: &PedersenParams<C>,
        transcript: &mut impl Transcript<C>,
        x: &C::ScalarField, // evaluation point
        v: &C::ScalarField, // value at evaluation point
        P: &C,              // commitment
        p: &Proof<C>,
        r: &C::ScalarField, // blinding factor
        k: usize,           // k = log2(d), where d is the degree of the committed polynomial
    ) -> Result<bool, Error> {
        if !BLIND && (p.l.len() != 0 || p.r.len() != 0) {
            return Err(Error::CommitmentVerificationFail);
        }
        if BLIND && (p.l.len() != k || p.r.len() != k) {
            return Err(Error::CommitmentVerificationFail);
        }
        if p.L.len() != k || p.R.len() != k || p.u_invs.len() != k {
            return Err(Error::CommitmentVerificationFail);
        }

        // absorbs & get challenges
        transcript.absorb_point(&P)?;
        let s = transcript.get_challenge();
        let U = C::generator().mul(s);
        let mut u: Vec<C::ScalarField> = vec![C::ScalarField::zero(); k];
        for i in (0..k).rev() {
            transcript.absorb_point(&p.L[i])?;
            transcript.absorb_point(&p.R[i])?;
            u[i] = transcript.get_challenge();
        }

        let P = *P + U.mul(v);

        let mut q_0 = P;
        let mut r = *r;

        // check correctnes of the u_invs delegated to the prover
        for j in 0..k {
            if u[j].clone() * p.u_invs[j].clone() != C::ScalarField::one() {
                return Err(Error::CommitmentVerificationFail);
            }
        }

        // compute b & G from s
        let s = build_s(&u, &p.u_invs, k)?;
        // b = <s, b_vec> = <s, [1, x, x^2, ..., x^d-1]>
        let b = s_b_inner(&u, x)?;
        let d: usize = 2_u64.pow(k as u32) as usize;
        if params.generators.len() < d {
            return Err(Error::PedersenParamsLen(params.generators.len(), d));
        }
        let G = C::msm_unchecked(&params.generators, &s);

        for j in 0..k {
            let uj2 = u[j].square();
            let uj_inv2 = p.u_invs[j].square();

            q_0 = q_0 + p.L[j].mul(uj2) + p.R[j].mul(uj_inv2);
            if BLIND {
                r = r + p.l[j] * uj2 + p.r[j] * uj_inv2;
            }
        }

        let q_1;
        if BLIND {
            q_1 = G.mul(p.a) + params.h.mul(r) + U.mul(p.a * b);
        } else {
            q_1 = G.mul(p.a) + U.mul(p.a * b);
        }

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
// naively would take k * d = k * 2^k time, with the current approach taking advantadge of the
// symmetric nature of s, it takes k * d/2 = k * (2^k)/2 = k * 2^{k-1} time.
fn build_s<F: PrimeField>(u: &[F], u_invs: &[F], k: usize) -> Result<Vec<F>, Error> {
    let d: usize = 2_u64.pow(k as u32) as usize;
    let mut s: Vec<F> = vec![F::one(); d];
    for i in 0..d / 2 {
        let i_bits = bit_decompose(i as u64, k);
        for j in 0..k {
            if i_bits[j] {
                s[i] *= u[j].clone();
            } else {
                s[i] *= u_invs[j].clone();
            }
        }

        // now place the inverse to the other side following the symmetric structure of s
        s[d - 1 - i] = s[i]
            .inverse()
            .ok_or(Error::Other("error on computing inverse".to_string()))?;
    }
    Ok(s)
}
fn build_s_gadget<F: PrimeField, CF: PrimeField>(
    u: &[NonNativeFieldVar<F, CF>],
    // u_invs are assumed have their correctness checked in higher levels of the circuit logic
    u_invs: &[NonNativeFieldVar<F, CF>],
    k: usize,
) -> Result<Vec<NonNativeFieldVar<F, CF>>, SynthesisError> {
    let d: usize = 2_u64.pow(k as u32) as usize;
    let mut s: Vec<NonNativeFieldVar<F, CF>> = vec![NonNativeFieldVar::one(); d];
    for i in 0..d / 2 {
        let i_bits = bit_decompose(i as u64, k);
        for j in 0..k {
            if i_bits[j] {
                s[i] *= u[j].clone();
            } else {
                s[i] *= u_invs[j].clone();
            }
        }

        // now place the inverse to the other side
        s[d - 1 - i] = s[i].inverse()?;
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
    let mut c: F = F::zero();
    for i in 0..a.len() {
        c += a[i] * b[i];
    }
    Ok(c)
}

// g(x, u_1, u_2, ..., u_k) = <s, b>, naively takes linear, but can compute in log time through
// g(x, u_1, u_2, ..., u_k) = (\Prod u_i x^{2^i} + u_i^-1) * x
fn s_b_inner<F: PrimeField>(u: &[F], x: &F) -> Result<F, Error> {
    let k = u.len();
    let mut c: F = F::one();
    let mut x_2_i = x.clone(); // x_2_i is x^{2^i}, starting from x^{2^0}=x
    for i in 0..k {
        c *= (u[i].clone() * x_2_i.clone())
            + u[i]
                .inverse()
                .ok_or(Error::Other("error on computing inverse".to_string()))?;
        x_2_i *= x_2_i.clone();
    }
    Ok(c * x.clone())
}

// g(x, u_1, u_2, ..., u_k) = <s, b>, naively takes linear, but can compute in log time through
// g(x, u_1, u_2, ..., u_k) = (\Prod u_i x^{2^i} + u_i^-1) * x
fn s_b_inner_gadget<F: PrimeField, CF: PrimeField>(
    u: &[NonNativeFieldVar<F, CF>],
    x: &NonNativeFieldVar<F, CF>,
) -> Result<NonNativeFieldVar<F, CF>, SynthesisError> {
    let k = u.len();
    let mut c: NonNativeFieldVar<F, CF> = NonNativeFieldVar::<F, CF>::one();
    let mut x_2_i = x.clone(); // x_2_i is x^{2^i}, starting from x^{2^0}=x
    for i in 0..k {
        c *= u[i].clone() * x_2_i.clone() + u[i].inverse()?;
        x_2_i *= x_2_i.clone();
    }
    Ok(c * x.clone())
}

fn powers_of<F: PrimeField>(x: F, n: usize) -> Vec<F> {
    let mut c: Vec<F> = vec![F::zero(); n];
    c[0] = x;
    for i in 1..n {
        c[i] = c[i - 1] * x;
    }
    c
}

pub type CF<C> = <<C as CurveGroup>::BaseField as Field>::BasePrimeField;

pub struct ProofVar<C: CurveGroup, GC: CurveVar<C, CF<C>>> {
    a: NonNativeFieldVar<C::ScalarField, CF<C>>,
    l: Vec<NonNativeFieldVar<C::ScalarField, CF<C>>>,
    r: Vec<NonNativeFieldVar<C::ScalarField, CF<C>>>,
    L: Vec<GC>,
    R: Vec<GC>,
    u_invs: Vec<NonNativeFieldVar<C::ScalarField, CF<C>>>,
}
impl<C, GC> AllocVar<Proof<C>, CF<C>> for ProofVar<C, GC>
where
    C: CurveGroup,
    GC: CurveVar<C, CF<C>>,
    <C as ark_ec::CurveGroup>::BaseField: PrimeField,
{
    fn new_variable<T: Borrow<Proof<C>>>(
        cs: impl Into<Namespace<CF<C>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|val| {
            let cs = cs.into();

            let a = NonNativeFieldVar::<C::ScalarField, CF<C>>::new_variable(
                cs.clone(),
                || Ok(val.borrow().a),
                mode,
            )?;
            let l: Vec<NonNativeFieldVar<C::ScalarField, CF<C>>> =
                Vec::new_variable(cs.clone(), || Ok(val.borrow().l.clone()), mode)?;
            let r: Vec<NonNativeFieldVar<C::ScalarField, CF<C>>> =
                Vec::new_variable(cs.clone(), || Ok(val.borrow().r.clone()), mode)?;
            let L: Vec<GC> = Vec::new_variable(cs.clone(), || Ok(val.borrow().L.clone()), mode)?;
            let R: Vec<GC> = Vec::new_variable(cs.clone(), || Ok(val.borrow().R.clone()), mode)?;
            let u_invs: Vec<NonNativeFieldVar<C::ScalarField, CF<C>>> =
                Vec::new_variable(cs.clone(), || Ok(val.borrow().u_invs.clone()), mode)?;

            Ok(Self {
                a,
                l,
                r,
                L,
                R,
                u_invs,
            })
        })
    }
}

pub struct IPAGadget<C, GC>
where
    C: CurveGroup,
    GC: CurveVar<C, CF<C>>,
{
    _cf: PhantomData<CF<C>>,
    _c: PhantomData<C>,
    _gc: PhantomData<GC>,
}

impl<C, GC> IPAGadget<C, GC>
where
    C: CurveGroup,
    GC: CurveVar<C, CF<C>>,

    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
    for<'a> &'a GC: GroupOpsBounds<'a, C, GC>,
{
    /// verify the IPA opening proof, K=log2(d), where d is the degree of the committed polynomial,
    /// and BLIND indicates if the commitment uses blinding factors, if not, there are some
    /// constraints saved.
    pub fn verify<const K: usize, const BLIND: bool>(
        // transcript: &impl TranscriptVar<CF<C>>,
        g: &Vec<GC>,                                  // parms.generators
        h: &GC,                                       // parms.h
        x: &NonNativeFieldVar<C::ScalarField, CF<C>>, // evaluation point
        v: &NonNativeFieldVar<C::ScalarField, CF<C>>, // value at evaluation point
        P: &GC,                                       // commitment
        p: &ProofVar<C, GC>,
        r: &NonNativeFieldVar<C::ScalarField, CF<C>>, // blinding factor
        u: &[NonNativeFieldVar<C::ScalarField, CF<C>>; K], // challenges
        U: &GC,                                       // challenge
    ) -> Result<Boolean<CF<C>>, SynthesisError> {
        // transcript.absorb_point(&P)?;
        // let u = transcript.get_challenges(K)?;
        // let s = transcript.get_challenge()?;
        // let U = GC::generator().scalar_mul_le(s.to_bits_le()?.iter());

        let P_ = P + U.scalar_mul_le(v.to_bits_le()?.iter())?;
        let mut q_0 = P_;
        let mut r = r.clone();

        // check correctnes of the u_invs delegated to the prover
        for j in 0..K {
            (u[j].clone() * p.u_invs[j].clone()).enforce_equal(&NonNativeFieldVar::one())?;
        }

        // compute b & G from s
        // let d: usize = 2_u64.pow(K as u32) as usize;
        let s = build_s_gadget(u, &p.u_invs, K)?;
        // b = <s, b_vec> = <s, [1, x, x^2, ..., x^K-1]>
        let b = s_b_inner_gadget(u, x)?;
        // ensure that generators.len() === s.len():
        if g.len() < K {
            return Err(SynthesisError::Unsatisfiable);
        }

        // msm: G=<G, s>
        let mut G = GC::zero();
        for (i, s_i) in s.iter().enumerate() {
            G += g[i].scalar_mul_le(s_i.to_bits_le()?.iter())?;
        }

        for j in 0..K {
            let uj2 = u[j].square()?;
            let uj_inv2 = p.u_invs[j].square()?; // cheaper square than inversing the uj2

            q_0 = q_0
                + p.L[j].scalar_mul_le(uj2.to_bits_le()?.iter())?
                + p.R[j].scalar_mul_le(uj_inv2.to_bits_le()?.iter())?;
            if BLIND {
                r = r + &p.l[j] * &uj2 + &p.r[j] * &uj_inv2;
            }
        }

        let q_1;
        if BLIND {
            q_1 = G.scalar_mul_le(p.a.to_bits_le()?.iter())?
                + h.scalar_mul_le(r.to_bits_le()?.iter())?
                + U.scalar_mul_le((p.a.clone() * b).to_bits_le()?.iter())?;
        } else {
            q_1 = G.scalar_mul_le(p.a.to_bits_le()?.iter())?
                + U.scalar_mul_le((p.a.clone() * b).to_bits_le()?.iter())?;
        }
        // q_0 == q_1
        Ok(q_0.is_eq(&q_1)?)
    }
}

#[cfg(test)]
mod tests {
    use ark_pallas::{constraints::GVar, Fq, Fr, Projective};
    use ark_r1cs_std::{alloc::AllocVar, bits::boolean::Boolean, eq::EqGadget};
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::UniformRand;

    use super::*;
    use crate::commitment::pedersen::Pedersen;
    use crate::transcript::poseidon::{
        poseidon_test_config, PoseidonTranscript, PoseidonTranscriptVar,
    };

    #[test]
    fn test_ipa() {
        test_ipa_opt::<false>();
        test_ipa_opt::<true>();
    }
    fn test_ipa_opt<const blind: bool>() {
        let mut rng = ark_std::test_rng();

        const k: usize = 4;
        const d: usize = 2_u64.pow(k as u32) as usize;

        // setup params
        let params = IPA::<blind, Projective>::new_params(&mut rng, d);

        let poseidon_config = poseidon_test_config::<Fr>();
        // init Prover's transcript
        let mut transcript_p = PoseidonTranscript::<Projective>::new(&poseidon_config);
        // init Verifier's transcript
        let mut transcript_v = PoseidonTranscript::<Projective>::new(&poseidon_config);

        let a: Vec<Fr> = std::iter::repeat_with(|| Fr::rand(&mut rng))
            .take(d)
            .collect();
        let r_blind: Fr = Fr::rand(&mut rng);
        let cm = IPA::<blind, Projective>::commit(&params, &a, &r_blind).unwrap();

        // evaluation point
        let x = Fr::rand(&mut rng);

        let proof =
            IPA::<blind, Projective>::prove(&mut rng, &params, &mut transcript_p, &cm, &a, &x)
                .unwrap();

        let b = powers_of(x, d); // WIP
        let v = inner_prod(&a, &b).unwrap(); // WIP
        assert!(IPA::<blind, Projective>::verify(
            &params,
            &mut transcript_v,
            &x,
            &v,
            &cm,
            &proof,
            &r_blind,
            k,
        )
        .unwrap());
    }

    #[test]
    fn test_ipa_gadget() {
        test_ipa_gadget_opt::<false>();
        test_ipa_gadget_opt::<true>();
    }
    fn test_ipa_gadget_opt<const blind: bool>() {
        let mut rng = ark_std::test_rng();

        const k: usize = 4;
        const d: usize = 2_u64.pow(k as u32) as usize;

        // setup params
        let params = IPA::<blind, Projective>::new_params(&mut rng, d);

        let poseidon_config = poseidon_test_config::<Fr>();
        // init Prover's transcript
        let mut transcript_p = PoseidonTranscript::<Projective>::new(&poseidon_config);
        // init Verifier's transcript
        let mut transcript_v = PoseidonTranscript::<Projective>::new(&poseidon_config);

        let mut a: Vec<Fr> = std::iter::repeat_with(|| Fr::rand(&mut rng))
            .take(d / 2)
            .collect();
        a.extend(vec![Fr::zero(); d / 2]);
        let r_blind: Fr = Fr::rand(&mut rng);
        let cm = IPA::<blind, Projective>::commit(&params, &a, &r_blind).unwrap();

        // evaluation point
        let x = Fr::rand(&mut rng);

        let proof =
            IPA::<blind, Projective>::prove(&mut rng, &params, &mut transcript_p, &cm, &a, &x)
                .unwrap();

        let b = powers_of(x, d); // WIP
        let v = inner_prod(&a, &b).unwrap(); // WIP
        assert!(IPA::<blind, Projective>::verify(
            &params,
            &mut transcript_v,
            &x,
            &v,
            &cm,
            &proof,
            &r_blind,
            k,
        )
        .unwrap());

        // circuit
        let cs = ConstraintSystem::<Fq>::new_ref();

        // TODO incircuit
        let mut transcript_v = PoseidonTranscript::<Projective>::new(&poseidon_config);
        use ark_ec::Group;
        use std::ops::Mul;
        transcript_v.absorb_point(&cm).unwrap();
        let s = transcript_v.get_challenge();
        let U = Projective::generator().mul(s);
        let mut u: Vec<Fr> = vec![Fr::zero(); k];
        for i in (0..k).rev() {
            transcript_v.absorb_point(&proof.L[i]).unwrap();
            transcript_v.absorb_point(&proof.R[i]).unwrap();
            u[i] = transcript_v.get_challenge();
        }

        // prepare inputs
        // let mut transcriptVar = PoseidonTranscriptVar::<Fq>::new(cs.clone(), &poseidon_config);
        let gVar = Vec::<GVar>::new_constant(cs.clone(), params.generators).unwrap();
        let hVar = GVar::new_constant(cs.clone(), params.h).unwrap();
        let xVar = NonNativeFieldVar::<Fr, Fq>::new_witness(cs.clone(), || Ok(x)).unwrap();
        let vVar = NonNativeFieldVar::<Fr, Fq>::new_witness(cs.clone(), || Ok(v)).unwrap();
        let cmVar = GVar::new_witness(cs.clone(), || Ok(cm)).unwrap();
        let proofVar = ProofVar::<Projective, GVar>::new_witness(cs.clone(), || Ok(proof)).unwrap();
        let r_blindVar =
            NonNativeFieldVar::<Fr, Fq>::new_witness(cs.clone(), || Ok(r_blind)).unwrap();
        let uVar_vec = Vec::<NonNativeFieldVar<Fr, Fq>>::new_witness(cs.clone(), || Ok(u)).unwrap();
        let uVar: [NonNativeFieldVar<Fr, Fq>; k] = uVar_vec.try_into().unwrap();
        let UVar = GVar::new_witness(cs.clone(), || Ok(U)).unwrap();

        let v = IPAGadget::<Projective, GVar>::verify::<k, blind>(
            // &mut transcriptVar,
            &gVar,
            &hVar,
            &xVar,
            &vVar,
            &cmVar,
            &proofVar,
            &r_blindVar,
            &uVar,
            &UVar,
        )
        .unwrap();
        v.enforce_equal(&Boolean::TRUE).unwrap();
        dbg!(cs.num_constraints());
        assert!(cs.is_satisfied().unwrap());
    }
}
