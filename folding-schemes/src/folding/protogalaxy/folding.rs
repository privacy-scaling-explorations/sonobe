/// Implements the scheme described in [ProtoGalaxy](https://eprint.iacr.org/2023/1106.pdf)
use ark_crypto_primitives::sponge::Absorb;
use ark_ec::{CurveGroup, Group};
use ark_ff::PrimeField;
use ark_poly::{
    univariate::{DensePolynomial, SparsePolynomial},
    DenseUVPolynomial, EvaluationDomain, Evaluations, GeneralEvaluationDomain, Polynomial,
};
use ark_std::{cfg_into_iter, log2, One, Zero};
use rayon::prelude::*;
use std::marker::PhantomData;

use super::utils::{all_powers, betas_star, exponential_powers, pow_i};
use super::ProtoGalaxyError;
use super::{CommittedInstance, Witness};

use crate::arith::r1cs::R1CS;
use crate::transcript::Transcript;
use crate::utils::vec::*;
use crate::Error;

#[derive(Clone, Debug)]
/// Implements the protocol described in section 4 of
/// [ProtoGalaxy](https://eprint.iacr.org/2023/1106.pdf)
pub struct Folding<C: CurveGroup> {
    _phantom: PhantomData<C>,
}
impl<C: CurveGroup> Folding<C>
where
    <C as Group>::ScalarField: Absorb,
    <C as CurveGroup>::BaseField: Absorb,
{
    #![allow(clippy::type_complexity)]
    /// implements the non-interactive Prover from the folding scheme described in section 4
    pub fn prove(
        transcript: &mut impl Transcript<C::ScalarField>,
        r1cs: &R1CS<C::ScalarField>,
        // running instance
        instance: &CommittedInstance<C, true>,
        w: &Witness<C::ScalarField>,
        // incoming instances
        vec_instances: &[CommittedInstance<C, false>],
        vec_w: &[Witness<C::ScalarField>],
    ) -> Result<
        (
            CommittedInstance<C, true>,
            Witness<C::ScalarField>,
            Vec<C::ScalarField>, // F_X coeffs
            Vec<C::ScalarField>, // K_X coeffs
            Vec<C::ScalarField>, // L_X evals
            Vec<C>,              // phi_stars
        ),
        Error,
    > {
        if vec_instances.len() != vec_w.len() {
            return Err(Error::NotSameLength(
                "vec_instances.len()".to_string(),
                vec_instances.len(),
                "vec_w.len()".to_string(),
                vec_w.len(),
            ));
        }
        let d = 2; // for the moment hardcoded to 2 since it only supports R1CS
        let k = vec_instances.len();
        let t = instance.betas.len();
        let n = r1cs.A.n_cols;
        let m = r1cs.A.n_rows;

        let z = [vec![C::ScalarField::one()], instance.x.clone(), w.w.clone()].concat();

        if z.len() != n {
            return Err(Error::NotSameLength(
                "z.len()".to_string(),
                z.len(),
                "number of variables in R1CS".to_string(), // hardcoded to R1CS
                n,
            ));
        }
        if log2(m) as usize != t {
            return Err(Error::NotSameLength(
                "log2(number of constraints in R1CS)".to_string(),
                log2(m) as usize,
                "instance.betas.len()".to_string(),
                t,
            ));
        }
        if !(k + 1).is_power_of_two() {
            return Err(Error::ProtoGalaxy(ProtoGalaxyError::WrongNumInstances(k)));
        }

        // absorb the committed instances
        transcript.absorb(instance);
        transcript.absorb(&vec_instances);

        let delta = transcript.get_challenge();
        let deltas = exponential_powers(delta, t);

        let mut f_z = r1cs.eval_at_z(&z)?;
        if f_z.len() != m {
            return Err(Error::NotSameLength(
                "number of constraints in R1CS".to_string(),
                m,
                "f_z.len()".to_string(),
                f_z.len(),
            ));
        }
        f_z.resize(1 << t, C::ScalarField::zero());

        // F(X)
        let F_X: SparsePolynomial<C::ScalarField> =
            calc_f_from_btree(&f_z, &instance.betas, &deltas).expect("Error calculating F[x]");
        let F_X_dense = DensePolynomial::from(F_X.clone());
        let mut F_coeffs = F_X_dense.coeffs;
        F_coeffs.resize(t, C::ScalarField::zero());
        transcript.absorb(&F_coeffs);

        let alpha = transcript.get_challenge();

        // eval F(alpha)
        let F_alpha = F_X.evaluate(&alpha);

        // betas*
        let betas_star = betas_star(&instance.betas, &deltas, alpha);

        // sanity check: check that the new randomized instance (the original instance but with
        // 'refreshed' randomness) satisfies the relation.
        #[cfg(test)]
        {
            use crate::arith::Arith;
            r1cs.check_relation(
                w,
                &CommittedInstance::<_, true> {
                    phi: instance.phi,
                    betas: betas_star.clone(),
                    e: F_alpha,
                    x: instance.x.clone(),
                },
            )?;
        }

        let zs: Vec<Vec<C::ScalarField>> = std::iter::once(z.clone())
            .chain(
                vec_w
                    .iter()
                    .zip(vec_instances)
                    .map(|(wj, uj)| {
                        let zj = [vec![C::ScalarField::one()], uj.x.clone(), wj.w.clone()].concat();
                        if zj.len() != n {
                            return Err(Error::NotSameLength(
                                "zj.len()".to_string(),
                                zj.len(),
                                "number of variables in R1CS".to_string(),
                                n,
                            ));
                        }
                        Ok(zj)
                    })
                    .collect::<Result<Vec<Vec<C::ScalarField>>, Error>>()?,
            )
            .collect::<Vec<Vec<C::ScalarField>>>();

        let H =
            GeneralEvaluationDomain::<C::ScalarField>::new(k + 1).ok_or(Error::NewDomainFail)?;
        let G_domain = GeneralEvaluationDomain::<C::ScalarField>::new((d * k) + 1)
            .ok_or(Error::NewDomainFail)?;
        let L_X: Vec<DensePolynomial<C::ScalarField>> = lagrange_polys(H);

        // K(X) computation in a naive way, next iterations will compute K(X) as described in Claim
        // 4.5 of the paper.
        let mut G_evals: Vec<C::ScalarField> = vec![C::ScalarField::zero(); G_domain.size()];
        for (hi, h) in G_domain.elements().enumerate() {
            // each iteration evaluates G(h)
            // inner = L_0(x) * z + \sum_k L_i(x) * z_j
            let mut inner: Vec<C::ScalarField> = vec![C::ScalarField::zero(); zs[0].len()];
            for (z, L) in zs.iter().zip(&L_X) {
                // Li_z_h = (Li(X)*zj)(h) = Li(h) * zj
                let Lh = L.evaluate(&h);
                for (j, zj) in z.iter().enumerate() {
                    inner[j] += Lh * zj;
                }
            }
            let f_ev = r1cs.eval_at_z(&inner)?;

            G_evals[hi] = cfg_into_iter!(f_ev)
                .enumerate()
                .map(|(i, f_ev_i)| pow_i(i, &betas_star) * f_ev_i)
                .sum();
        }
        let G_X: DensePolynomial<C::ScalarField> =
            Evaluations::<C::ScalarField>::from_vec_and_domain(G_evals, G_domain).interpolate();
        let Z_X: DensePolynomial<C::ScalarField> = H.vanishing_polynomial().into();
        // K(X) = (G(X) - F(alpha)*L_0(X)) / Z(X)
        // Notice that L0(X)*F(a) will be 0 in the native case (the instance of the first folding
        // iteration case).
        let L0_e = &L_X[0] * F_alpha;
        let G_L0e = &G_X - &L0_e;
        // Pending optimization: move division by Z_X to the prev loop
        let (K_X, remainder) = G_L0e.divide_by_vanishing_poly(H).ok_or(Error::ProtoGalaxy(
            ProtoGalaxyError::CouldNotDivideByVanishing,
        ))?;
        if !remainder.is_zero() {
            return Err(Error::ProtoGalaxy(ProtoGalaxyError::RemainderNotZero));
        }

        let mut K_coeffs = K_X.coeffs.clone();
        K_coeffs.resize(d * k + 1, C::ScalarField::zero());
        transcript.absorb(&K_coeffs);

        let gamma = transcript.get_challenge();

        let L_X_evals = L_X
            .iter()
            .take(k + 1)
            .map(|L| L.evaluate(&gamma))
            .collect::<Vec<_>>();

        let mut phi_stars = vec![];

        let e_star = F_alpha * L_X_evals[0] + Z_X.evaluate(&gamma) * K_X.evaluate(&gamma);
        let mut w_star = vec_scalar_mul(&w.w, &L_X_evals[0]);
        let mut r_w_star = w.r_w * L_X_evals[0];
        let mut phi_star = instance.phi * L_X_evals[0];
        let mut x_star = vec_scalar_mul(&instance.x, &L_X_evals[0]);
        for i in 0..k {
            w_star = vec_add(&w_star, &vec_scalar_mul(&vec_w[i].w, &L_X_evals[i + 1]))?;
            r_w_star += vec_w[i].r_w * L_X_evals[i + 1];
            phi_stars.push(phi_star); // Push before updating. We don't need the last one
            phi_star += vec_instances[i].phi * L_X_evals[i + 1];
            x_star = vec_add(
                &x_star,
                &vec_scalar_mul(&vec_instances[i].x, &L_X_evals[i + 1]),
            )?;
        }

        Ok((
            CommittedInstance {
                betas: betas_star,
                phi: phi_star,
                e: e_star,
                x: x_star,
            },
            Witness {
                w: w_star,
                r_w: r_w_star,
            },
            F_coeffs,
            K_coeffs,
            L_X_evals,
            phi_stars,
        ))
    }

    /// implements the non-interactive Verifier from the folding scheme described in section 4
    pub fn verify(
        transcript: &mut impl Transcript<C::ScalarField>,
        // running instance
        instance: &CommittedInstance<C, true>,
        // incoming instances
        vec_instances: &[CommittedInstance<C, false>],
        // polys from P
        F_coeffs: Vec<C::ScalarField>,
        K_coeffs: Vec<C::ScalarField>,
    ) -> Result<CommittedInstance<C, true>, Error> {
        let t = instance.betas.len();

        // absorb the committed instances
        transcript.absorb(instance);
        transcript.absorb(&vec_instances);

        let delta = transcript.get_challenge();
        let deltas = exponential_powers(delta, t);

        transcript.absorb(&F_coeffs);

        let alpha = transcript.get_challenge();
        let alphas = all_powers(alpha, t);

        // F(alpha) = e + \sum_t F_i * alpha^i
        let mut F_alpha = instance.e;
        for (i, F_i) in F_coeffs.iter().skip(1).enumerate() {
            F_alpha += *F_i * alphas[i + 1];
        }

        let betas_star = betas_star(&instance.betas, &deltas, alpha);

        transcript.absorb(&K_coeffs);

        let k = vec_instances.len();
        let H =
            GeneralEvaluationDomain::<C::ScalarField>::new(k + 1).ok_or(Error::NewDomainFail)?;
        let L_X: Vec<DensePolynomial<C::ScalarField>> = lagrange_polys(H);
        let Z_X: DensePolynomial<C::ScalarField> = H.vanishing_polynomial().into();
        let K_X: DensePolynomial<C::ScalarField> =
            DensePolynomial::<C::ScalarField>::from_coefficients_vec(K_coeffs);

        let gamma = transcript.get_challenge();

        let L_X_evals = L_X
            .iter()
            .take(k + 1)
            .map(|L| L.evaluate(&gamma))
            .collect::<Vec<_>>();

        let e_star = F_alpha * L_X_evals[0] + Z_X.evaluate(&gamma) * K_X.evaluate(&gamma);

        let mut phi_star = instance.phi * L_X_evals[0];
        let mut x_star = vec_scalar_mul(&instance.x, &L_X_evals[0]);
        for i in 0..k {
            phi_star += vec_instances[i].phi * L_X_evals[i + 1];
            x_star = vec_add(
                &x_star,
                &vec_scalar_mul(&vec_instances[i].x, &L_X_evals[i + 1]),
            )?;
        }

        // return the folded instance
        Ok(CommittedInstance {
            betas: betas_star,
            phi: phi_star,
            e: e_star,
            x: x_star,
        })
    }
}

/// calculates F[x] using the optimized binary-tree technique
/// described in Claim 4.4
/// of [ProtoGalaxy](https://eprint.iacr.org/2023/1106.pdf)
fn calc_f_from_btree<F: PrimeField>(
    fw: &[F],
    betas: &[F],
    deltas: &[F],
) -> Result<SparsePolynomial<F>, Error> {
    let fw_len = fw.len();
    let betas_len = betas.len();
    let deltas_len = deltas.len();

    // ensure our binary tree is full
    if !fw_len.is_power_of_two() {
        return Err(Error::ProtoGalaxy(ProtoGalaxyError::BTreeNotFull(fw_len)));
    }

    if betas_len != deltas_len {
        return Err(Error::ProtoGalaxy(ProtoGalaxyError::WrongLenBetas(
            betas_len, deltas_len,
        )));
    }

    let mut layers: Vec<Vec<SparsePolynomial<F>>> = Vec::new();
    let leaves: Vec<SparsePolynomial<F>> = fw
        .iter()
        .copied()
        .map(|e| SparsePolynomial::<F>::from_coefficients_slice(&[(0, e)]))
        .collect();
    layers.push(leaves.to_vec());
    let mut currentNodes = leaves.clone();
    while currentNodes.len() > 1 {
        let index = layers.len();
        layers.push(vec![]);
        for (i, ni) in currentNodes.iter().enumerate().step_by(2) {
            let left = ni.clone();
            let right = SparsePolynomial::<F>::from_coefficients_vec(vec![
                (0, betas[layers.len() - 2]),
                (1, deltas[layers.len() - 2]),
            ])
            .mul(&currentNodes[i + 1]);

            layers[index].push(left + right);
        }
        currentNodes = layers[index].clone();
    }
    let root_index = layers.len() - 1;
    Ok(layers[root_index][0].clone())
}

// lagrange_polys method from caulk: https://github.com/caulk-crypto/caulk/tree/8210b51fb8a9eef4335505d1695c44ddc7bf8170/src/multi/setup.rs#L300
pub fn lagrange_polys<F: PrimeField>(
    domain_n: GeneralEvaluationDomain<F>,
) -> Vec<DensePolynomial<F>> {
    let mut lagrange_polynomials: Vec<DensePolynomial<F>> = Vec::new();
    for i in 0..domain_n.size() {
        let evals: Vec<F> = cfg_into_iter!(0..domain_n.size())
            .map(|k| if k == i { F::one() } else { F::zero() })
            .collect();
        lagrange_polynomials.push(Evaluations::from_vec_and_domain(evals, domain_n).interpolate());
    }
    lagrange_polynomials
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use ark_crypto_primitives::sponge::poseidon::PoseidonSponge;
    use ark_crypto_primitives::sponge::CryptographicSponge;
    use ark_pallas::{Fr, Projective};
    use ark_std::{rand::Rng, UniformRand};

    use crate::arith::r1cs::tests::{get_test_r1cs, get_test_z_split};
    use crate::arith::Arith;
    use crate::commitment::{pedersen::Pedersen, CommitmentScheme};
    use crate::transcript::poseidon::poseidon_canonical_config;

    #[test]
    fn test_pow_i() {
        let mut rng = ark_std::test_rng();
        let t = 4;
        let n = 16;
        let beta = Fr::rand(&mut rng);
        let betas = exponential_powers(beta, t);
        let not_betas = all_powers(beta, n);

        #[allow(clippy::needless_range_loop)]
        for i in 0..n {
            assert_eq!(pow_i(i, &betas), not_betas[i]);
        }
    }

    // k represents the number of instances to be fold, apart from the running instance
    #[allow(clippy::type_complexity)]
    pub fn prepare_inputs<C: CurveGroup>(
        k: usize,
    ) -> (
        Witness<C::ScalarField>,
        CommittedInstance<C, true>,
        Vec<Witness<C::ScalarField>>,
        Vec<CommittedInstance<C, false>>,
    ) {
        let mut rng = ark_std::test_rng();

        let (_, x, w) = get_test_z_split::<C::ScalarField>(rng.gen::<u16>() as usize);

        let (pedersen_params, _) = Pedersen::<C>::setup(&mut rng, w.len()).unwrap();

        let t = log2(get_test_r1cs::<C::ScalarField>().A.n_rows) as usize;

        let beta = C::ScalarField::rand(&mut rng);
        let betas = exponential_powers(beta, t);

        let witness = Witness::<C::ScalarField> {
            w,
            r_w: C::ScalarField::zero(),
        };
        let phi = Pedersen::<C>::commit(&pedersen_params, &witness.w, &witness.r_w).unwrap();
        let instance = CommittedInstance::<C, true> {
            phi,
            betas: betas.clone(),
            e: C::ScalarField::zero(),
            x,
        };
        // same for the other instances
        let mut witnesses: Vec<Witness<C::ScalarField>> = Vec::new();
        let mut instances: Vec<CommittedInstance<C, false>> = Vec::new();
        #[allow(clippy::needless_range_loop)]
        for _ in 0..k {
            let (_, x_i, w_i) = get_test_z_split::<C::ScalarField>(rng.gen::<u16>() as usize);
            let witness_i = Witness::<C::ScalarField> {
                w: w_i,
                r_w: C::ScalarField::zero(),
            };
            let phi_i =
                Pedersen::<C>::commit(&pedersen_params, &witness_i.w, &witness_i.r_w).unwrap();
            let instance_i = CommittedInstance::<C, false> {
                phi: phi_i,
                betas: vec![],
                e: C::ScalarField::zero(),
                x: x_i,
            };
            witnesses.push(witness_i);
            instances.push(instance_i);
        }

        (witness, instance, witnesses, instances)
    }

    #[test]
    fn test_fold() {
        let k = 7;
        let (witness, instance, witnesses, instances) = prepare_inputs(k);
        let r1cs = get_test_r1cs::<Fr>();

        // init Prover & Verifier's transcript
        let poseidon_config = poseidon_canonical_config::<Fr>();
        let mut transcript_p = PoseidonSponge::<Fr>::new(&poseidon_config);
        let mut transcript_v = PoseidonSponge::<Fr>::new(&poseidon_config);

        let (folded_instance, folded_witness, F_coeffs, K_coeffs, _, _) =
            Folding::<Projective>::prove(
                &mut transcript_p,
                &r1cs,
                &instance,
                &witness,
                &instances,
                &witnesses,
            )
            .unwrap();

        // verifier
        let folded_instance_v = Folding::<Projective>::verify(
            &mut transcript_v,
            &instance,
            &instances,
            F_coeffs,
            K_coeffs,
        )
        .unwrap();

        // check that prover & verifier folded instances are the same values
        assert_eq!(folded_instance.phi, folded_instance_v.phi);
        assert_eq!(folded_instance.betas, folded_instance_v.betas);
        assert_eq!(folded_instance.e, folded_instance_v.e);
        assert!(!folded_instance.e.is_zero());

        // check that the folded instance satisfies the relation
        r1cs.check_relation(&folded_witness, &folded_instance)
            .unwrap();
    }

    #[test]
    fn test_fold_various_iterations() {
        let r1cs = get_test_r1cs::<Fr>();

        // init Prover & Verifier's transcript
        let poseidon_config = poseidon_canonical_config::<Fr>();
        let mut transcript_p = PoseidonSponge::<Fr>::new(&poseidon_config);
        let mut transcript_v = PoseidonSponge::<Fr>::new(&poseidon_config);

        let (mut running_witness, mut running_instance, _, _) = prepare_inputs(0);

        // fold k instances on each of num_iters iterations
        let k = 7;
        let num_iters = 10;
        for _ in 0..num_iters {
            // generate the instances to be fold
            let (_, _, witnesses, instances) = prepare_inputs(k);

            let (folded_instance, folded_witness, F_coeffs, K_coeffs, _, _) =
                Folding::<Projective>::prove(
                    &mut transcript_p,
                    &r1cs,
                    &running_instance,
                    &running_witness,
                    &instances,
                    &witnesses,
                )
                .unwrap();

            // verifier
            let folded_instance_v = Folding::<Projective>::verify(
                &mut transcript_v,
                &running_instance,
                &instances,
                F_coeffs,
                K_coeffs,
            )
            .unwrap();

            // check that prover & verifier folded instances are the same values
            assert_eq!(folded_instance, folded_instance_v);

            assert!(!folded_instance.e.is_zero());

            // check that the folded instance satisfies the relation
            r1cs.check_relation(&folded_witness, &folded_instance)
                .unwrap();

            running_witness = folded_witness;
            running_instance = folded_instance;
        }
    }
}
