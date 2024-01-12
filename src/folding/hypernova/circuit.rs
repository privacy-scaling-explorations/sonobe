// hypernova nimfs verifier circuit
// see section 5 in https://eprint.iacr.org/2023/573.pdf

use crate::{ccs::CCS, folding::circuits::utils::EqEvalGadget};
use ark_ec::{CurveGroup, Group};
use ark_ff::PrimeField;
use ark_r1cs_std::{
    alloc::AllocVar,
    fields::{fp::FpVar, FieldVar},
    ToBitsGadget,
};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use ark_std::Zero;
use std::{borrow::Borrow, marker::PhantomData};

/// Gadget to compute the sum of all $\gamma^{j} \cdot eq(r_{x_j}, r_x^{\prime}) \cdot \sigma_j$.
pub struct SumMulsGammaPowsEqSigmaGadget<F: PrimeField> {
    _f: PhantomData<F>,
}

impl<F: PrimeField> SumMulsGammaPowsEqSigmaGadget<F> {
    /// Computes the sum $\sum_{j}^{j + n} \gamma^{j} \cdot eq_eval \cdot \sigma_{j}$, where $n$ is the length of the `sigmas` vector
    /// It corresponds to the first term of the sum that $\mathcal{V}$ has to compute at section 5, step 5 of "A multi-folding scheme for CCS".
    ///
    /// # Arguments
    /// - `sigmas`: vector of $\sigma_j$ values
    /// - `eq_eval`: the value of $\tilde{eq}(x_j, x^{\prime})$
    /// - `gamma`: value $\gamma$
    /// - `j`: the power at which we start to compute $\gamma^{j}$. This is needed in the context of multifolding.
    ///
    /// # Notes
    /// In the context of multifolding, `j` corresponds to `ccs.t` in `compute_c_from_sigmas_and_thetas`
    pub fn sum_muls_gamma_pows_eq_sigma(
        gamma: FpVar<F>,
        eq_eval: FpVar<F>,
        sigmas: Vec<FpVar<F>>,
        j: FpVar<F>,
    ) -> Result<FpVar<F>, SynthesisError> {
        let mut result = FpVar::<F>::zero();
        let mut gamma_pow = gamma.pow_le(&j.to_bits_le()?)?;
        for sigma in sigmas {
            result += gamma_pow.clone() * eq_eval.clone() * sigma;
            gamma_pow *= gamma.clone();
        }
        Ok(result)
    }
}

/// Gadget to compute $\sum_{i=1}^{q} c_i * \prod_{j \in S_i} theta_j$.
pub struct SumCiMulProdThetajGadget<F: PrimeField> {
    _f: PhantomData<F>,
}

impl<F: PrimeField> SumCiMulProdThetajGadget<F> {
    /// Computes $\sum_{i=1}^{q} c_i * \prod_{j \in S_i} theta_j$
    ///
    /// # Arguments
    /// - `c_i`: vector of $c_i$ values
    /// - `thetas`: vector of pre-processed $\thetas[j]$ values corresponding to a particular `ccs.S[i]`
    ///
    /// # Notes
    /// This is a part of the second term of the sum that $\mathcal{V}$ has to compute at section 5, step 5 of "A multi-folding scheme for CCS".
    /// The first term is computed by `SumMulsGammaPowsEqSigmaGadget::sum_muls_gamma_pows_eq_sigma`.
    /// This is a doct product between a vector of c_i values and a vector of pre-processed $\theta_j$ values, where $j$ is a value from $S_i$.
    /// Hence, this requires some pre-processing of the $\theta_j$ values, before running this gadget.
    pub fn sum_ci_mul_prod_thetaj(
        c_i: Vec<FpVar<F>>,
        thetas: Vec<Vec<FpVar<F>>>,
    ) -> Result<FpVar<F>, SynthesisError> {
        let mut result = FpVar::<F>::zero();
        for (i, c_i) in c_i.iter().enumerate() {
            let prod = &thetas[i].iter().fold(FpVar::one(), |acc, e| acc * e);
            result += c_i * prod;
        }
        Ok(result)
    }
}

/// Gadget to compute $\sum_{j \in [t]} \gamma^{j} \cdot e_1 \cdot \sigma_j + \gamma^{t+1} \cdot e_2 \cdot \sum_{i=1}^{q} c_i * \prod_{j \in S_i} theta_j$.
/// This is the sum computed by the verifier and laid out in section 5, step 5 of "A multi-folding scheme for CCS".
pub struct ComputeCFromSigmasAndThetasGadget<C: CurveGroup> {
    _c: PhantomData<C>,
}

impl<C: CurveGroup> ComputeCFromSigmasAndThetasGadget<C> {
    /// Computes the sum that the verifier has to compute at section 5, step 5 of "A multi-folding scheme for CCS".
    ///
    /// # Arguments
    /// - `cs`: constraint system
    /// - `ccs`: the CCS instance
    /// - `vec_sigmas`: vector of $\sigma_j$ values
    /// - `vec_thetas`: vector of $\theta_j$ values
    /// - `gamma`: value $\gamma$
    /// - `beta`: vector of $\beta_j$ values
    /// - `vec_r_x`: vector of $r_{x_j}$ values
    /// - `vec_r_x_prime`: vector of $r_{x_j}^{\prime}$ values
    ///
    /// # Notes
    /// Arguments to this function are *almost* the same as the arguments to `compute_c_from_sigmas_and_thetas` in `utils.rs`.
    #[allow(clippy::too_many_arguments)]
    pub fn compute_c_from_sigmas_and_thetas(
        cs: ConstraintSystemRef<C::ScalarField>,
        ccs: &CCS<C>,
        vec_sigmas: Vec<Vec<FpVar<C::ScalarField>>>,
        vec_thetas: Vec<Vec<FpVar<C::ScalarField>>>,
        gamma: FpVar<C::ScalarField>,
        beta: Vec<FpVar<C::ScalarField>>,
        vec_r_x: Vec<Vec<FpVar<C::ScalarField>>>,
        vec_r_x_prime: Vec<FpVar<C::ScalarField>>,
    ) -> Result<FpVar<C::ScalarField>, SynthesisError> {
        let mut c =
            FpVar::<C::ScalarField>::new_witness(cs.clone(), || Ok(C::ScalarField::zero()))?;
        let t = FpVar::<C::ScalarField>::new_witness(cs.clone(), || {
            Ok(C::ScalarField::from(ccs.t as u64))
        })?;

        let mut e_lcccs = Vec::new();
        for r_x in vec_r_x.iter() {
            let e_1 = EqEvalGadget::eq_eval(r_x.to_vec(), vec_r_x_prime.to_vec())?;
            e_lcccs.push(e_1);
        }

        for (i, sigmas) in vec_sigmas.iter().enumerate() {
            let i_var = FpVar::<C::ScalarField>::new_witness(cs.clone(), || {
                Ok(C::ScalarField::from(i as u64))
            })?;
            let pow = i_var * t.clone();
            c += SumMulsGammaPowsEqSigmaGadget::sum_muls_gamma_pows_eq_sigma(
                gamma.clone(),
                e_lcccs[i].clone(),
                sigmas.to_vec(),
                pow,
            )?;
        }

        let mu = FpVar::<C::ScalarField>::new_witness(cs.clone(), || {
            Ok(C::ScalarField::from(vec_sigmas.len() as u64))
        })?;
        let e_2 = EqEvalGadget::eq_eval(beta, vec_r_x_prime)?;
        for (k, thetas) in vec_thetas.iter().enumerate() {
            // get prepared thetas. only step different from original `compute_c_from_sigmas_and_thetas`
            let mut prepared_thetas = Vec::new();
            for i in 0..ccs.q {
                let prepared: Vec<FpVar<C::ScalarField>> =
                    ccs.S[i].iter().map(|j| thetas[*j].clone()).collect();
                prepared_thetas.push(prepared.to_vec());
            }

            let c_i = Vec::<FpVar<C::ScalarField>>::new_witness(cs.clone(), || Ok(ccs.c.clone()))
                .unwrap();
            let lhs = SumCiMulProdThetajGadget::sum_ci_mul_prod_thetaj(
                c_i.clone(),
                prepared_thetas.clone(),
            )?;

            // compute gamma^(t+1)
            let pow = mu.clone() * t.clone()
                + FpVar::<C::ScalarField>::new_witness(cs.clone(), || {
                    Ok(C::ScalarField::from(k as u64))
                })?;
            let gamma_t1 = gamma.pow_le(&pow.to_bits_le()?)?;

            c += gamma_t1.clone() * e_2.clone() * lhs.clone();
        }

        Ok(c)
    }
}

#[cfg(test)]
mod tests {
    use super::{
        ComputeCFromSigmasAndThetasGadget, SumCiMulProdThetajGadget, SumMulsGammaPowsEqSigmaGadget,
    };
    use crate::{
        ccs::{
            tests::{get_test_ccs, get_test_z},
            CCS,
        },
        folding::hypernova::utils::{
            compute_c_from_sigmas_and_thetas, compute_sigmas_and_thetas, sum_ci_mul_prod_thetaj,
            sum_muls_gamma_pows_eq_sigma,
        },
        pedersen::Pedersen,
        utils::virtual_polynomial::eq_eval,
    };
    use ark_pallas::{Fr, Projective};
    use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar, R1CSVar};
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::{test_rng, UniformRand};

    #[test]
    pub fn test_sum_muls_gamma_pow_eq_sigma_gadget() {
        let mut rng = test_rng();
        let ccs: CCS<Projective> = get_test_ccs();
        let z1 = get_test_z(3);
        let z2 = get_test_z(4);

        let gamma: Fr = Fr::rand(&mut rng);
        let r_x_prime: Vec<Fr> = (0..ccs.s).map(|_| Fr::rand(&mut rng)).collect();

        // Initialize a multifolding object
        let pedersen_params = Pedersen::new_params(&mut rng, ccs.n - ccs.l - 1);
        let (lcccs_instance, _) = ccs.to_lcccs(&mut rng, &pedersen_params, &z1).unwrap();
        let sigmas_thetas =
            compute_sigmas_and_thetas(&ccs, &[z1.clone()], &[z2.clone()], &r_x_prime);

        let mut e_lcccs = Vec::new();
        for r_x in &vec![lcccs_instance.r_x] {
            e_lcccs.push(eq_eval(r_x, &r_x_prime).unwrap());
        }

        // Initialize cs and gamma
        let cs = ConstraintSystem::<Fr>::new_ref();
        let gamma_var = FpVar::<Fr>::new_witness(cs.clone(), || Ok(gamma)).unwrap();

        for (i, sigmas) in sigmas_thetas.0.iter().enumerate() {
            let expected =
                sum_muls_gamma_pows_eq_sigma(gamma, e_lcccs[i], sigmas, (i * ccs.t) as u64);
            let sigmas_var =
                Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(sigmas.clone())).unwrap();
            let eq_var = FpVar::<Fr>::new_witness(cs.clone(), || Ok(e_lcccs[i])).unwrap();
            let pow =
                FpVar::<Fr>::new_witness(cs.clone(), || Ok(Fr::from((i * ccs.t) as u64))).unwrap();
            let computed = SumMulsGammaPowsEqSigmaGadget::sum_muls_gamma_pows_eq_sigma(
                gamma_var.clone(),
                eq_var,
                sigmas_var,
                pow,
            )
            .unwrap();
            assert_eq!(expected, computed.value().unwrap());
        }
    }

    #[test]
    pub fn test_sum_ci_mul_prod_thetaj_gadget() {
        let mut rng = test_rng();
        let ccs: CCS<Projective> = get_test_ccs();
        let z1 = get_test_z(3);
        let z2 = get_test_z(4);

        let r_x_prime: Vec<Fr> = (0..ccs.s).map(|_| Fr::rand(&mut rng)).collect();

        // Initialize a multifolding object
        let pedersen_params = Pedersen::new_params(&mut rng, ccs.n - ccs.l - 1);
        let (lcccs_instance, _) = ccs.to_lcccs(&mut rng, &pedersen_params, &z1).unwrap();
        let sigmas_thetas =
            compute_sigmas_and_thetas(&ccs, &[z1.clone()], &[z2.clone()], &r_x_prime);

        let mut e_lcccs = Vec::new();
        for r_x in &vec![lcccs_instance.r_x] {
            e_lcccs.push(eq_eval(r_x, &r_x_prime).unwrap());
        }

        // Initialize cs
        let cs = ConstraintSystem::<Fr>::new_ref();
        let vec_thetas = sigmas_thetas.1;
        for (_, thetas) in vec_thetas.iter().enumerate() {
            // sum c_i * prod theta_j
            let expected = sum_ci_mul_prod_thetaj(&ccs, thetas); // from `compute_c_from_sigmas_and_thetas`
            let mut prepared_thetas = Vec::new();
            for i in 0..ccs.q {
                let prepared: Vec<Fr> = ccs.S[i].iter().map(|j| thetas[*j]).collect();
                prepared_thetas
                    .push(Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(prepared)).unwrap());
            }
            let computed = SumCiMulProdThetajGadget::sum_ci_mul_prod_thetaj(
                Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(ccs.c.clone())).unwrap(),
                prepared_thetas,
            )
            .unwrap();
            assert_eq!(expected, computed.value().unwrap());
        }
    }

    #[test]
    pub fn test_compute_c_from_sigmas_and_thetas_gadget() {
        let ccs: CCS<Projective> = get_test_ccs();
        let z1 = get_test_z(3);
        let z2 = get_test_z(4);

        let mut rng = test_rng();
        let gamma: Fr = Fr::rand(&mut rng);
        let beta: Vec<Fr> = (0..ccs.s).map(|_| Fr::rand(&mut rng)).collect();
        let r_x_prime: Vec<Fr> = (0..ccs.s).map(|_| Fr::rand(&mut rng)).collect();

        // Initialize a multifolding object
        let pedersen_params = Pedersen::new_params(&mut rng, ccs.n - ccs.l - 1);
        let (lcccs_instance, _) = ccs.to_lcccs(&mut rng, &pedersen_params, &z1).unwrap();
        let sigmas_thetas =
            compute_sigmas_and_thetas(&ccs, &[z1.clone()], &[z2.clone()], &r_x_prime);

        let expected_c = compute_c_from_sigmas_and_thetas(
            &ccs,
            &sigmas_thetas,
            gamma,
            &beta,
            &vec![lcccs_instance.r_x.clone()],
            &r_x_prime,
        );

        let cs = ConstraintSystem::<Fr>::new_ref();
        let mut vec_sigmas = Vec::new();
        let mut vec_thetas = Vec::new();
        for sigmas in sigmas_thetas.0 {
            vec_sigmas
                .push(Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(sigmas.clone())).unwrap());
        }
        for thetas in sigmas_thetas.1 {
            vec_thetas
                .push(Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(thetas.clone())).unwrap());
        }
        let vec_r_x =
            vec![
                Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(lcccs_instance.r_x.clone()))
                    .unwrap(),
            ];
        let vec_r_x_prime =
            Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(r_x_prime.clone())).unwrap();
        let gamma_var = FpVar::<Fr>::new_witness(cs.clone(), || Ok(gamma)).unwrap();
        let beta_var = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(beta.clone())).unwrap();
        let computed_c = ComputeCFromSigmasAndThetasGadget::compute_c_from_sigmas_and_thetas(
            cs,
            &ccs,
            vec_sigmas,
            vec_thetas,
            gamma_var,
            beta_var,
            vec_r_x,
            vec_r_x_prime,
        )
        .unwrap();

        assert_eq!(expected_c, computed_c.value().unwrap());
    }
}
