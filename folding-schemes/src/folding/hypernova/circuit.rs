// hypernova nimfs verifier circuit
// see section 5 in https://eprint.iacr.org/2023/573.pdf

use crate::{ccs::CCS, folding::circuits::utils::EqEvalGadget};
use ark_ff::PrimeField;
use ark_r1cs_std::{
    alloc::AllocVar,
    fields::{fp::FpVar, FieldVar},
    ToBitsGadget,
};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use std::marker::PhantomData;

/// Gadget to compute $\sum_{j \in [t]} \gamma^{j} \cdot e_1 \cdot \sigma_j + \gamma^{t+1} \cdot e_2 \cdot \sum_{i=1}^{q} c_i * \prod_{j \in S_i} \theta_j$.
/// This is the sum computed by the verifier and laid out in section 5, step 5 of "A multi-folding scheme for CCS".
pub struct ComputeCFromSigmasAndThetasGadget<F: PrimeField> {
    _f: PhantomData<F>,
}

impl<F: PrimeField> ComputeCFromSigmasAndThetasGadget<F> {
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
    fn sum_muls_gamma_pows_eq_sigma(
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
    fn sum_ci_mul_prod_thetaj(
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
        cs: ConstraintSystemRef<F>,
        ccs: &CCS<F>,
        vec_sigmas: Vec<Vec<FpVar<F>>>,
        vec_thetas: Vec<Vec<FpVar<F>>>,
        gamma: FpVar<F>,
        beta: Vec<FpVar<F>>,
        vec_r_x: Vec<Vec<FpVar<F>>>,
        vec_r_x_prime: Vec<FpVar<F>>,
    ) -> Result<FpVar<F>, SynthesisError> {
        let mut c = FpVar::<F>::new_witness(cs.clone(), || Ok(F::zero()))?;
        let t = FpVar::<F>::new_witness(cs.clone(), || Ok(F::from(ccs.t as u64)))?;

        let mut e_lcccs = Vec::new();
        for r_x in vec_r_x.iter() {
            let e_1 = EqEvalGadget::eq_eval(r_x.to_vec(), vec_r_x_prime.to_vec())?;
            e_lcccs.push(e_1);
        }

        for (i, sigmas) in vec_sigmas.iter().enumerate() {
            let i_var = FpVar::<F>::new_witness(cs.clone(), || Ok(F::from(i as u64)))?;
            let pow = i_var * t.clone();
            c += Self::sum_muls_gamma_pows_eq_sigma(
                gamma.clone(),
                e_lcccs[i].clone(),
                sigmas.to_vec(),
                pow,
            )?;
        }

        let mu = FpVar::<F>::new_witness(cs.clone(), || Ok(F::from(vec_sigmas.len() as u64)))?;
        let e_2 = EqEvalGadget::eq_eval(beta, vec_r_x_prime)?;
        for (k, thetas) in vec_thetas.iter().enumerate() {
            // get prepared thetas. only step different from original `compute_c_from_sigmas_and_thetas`
            let mut prepared_thetas = Vec::new();
            for i in 0..ccs.q {
                let prepared: Vec<FpVar<F>> = ccs.S[i].iter().map(|j| thetas[*j].clone()).collect();
                prepared_thetas.push(prepared.to_vec());
            }

            let c_i = Vec::<FpVar<F>>::new_witness(cs.clone(), || Ok(ccs.c.clone())).unwrap();
            let lhs = Self::sum_ci_mul_prod_thetaj(c_i.clone(), prepared_thetas.clone())?;

            // compute gamma^(t+1)
            let pow = mu.clone() * t.clone()
                + FpVar::<F>::new_witness(cs.clone(), || Ok(F::from(k as u64)))?;
            let gamma_t1 = gamma.pow_le(&pow.to_bits_le()?)?;

            c += gamma_t1.clone() * e_2.clone() * lhs.clone();
        }

        Ok(c)
    }
}

#[cfg(test)]
mod tests {
    use super::ComputeCFromSigmasAndThetasGadget;
    use crate::{
        ccs::{
            tests::{get_test_ccs, get_test_z},
            CCS,
        },
        commitment::{pedersen::Pedersen, CommitmentScheme},
        folding::hypernova::utils::{
            compute_c_from_sigmas_and_thetas, compute_sigmas_and_thetas, sum_ci_mul_prod_thetaj,
            sum_muls_gamma_pows_eq_sigma,
        },
        utils::virtual_polynomial::eq_eval,
    };
    use ark_pallas::{Fr, Projective};
    use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar, R1CSVar};
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::{test_rng, UniformRand};

    #[test]
    pub fn test_sum_muls_gamma_pow_eq_sigma_gadget() {
        let mut rng = test_rng();
        let ccs: CCS<Fr> = get_test_ccs();
        let z1 = get_test_z(3);
        let z2 = get_test_z(4);

        let gamma: Fr = Fr::rand(&mut rng);
        let r_x_prime: Vec<Fr> = (0..ccs.s).map(|_| Fr::rand(&mut rng)).collect();

        // Initialize a multifolding object
        let (pedersen_params, _) =
            Pedersen::<Projective>::setup(&mut rng, ccs.n - ccs.l - 1).unwrap();
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
            let computed = ComputeCFromSigmasAndThetasGadget::<Fr>::sum_muls_gamma_pows_eq_sigma(
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
        let ccs: CCS<Fr> = get_test_ccs();
        let z1 = get_test_z(3);
        let z2 = get_test_z(4);

        let r_x_prime: Vec<Fr> = (0..ccs.s).map(|_| Fr::rand(&mut rng)).collect();

        // Initialize a multifolding object
        let (pedersen_params, _) =
            Pedersen::<Projective>::setup(&mut rng, ccs.n - ccs.l - 1).unwrap();
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
        for thetas in vec_thetas.iter() {
            // sum c_i * prod theta_j
            let expected = sum_ci_mul_prod_thetaj(&ccs, thetas); // from `compute_c_from_sigmas_and_thetas`
            let mut prepared_thetas = Vec::new();
            for i in 0..ccs.q {
                let prepared: Vec<Fr> = ccs.S[i].iter().map(|j| thetas[*j]).collect();
                prepared_thetas
                    .push(Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(prepared)).unwrap());
            }
            let computed = ComputeCFromSigmasAndThetasGadget::<Fr>::sum_ci_mul_prod_thetaj(
                Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(ccs.c.clone())).unwrap(),
                prepared_thetas,
            )
            .unwrap();
            assert_eq!(expected, computed.value().unwrap());
        }
    }

    #[test]
    pub fn test_compute_c_from_sigmas_and_thetas_gadget() {
        // number of LCCCS & CCCS instances to fold in a single step
        let mu = 32;
        let nu = 42;

        let mut z_lcccs = Vec::new();
        for i in 0..mu {
            let z = get_test_z(i + 3);
            z_lcccs.push(z);
        }
        let mut z_cccs = Vec::new();
        for i in 0..nu {
            let z = get_test_z(i + 3);
            z_cccs.push(z);
        }

        let ccs: CCS<Fr> = get_test_ccs();

        let mut rng = test_rng();
        let gamma: Fr = Fr::rand(&mut rng);
        let beta: Vec<Fr> = (0..ccs.s).map(|_| Fr::rand(&mut rng)).collect();
        let r_x_prime: Vec<Fr> = (0..ccs.s).map(|_| Fr::rand(&mut rng)).collect();

        let (pedersen_params, _) =
            Pedersen::<Projective>::setup(&mut rng, ccs.n - ccs.l - 1).unwrap();

        // Create the LCCCS instances out of z_lcccs
        let mut lcccs_instances = Vec::new();
        for z_i in z_lcccs.iter() {
            let (inst, _) = ccs.to_lcccs(&mut rng, &pedersen_params, z_i).unwrap();
            lcccs_instances.push(inst);
        }
        // Create the CCCS instance out of z_cccs
        let mut cccs_instances = Vec::new();
        for z_i in z_cccs.iter() {
            let (inst, _) = ccs.to_cccs(&mut rng, &pedersen_params, z_i).unwrap();
            cccs_instances.push(inst);
        }

        let sigmas_thetas = compute_sigmas_and_thetas(&ccs, &z_lcccs, &z_cccs, &r_x_prime);

        let expected_c = compute_c_from_sigmas_and_thetas(
            &ccs,
            &sigmas_thetas,
            gamma,
            &beta,
            &lcccs_instances
                .iter()
                .map(|lcccs| lcccs.r_x.clone())
                .collect(),
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
        let vec_r_x: Vec<Vec<FpVar<Fr>>> = lcccs_instances
            .iter()
            .map(|lcccs| {
                Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(lcccs.r_x.clone())).unwrap()
            })
            .collect();
        let vec_r_x_prime =
            Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(r_x_prime.clone())).unwrap();
        let gamma_var = FpVar::<Fr>::new_witness(cs.clone(), || Ok(gamma)).unwrap();
        let beta_var = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(beta.clone())).unwrap();
        let computed_c = ComputeCFromSigmasAndThetasGadget::compute_c_from_sigmas_and_thetas(
            cs.clone(),
            &ccs,
            vec_sigmas,
            vec_thetas,
            gamma_var,
            beta_var,
            vec_r_x,
            vec_r_x_prime,
        )
        .unwrap();

        dbg!(cs.num_constraints());
        assert_eq!(expected_c, computed_c.value().unwrap());
    }
}
