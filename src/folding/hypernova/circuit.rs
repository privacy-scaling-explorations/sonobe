// hypernova nimfs verifier circuit
// see section 5 in https://eprint.iacr.org/2023/573.pdf

use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use ark_r1cs_std::{
    fields::{fp::FpVar, FieldVar},
    ToBitsGadget,
};
use ark_relations::r1cs::SynthesisError;
use std::marker::PhantomData;

/// Gadget to compute the sum of all $\gamma^{j} \cdot eq(r_{x_j}, r_x^{\prime}) \cdot \sigma_j$.
pub struct SumMulsGammaPowsEqSigmaGadget<F: PrimeField> {
    _f: PhantomData<F>,
}

impl<F: PrimeField> SumMulsGammaPowsEqSigmaGadget<F> {
    /// Computes the sum $\Sigma_{j}^{j + n} \gamma^{j} \cdot eq_eval \cdot \sigma_{j}$, where $n$ is the length of the `sigmas` vector
    /// It corresponds to the first term of the sum that $\mathcal{V}$ has to compute at section 5, step 5 of "A multi-folding scheme for CCS".
    ///
    /// # Arguments
    /// - `sigmas`: vector of $\sigma_j$ values
    /// - `eq_eval`: the value of $\tilde{eq}(x_j, x^{\prime})$
    /// - `gamma`: value $\gamma$
    /// - `j`: the power at which we start to compute $\gamma^{j}$. This is needed in the contexxt of multifolding.
    ///
    /// # Notes
    /// In the context of multifolding, `j` corresponds to `ccs.t` in `compute_c_from_sigmas_and_thetas`
    pub fn sum_muls_gamma_pows_eq_sigma(
        sigmas: Vec<FpVar<F>>,
        eq_eval: FpVar<F>,
        gamma: FpVar<F>,
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

/// Gadget to compute $\Sigma_{i=1}^{q} c_i * \Pi_{j \in S_i} theta_j$.
pub struct SumCiMulProdThetajGadget<F: PrimeField> {
    _f: PhantomData<F>,
}

impl<F: PrimeField> SumCiMulProdThetajGadget<F> {
    /// Computes $\Sigma_{i=1}^{q} c_i * \Pi_{j \in S_i} theta_j$
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
    pub fn sum_ci_mul_prod_thetaj(c_i: Vec<FpVar<F>>, thetas: Vec<Vec<FpVar<F>>>) -> FpVar<F> {
        let mut result = FpVar::<F>::zero();
        for (i, c_i) in c_i.iter().enumerate() {
            let prod = &thetas[i].iter().fold(FpVar::one(), |acc, e| acc * e);
            result += c_i * prod;
        }
        result
    }
}

/// Returns a vector of thetas for a corresponding $S_i$
/// An helper function to run before computing $\Pi_{j \in S_i} \theta_j$ in a circuit.
pub fn get_prepared_thetas<C: CurveGroup>(
    S_i: &Vec<usize>,
    thetas: &[C::ScalarField],
) -> Vec<C::ScalarField> {
    let mut prepared: Vec<C::ScalarField> = Vec::new();
    for j in S_i {
        prepared.push(thetas[*j]);
    }
    prepared
}

#[cfg(test)]
mod tests {
    use super::{SumCiMulProdThetajGadget, SumMulsGammaPowsEqSigmaGadget};
    use crate::{
        ccs::{
            tests::{get_test_ccs, get_test_z},
            CCS,
        },
        folding::hypernova::{
            circuit::get_prepared_thetas,
            utils::{
                compute_sigmas_and_thetas, sum_ci_mul_prod_thetaj, sum_muls_gamma_pows_eq_sigma,
            },
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
                sigmas_var,
                eq_var,
                gamma_var.clone(),
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
                let prepared = get_prepared_thetas::<Projective>(&ccs.S[i], thetas);
                prepared_thetas
                    .push(Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(prepared)).unwrap());
            }
            let computed = SumCiMulProdThetajGadget::sum_ci_mul_prod_thetaj(
                Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(ccs.c.clone())).unwrap(),
                prepared_thetas,
            );
            assert_eq!(expected, computed.value().unwrap());
        }
    }
}
