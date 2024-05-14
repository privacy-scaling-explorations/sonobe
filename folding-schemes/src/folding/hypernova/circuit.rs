/// Implementation of [HyperNova](https://eprint.iacr.org/2023/573.pdf) NIMFS verifier circuit
use ark_ff::PrimeField;
use ark_r1cs_std::{
    alloc::AllocVar,
    fields::{fp::FpVar, FieldVar},
};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};

use crate::ccs::CCS;
use crate::folding::circuits::utils::EqEvalGadget;

/// computes c from the step 5 in section 5 of HyperNova, adapted to multiple LCCCS & CCCS
/// instances:
/// $$
/// c = \sum_{i \in [\mu]} \left(\sum_{j \in [t]} \gamma^{i \cdot t + j} \cdot e_i \cdot \sigma_{i,j} \right)
/// + \sum_{k \in [\nu]} \gamma^{\mu \cdot t+k} \cdot e_k \cdot \left( \sum_{i=1}^q c_i \cdot \prod_{j \in S_i}
/// \theta_{k,j} \right)
/// $$
#[allow(dead_code)] // TMP while the other circuits are not ready
#[allow(clippy::too_many_arguments)]
fn compute_c_gadget<F: PrimeField>(
    cs: ConstraintSystemRef<F>,
    ccs: &CCS<F>,
    vec_sigmas: Vec<Vec<FpVar<F>>>,
    vec_thetas: Vec<Vec<FpVar<F>>>,
    gamma: FpVar<F>,
    beta: Vec<FpVar<F>>,
    vec_r_x: Vec<Vec<FpVar<F>>>,
    vec_r_x_prime: Vec<FpVar<F>>,
) -> Result<FpVar<F>, SynthesisError> {
    let mut e_lcccs = Vec::new();
    for r_x in vec_r_x.iter() {
        e_lcccs.push(EqEvalGadget::eq_eval(r_x, &vec_r_x_prime)?);
    }

    let mut c = FpVar::<F>::zero();
    let mut current_gamma = FpVar::<F>::one();
    for i in 0..vec_sigmas.len() {
        for j in 0..ccs.t {
            c += current_gamma.clone() * e_lcccs[i].clone() * vec_sigmas[i][j].clone();
            current_gamma *= gamma.clone();
        }
    }

    let ccs_c = Vec::<FpVar<F>>::new_constant(cs.clone(), ccs.c.clone())?;
    let e_k = EqEvalGadget::eq_eval(&beta, &vec_r_x_prime)?;
    #[allow(clippy::needless_range_loop)]
    for k in 0..vec_thetas.len() {
        let mut sum = FpVar::<F>::zero();
        for i in 0..ccs.q {
            let mut prod = FpVar::<F>::one();
            for j in ccs.S[i].clone() {
                prod *= vec_thetas[k][j].clone();
            }
            sum += ccs_c[i].clone() * prod;
        }
        c += current_gamma.clone() * e_k.clone() * sum;
        current_gamma *= gamma.clone();
    }
    Ok(c)
}

#[cfg(test)]
mod tests {
    use ark_pallas::{Fr, Projective};
    use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar, R1CSVar};
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::{test_rng, UniformRand};

    use super::*;
    use crate::{
        ccs::{
            tests::{get_test_ccs, get_test_z},
            CCS,
        },
        commitment::{pedersen::Pedersen, CommitmentScheme},
        folding::hypernova::utils::{compute_c, compute_sigmas_and_thetas},
    };

    #[test]
    pub fn test_compute_c_gadget() {
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

        let expected_c = compute_c(
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
        let computed_c = compute_c_gadget(
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
