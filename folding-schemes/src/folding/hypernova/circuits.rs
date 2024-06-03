/// Implementation of [HyperNova](https://eprint.iacr.org/2023/573.pdf) NIMFS verifier circuit
use ark_crypto_primitives::sponge::Absorb;
use ark_ec::{CurveGroup, Group};
use ark_ff::PrimeField;
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    eq::EqGadget,
    fields::{fp::FpVar, FieldVar},
};
use ark_relations::r1cs::{ConstraintSystemRef, Namespace, SynthesisError};
use core::{borrow::Borrow, marker::PhantomData};

use super::{cccs::CCCS, lcccs::LCCCS, nimfs::Proof};
use crate::folding::circuits::{
    nonnative::affine::NonNativeAffineVar,
    sum_check::{IOPProofVar, SumCheckVerifierGadget, VPAuxInfoVar},
    utils::EqEvalGadget,
    CF1,
};
use crate::utils::virtual_polynomial::VPAuxInfo;
use crate::{ccs::CCS, transcript::TranscriptVar};

/// Committed CCS instance
#[derive(Debug, Clone)]
pub struct CCCSVar<C: CurveGroup>
where
    <C as CurveGroup>::BaseField: PrimeField,
{
    // Commitment to witness
    pub C: NonNativeAffineVar<C>,
    // Public input/output
    pub x: Vec<FpVar<CF1<C>>>,
}
impl<C> AllocVar<CCCS<C>, CF1<C>> for CCCSVar<C>
where
    C: CurveGroup,
    <C as ark_ec::CurveGroup>::BaseField: PrimeField,
{
    fn new_variable<T: Borrow<CCCS<C>>>(
        cs: impl Into<Namespace<CF1<C>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|val| {
            let cs = cs.into();

            let C = NonNativeAffineVar::<C>::new_variable(cs.clone(), || Ok(val.borrow().C), mode)?;
            let x: Vec<FpVar<C::ScalarField>> =
                Vec::new_variable(cs.clone(), || Ok(val.borrow().x.clone()), mode)?;

            Ok(Self { C, x })
        })
    }
}

/// Linearized Committed CCS instance
#[derive(Debug, Clone)]
pub struct LCCCSVar<C: CurveGroup>
where
    <C as CurveGroup>::BaseField: PrimeField,
{
    // Commitment to witness
    pub C: NonNativeAffineVar<C>,
    // Relaxation factor of z for folded LCCCS
    pub u: FpVar<CF1<C>>,
    // Public input/output
    pub x: Vec<FpVar<CF1<C>>>,
    // Random evaluation point for the v_i
    pub r_x: Vec<FpVar<CF1<C>>>,
    // Vector of v_i
    pub v: Vec<FpVar<CF1<C>>>,
}
impl<C> AllocVar<LCCCS<C>, CF1<C>> for LCCCSVar<C>
where
    C: CurveGroup,
    <C as ark_ec::CurveGroup>::BaseField: PrimeField,
{
    fn new_variable<T: Borrow<LCCCS<C>>>(
        cs: impl Into<Namespace<CF1<C>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|val| {
            let cs = cs.into();

            let C = NonNativeAffineVar::<C>::new_variable(cs.clone(), || Ok(val.borrow().C), mode)?;
            let u = FpVar::<C::ScalarField>::new_variable(cs.clone(), || Ok(val.borrow().u), mode)?;
            let x: Vec<FpVar<C::ScalarField>> =
                Vec::new_variable(cs.clone(), || Ok(val.borrow().x.clone()), mode)?;
            let r_x: Vec<FpVar<C::ScalarField>> =
                Vec::new_variable(cs.clone(), || Ok(val.borrow().r_x.clone()), mode)?;
            let v: Vec<FpVar<C::ScalarField>> =
                Vec::new_variable(cs.clone(), || Ok(val.borrow().v.clone()), mode)?;

            Ok(Self { C, u, x, r_x, v })
        })
    }
}

/// ProofVar defines a multifolding proof
#[derive(Debug)]
pub struct ProofVar<C: CurveGroup> {
    pub sc_proof: IOPProofVar<C>,
    #[allow(clippy::type_complexity)]
    pub sigmas_thetas: (Vec<Vec<FpVar<CF1<C>>>>, Vec<Vec<FpVar<CF1<C>>>>),
}
impl<C> AllocVar<Proof<C>, CF1<C>> for ProofVar<C>
where
    C: CurveGroup,
    <C as ark_ec::CurveGroup>::BaseField: PrimeField,
    <C as Group>::ScalarField: Absorb,
{
    fn new_variable<T: Borrow<Proof<C>>>(
        cs: impl Into<Namespace<CF1<C>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|val| {
            let cs = cs.into();

            let sc_proof = IOPProofVar::<C>::new_variable(
                cs.clone(),
                || Ok(val.borrow().sc_proof.clone()),
                mode,
            )?;
            let sigmas: Vec<Vec<FpVar<CF1<C>>>> = val
                .borrow()
                .sigmas_thetas
                .0
                .iter()
                .map(|sigmas_i| Vec::new_variable(cs.clone(), || Ok(sigmas_i.clone()), mode))
                .collect::<Result<Vec<Vec<FpVar<CF1<C>>>>, SynthesisError>>()?;
            let thetas: Vec<Vec<FpVar<CF1<C>>>> = val
                .borrow()
                .sigmas_thetas
                .1
                .iter()
                .map(|thetas_i| Vec::new_variable(cs.clone(), || Ok(thetas_i.clone()), mode))
                .collect::<Result<Vec<Vec<FpVar<CF1<C>>>>, SynthesisError>>()?;

            Ok(Self {
                sc_proof,
                sigmas_thetas: (sigmas.clone(), thetas.clone()),
            })
        })
    }
}

pub struct NIMFSGadget<C: CurveGroup> {
    _c: PhantomData<C>,
}
impl<C: CurveGroup> NIMFSGadget<C>
where
    <C as CurveGroup>::BaseField: PrimeField,
{
    pub fn verify(
        cs: ConstraintSystemRef<CF1<C>>,
        // only used the CCS params, not the matrices
        ccs: &CCS<C::ScalarField>,
        mut transcript: impl TranscriptVar<C::ScalarField>,

        running_instances: &[LCCCSVar<C>],
        new_instances: &[CCCSVar<C>],
        proof: ProofVar<C>,
    ) -> Result<LCCCSVar<C>, SynthesisError> {
        // get the challenges
        let gamma_scalar_raw = C::ScalarField::from_le_bytes_mod_order(b"gamma");
        let gamma_scalar: FpVar<CF1<C>> =
            FpVar::<CF1<C>>::new_constant(cs.clone(), gamma_scalar_raw)?;
        transcript.absorb(gamma_scalar)?;
        let gamma: FpVar<CF1<C>> = transcript.get_challenge()?;

        let beta_scalar_raw = C::ScalarField::from_le_bytes_mod_order(b"beta");
        let beta_scalar: FpVar<CF1<C>> =
            FpVar::<CF1<C>>::new_constant(cs.clone(), beta_scalar_raw)?;
        transcript.absorb(beta_scalar)?;
        let beta: Vec<FpVar<CF1<C>>> = transcript.get_challenges(ccs.s)?;

        let vp_aux_info_raw = VPAuxInfo::<C::ScalarField> {
            max_degree: ccs.d + 1,
            num_variables: ccs.s,
            phantom: PhantomData::<C::ScalarField>,
        };
        let vp_aux_info = VPAuxInfoVar::<CF1<C>>::new_witness(cs.clone(), || Ok(vp_aux_info_raw))?;

        // sumcheck
        // first, compute the expected sumcheck sum: \sum gamma^j v_j
        let mut sum_v_j_gamma = FpVar::<CF1<C>>::zero();
        let mut gamma_j = FpVar::<C::ScalarField>::one();
        for running_instance in running_instances.iter() {
            for j in 0..running_instance.v.len() {
                gamma_j *= gamma.clone();
                sum_v_j_gamma += running_instance.v[j].clone() * gamma_j.clone();
            }
        }

        // verify the interactive part of the sumcheck
        let (e_vars, r_vars) =
            SumCheckVerifierGadget::<C>::verify(&proof.sc_proof, &vp_aux_info, &mut transcript)?;

        // extract the randomness from the sumcheck
        let r_x_prime = r_vars.clone();

        // verify the claim c
        let computed_c = compute_c_gadget(
            cs.clone(),
            ccs,
            proof.sigmas_thetas.0.clone(), // sigmas
            proof.sigmas_thetas.1.clone(), // thetas
            gamma,
            beta,
            running_instances
                .iter()
                .map(|lcccs| lcccs.r_x.clone())
                .collect(),
            r_x_prime.clone(),
        )?;
        computed_c.enforce_equal(&e_vars[e_vars.len() - 1])?;

        // get the folding challenge
        let rho_scalar_raw = C::ScalarField::from_le_bytes_mod_order(b"rho");
        let rho_scalar: FpVar<CF1<C>> = FpVar::<CF1<C>>::new_constant(cs.clone(), rho_scalar_raw)?;
        transcript.absorb(rho_scalar)?;
        let rho: FpVar<CF1<C>> = transcript.get_challenge()?;

        // return the folded instance
        Self::fold(
            running_instances,
            new_instances,
            proof.sigmas_thetas,
            r_x_prime,
            rho,
        )
    }

    #[allow(clippy::type_complexity)]
    fn fold(
        lcccs: &[LCCCSVar<C>],
        cccs: &[CCCSVar<C>],
        sigmas_thetas: (Vec<Vec<FpVar<CF1<C>>>>, Vec<Vec<FpVar<CF1<C>>>>),
        r_x_prime: Vec<FpVar<CF1<C>>>,
        rho: FpVar<CF1<C>>,
    ) -> Result<LCCCSVar<C>, SynthesisError> {
        let (sigmas, thetas) = (sigmas_thetas.0.clone(), sigmas_thetas.1.clone());
        let mut u_folded: FpVar<CF1<C>> = FpVar::zero();
        let mut x_folded: Vec<FpVar<CF1<C>>> = vec![FpVar::zero(); lcccs[0].x.len()];
        let mut v_folded: Vec<FpVar<CF1<C>>> = vec![FpVar::zero(); sigmas[0].len()];

        let mut rho_i = FpVar::one();
        for i in 0..(lcccs.len() + cccs.len()) {
            let u: FpVar<CF1<C>>;
            let x: Vec<FpVar<CF1<C>>>;
            let v: Vec<FpVar<CF1<C>>>;
            if i < lcccs.len() {
                u = lcccs[i].u.clone();
                x = lcccs[i].x.clone();
                v = sigmas[i].clone();
            } else {
                u = FpVar::one();
                x = cccs[i - lcccs.len()].x.clone();
                v = thetas[i - lcccs.len()].clone();
            }

            u_folded += rho_i.clone() * u;
            x_folded = x_folded
                .iter()
                .zip(
                    x.iter()
                        .map(|x_i| x_i * rho_i.clone())
                        .collect::<Vec<FpVar<CF1<C>>>>(),
                )
                .map(|(a_i, b_i)| a_i + b_i)
                .collect();

            v_folded = v_folded
                .iter()
                .zip(
                    v.iter()
                        .map(|x_i| x_i * rho_i.clone())
                        .collect::<Vec<FpVar<CF1<C>>>>(),
                )
                .map(|(a_i, b_i)| a_i + b_i)
                .collect();

            rho_i *= rho.clone();
        }

        Ok(LCCCSVar::<C> {
            C: lcccs[0].C.clone(), // WIP this will come from the cyclefold circuit
            u: u_folded,
            x: x_folded,
            r_x: r_x_prime,
            v: v_folded,
        })
    }
}

/// computes c from the step 5 in section 5 of HyperNova, adapted to multiple LCCCS & CCCS
/// instances:
/// $$
/// c = \sum_{i \in [\mu]} \left(\sum_{j \in [t]} \gamma^{i \cdot t + j} \cdot e_i \cdot \sigma_{i,j} \right)
/// + \sum_{k \in [\nu]} \gamma^{\mu \cdot t+k} \cdot e_k \cdot \left( \sum_{i=1}^q c_i \cdot \prod_{j \in S_i}
/// \theta_{k,j} \right)
/// $$
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
        folding::hypernova::{
            nimfs::NIMFS,
            utils::{compute_c, compute_sigmas_thetas},
        },
        transcript::{
            poseidon::{poseidon_canonical_config, PoseidonTranscript, PoseidonTranscriptVar},
            Transcript,
        },
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

        let sigmas_thetas = compute_sigmas_thetas(&ccs, &z_lcccs, &z_cccs, &r_x_prime).unwrap();

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

        assert_eq!(expected_c, computed_c.value().unwrap());
    }

    /// Test that generates mu>1 and nu>1 instances, and folds them in a single multifolding step,
    /// to verify the folding in the NIMFSGadget circuit
    #[test]
    pub fn test_nimfs_gadget_verify() {
        let mut rng = test_rng();

        // Create a basic CCS circuit
        let ccs = get_test_ccs::<Fr>();
        let (pedersen_params, _) =
            Pedersen::<Projective>::setup(&mut rng, ccs.n - ccs.l - 1).unwrap();

        let mu = 32;
        let nu = 42;

        // Generate a mu LCCCS & nu CCCS satisfying witness
        let mut z_lcccs = Vec::new();
        for i in 0..mu {
            let z = get_test_z(i + 3);
            z_lcccs.push(z);
        }
        let mut z_cccs = Vec::new();
        for i in 0..nu {
            let z = get_test_z(nu + i + 3);
            z_cccs.push(z);
        }

        // Create the LCCCS instances out of z_lcccs
        let mut lcccs_instances = Vec::new();
        let mut w_lcccs = Vec::new();
        for z_i in z_lcccs.iter() {
            let (running_instance, w) = ccs.to_lcccs(&mut rng, &pedersen_params, z_i).unwrap();
            lcccs_instances.push(running_instance);
            w_lcccs.push(w);
        }
        // Create the CCCS instance out of z_cccs
        let mut cccs_instances = Vec::new();
        let mut w_cccs = Vec::new();
        for z_i in z_cccs.iter() {
            let (new_instance, w) = ccs.to_cccs(&mut rng, &pedersen_params, z_i).unwrap();
            cccs_instances.push(new_instance);
            w_cccs.push(w);
        }

        // Prover's transcript
        let poseidon_config = poseidon_canonical_config::<Fr>();
        let mut transcript_p: PoseidonTranscript<Projective> =
            PoseidonTranscript::<Projective>::new(&poseidon_config);

        // Run the prover side of the multifolding
        let (proof, folded_lcccs, folded_witness) =
            NIMFS::<Projective, PoseidonTranscript<Projective>>::prove(
                &mut transcript_p,
                &ccs,
                &lcccs_instances,
                &cccs_instances,
                &w_lcccs,
                &w_cccs,
            )
            .unwrap();

        // Verifier's transcript
        let mut transcript_v: PoseidonTranscript<Projective> =
            PoseidonTranscript::<Projective>::new(&poseidon_config);

        // Run the verifier side of the multifolding
        let folded_lcccs_v = NIMFS::<Projective, PoseidonTranscript<Projective>>::verify(
            &mut transcript_v,
            &ccs,
            &lcccs_instances,
            &cccs_instances,
            proof.clone(),
        )
        .unwrap();
        assert_eq!(folded_lcccs, folded_lcccs_v);

        // Check that the folded LCCCS instance is a valid instance with respect to the folded witness
        folded_lcccs
            .check_relation(&pedersen_params, &ccs, &folded_witness)
            .unwrap();

        // allocate circuit inputs
        let cs = ConstraintSystem::<Fr>::new_ref();
        let lcccs_instancesVar =
            Vec::<LCCCSVar<Projective>>::new_witness(cs.clone(), || Ok(lcccs_instances.clone()))
                .unwrap();
        let cccs_instancesVar =
            Vec::<CCCSVar<Projective>>::new_witness(cs.clone(), || Ok(cccs_instances.clone()))
                .unwrap();
        let proofVar =
            ProofVar::<Projective>::new_witness(cs.clone(), || Ok(proof.clone())).unwrap();
        let transcriptVar = PoseidonTranscriptVar::<Fr>::new(cs.clone(), &poseidon_config);

        let folded_lcccsVar = NIMFSGadget::<Projective>::verify(
            cs.clone(),
            &ccs,
            transcriptVar,
            &lcccs_instancesVar,
            &cccs_instancesVar,
            proofVar,
        )
        .unwrap();
        assert!(cs.is_satisfied().unwrap());
        assert_eq!(folded_lcccsVar.u.value().unwrap(), folded_lcccs.u);
    }
}
