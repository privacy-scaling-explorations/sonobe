/// Implementation of [HyperNova](https://eprint.iacr.org/2023/573.pdf) circuits
use ark_crypto_primitives::sponge::{
    constraints::AbsorbGadget,
    poseidon::{constraints::PoseidonSpongeVar, PoseidonConfig, PoseidonSponge},
    CryptographicSponge,
};
use ark_ff::PrimeField;
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    boolean::Boolean,
    eq::EqGadget,
    fields::{fp::FpVar, FieldVar},
    uint8::UInt8,
    R1CSVar,
};
use ark_relations::r1cs::{
    ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, Namespace, SynthesisError,
};
use ark_std::{fmt::Debug, iter::Sum, One, Zero};
use core::{borrow::Borrow, marker::PhantomData};

use super::{
    cccs::CCCS,
    lcccs::LCCCS,
    nimfs::{NIMFSProof, NIMFS},
    HyperNovaCycleFoldConfig, Witness,
};
use crate::arith::{
    ccs::CCS,
    r1cs::{extract_r1cs, R1CS},
    Arith,
};
use crate::constants::NOVA_N_BITS_RO;
use crate::folding::{
    circuits::{
        cyclefold::{
            CycleFoldAugmentationGadget, CycleFoldCommittedInstance, CycleFoldCommittedInstanceVar,
            CycleFoldConfig,
        },
        nonnative::affine::NonNativeAffineVar,
        sum_check::{IOPProofVar, SumCheckVerifierGadget, VPAuxInfoVar},
        utils::EqEvalGadget,
        CF1,
    },
    nova::get_r1cs_from_cs,
    traits::{CommittedInstanceVarOps, Dummy},
};
use crate::frontend::FCircuit;
use crate::transcript::{AbsorbNonNativeGadget, Transcript, TranscriptVar};
use crate::utils::virtual_polynomial::VPAuxInfo;
use crate::{Curve, Error};

/// Committed CCS instance
#[derive(Debug, Clone)]
pub struct CCCSVar<C: Curve> {
    // Commitment to witness
    pub C: NonNativeAffineVar<C>,
    // Public io
    pub x: Vec<FpVar<CF1<C>>>,
}

impl<C: Curve> AllocVar<CCCS<C>, CF1<C>> for CCCSVar<C> {
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

impl<C: Curve> CommittedInstanceVarOps<C> for CCCSVar<C> {
    type PointVar = NonNativeAffineVar<C>;

    fn get_commitments(&self) -> Vec<Self::PointVar> {
        vec![self.C.clone()]
    }

    fn get_public_inputs(&self) -> &[FpVar<CF1<C>>] {
        &self.x
    }

    fn enforce_incoming(&self) -> Result<(), SynthesisError> {
        // `CCCSVar` is always the incoming instance
        Ok(())
    }

    fn enforce_partial_equal(&self, other: &Self) -> Result<(), SynthesisError> {
        self.x.enforce_equal(&other.x)
    }
}

impl<C: Curve> AbsorbGadget<C::ScalarField> for CCCSVar<C> {
    fn to_sponge_bytes(&self) -> Result<Vec<UInt8<C::ScalarField>>, SynthesisError> {
        FpVar::batch_to_sponge_bytes(&self.to_sponge_field_elements()?)
    }

    fn to_sponge_field_elements(&self) -> Result<Vec<FpVar<C::ScalarField>>, SynthesisError> {
        Ok([&self.C.to_native_sponge_field_elements()?, &self.x[..]].concat())
    }
}

/// Linearized Committed CCS instance
#[derive(Debug, Clone)]
pub struct LCCCSVar<C: Curve> {
    // Commitment to witness
    pub C: NonNativeAffineVar<C>,
    // Relaxation factor of z for folded LCCCS
    pub u: FpVar<CF1<C>>,
    // Public io
    pub x: Vec<FpVar<CF1<C>>>,
    // Random evaluation point for the v_i
    pub r_x: Vec<FpVar<CF1<C>>>,
    // Vector of v_i
    pub v: Vec<FpVar<CF1<C>>>,
}

impl<C: Curve> AllocVar<LCCCS<C>, CF1<C>> for LCCCSVar<C> {
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

impl<C: Curve> AbsorbGadget<C::ScalarField> for LCCCSVar<C> {
    fn to_sponge_bytes(&self) -> Result<Vec<UInt8<C::ScalarField>>, SynthesisError> {
        FpVar::batch_to_sponge_bytes(&self.to_sponge_field_elements()?)
    }

    fn to_sponge_field_elements(&self) -> Result<Vec<FpVar<C::ScalarField>>, SynthesisError> {
        Ok([
            &self.C.to_native_sponge_field_elements()?,
            &[self.u.clone()][..],
            &self.x,
            &self.r_x,
            &self.v,
        ]
        .concat())
    }
}

impl<C: Curve> CommittedInstanceVarOps<C> for LCCCSVar<C> {
    type PointVar = NonNativeAffineVar<C>;

    fn get_commitments(&self) -> Vec<Self::PointVar> {
        vec![self.C.clone()]
    }

    fn get_public_inputs(&self) -> &[FpVar<CF1<C>>] {
        &self.x
    }

    fn enforce_incoming(&self) -> Result<(), SynthesisError> {
        // `LCCCSVar` is always the running instance
        Err(SynthesisError::Unsatisfiable)
    }

    fn enforce_partial_equal(&self, other: &Self) -> Result<(), SynthesisError> {
        self.u.enforce_equal(&other.u)?;
        self.x.enforce_equal(&other.x)?;
        self.r_x.enforce_equal(&other.r_x)?;
        self.v.enforce_equal(&other.v)
    }
}

/// ProofVar defines a multifolding proof
#[derive(Debug)]
pub struct ProofVar<C: Curve> {
    pub sc_proof: IOPProofVar<C::ScalarField>,
    #[allow(clippy::type_complexity)]
    pub sigmas_thetas: (Vec<Vec<FpVar<CF1<C>>>>, Vec<Vec<FpVar<CF1<C>>>>),
}
impl<C: Curve> AllocVar<NIMFSProof<C>, CF1<C>> for ProofVar<C> {
    fn new_variable<T: Borrow<NIMFSProof<C>>>(
        cs: impl Into<Namespace<CF1<C>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|val| {
            let cs = cs.into();

            let sc_proof = IOPProofVar::<C::ScalarField>::new_variable(
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

pub struct NIMFSGadget<C: Curve> {
    _c: PhantomData<C>,
}
impl<C: Curve> NIMFSGadget<C> {
    /// Runs (in-circuit) the NIMFS.V, which outputs the new folded LCCCS instance together with
    /// the rho_powers, which will be used in other parts of the AugmentedFCircuit
    #[allow(clippy::type_complexity)]
    pub fn verify<S: CryptographicSponge, T: TranscriptVar<C::ScalarField, S>>(
        cs: ConstraintSystemRef<CF1<C>>,
        // only used the CCS params, not the matrices
        ccs: &CCS<C::ScalarField>,
        transcript: &mut T,
        running_instances: &[LCCCSVar<C>], // U
        new_instances: &[CCCSVar<C>],      // u
        proof: ProofVar<C>,
        enabled: Boolean<C::ScalarField>,
    ) -> Result<(LCCCSVar<C>, Vec<Boolean<CF1<C>>>), SynthesisError> {
        // absorb instances to transcript
        transcript.absorb(&running_instances)?;
        transcript.absorb(&new_instances)?;

        // get the challenges
        let gamma_scalar_raw = C::ScalarField::from_le_bytes_mod_order(b"gamma");
        let gamma_scalar: FpVar<CF1<C>> =
            FpVar::<CF1<C>>::new_constant(cs.clone(), gamma_scalar_raw)?;
        transcript.absorb(&gamma_scalar)?;
        let gamma: FpVar<CF1<C>> = transcript.get_challenge()?;

        let beta_scalar_raw = C::ScalarField::from_le_bytes_mod_order(b"beta");
        let beta_scalar: FpVar<CF1<C>> =
            FpVar::<CF1<C>>::new_constant(cs.clone(), beta_scalar_raw)?;
        transcript.absorb(&beta_scalar)?;
        let beta: Vec<FpVar<CF1<C>>> = transcript.get_challenges(ccs.s)?;

        let vp_aux_info_raw = VPAuxInfo::<C::ScalarField> {
            max_degree: ccs.degree() + 1,
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
        let (e_vars, r_vars) = SumCheckVerifierGadget::<C::ScalarField>::verify(
            &proof.sc_proof,
            &vp_aux_info,
            transcript,
            enabled.clone(),
        )?;

        // extract the randomness from the sumcheck
        let r_x_prime = r_vars.clone();

        // verify the claim c
        let computed_c = compute_c_gadget(
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
        computed_c.conditional_enforce_equal(&e_vars[e_vars.len() - 1], &enabled)?;

        // get the folding challenge
        let rho_scalar_raw = C::ScalarField::from_le_bytes_mod_order(b"rho");
        let rho_scalar: FpVar<CF1<C>> = FpVar::<CF1<C>>::new_constant(cs.clone(), rho_scalar_raw)?;
        transcript.absorb(&rho_scalar)?;
        let rho_bits: Vec<Boolean<CF1<C>>> = transcript.get_challenge_nbits(NOVA_N_BITS_RO)?;
        let rho = Boolean::le_bits_to_fp(&rho_bits)?;

        // Self::fold will return the folded instance
        let folded_lcccs = Self::fold(
            running_instances,
            new_instances,
            proof.sigmas_thetas,
            r_x_prime,
            rho,
        )?;
        // return the rho_bits so it can be used in other parts of the AugmentedFCircuit
        Ok((folded_lcccs, rho_bits))
    }

    /// Runs (in-circuit) the verifier side of the fold, computing the new folded LCCCS instance
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

            // compute the next power of rho
            rho_i *= rho.clone();
        }

        // return the folded instance, together with the rho's powers vector so they can be used in
        // other parts of the AugmentedFCircuit
        Ok(LCCCSVar::<C> {
            // C this is later overwritten by the U_{i+1}.C value checked by the cyclefold circuit
            C: lcccs[0].C.clone(),
            u: u_folded,
            x: x_folded,
            r_x: r_x_prime,
            v: v_folded,
        })
    }
}

/// Computes c from the step 5 in section 5 of HyperNova, adapted to multiple LCCCS & CCCS
/// instances:
/// $$
/// c = \sum_{i \in [\mu]} \left(\sum_{j \in [t]} \gamma^{i \cdot t + j} \cdot e_i \cdot \sigma_{i,j} \right) +
/// \sum_{k \in [\nu]} \gamma^{\mu \cdot t+k} \cdot e_k \cdot \left( \sum_{i=1}^q c_i \cdot \prod_{j \in S_i}
/// \theta_{k,j} \right)
/// $$
#[allow(clippy::too_many_arguments)]
fn compute_c_gadget<F: PrimeField>(
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
        for sigma in &vec_sigmas[i] {
            c += current_gamma.clone() * e_lcccs[i].clone() * sigma;
            current_gamma *= gamma.clone();
        }
    }

    let e_k = EqEvalGadget::eq_eval(&beta, &vec_r_x_prime)?;
    #[allow(clippy::needless_range_loop)]
    for k in 0..vec_thetas.len() {
        let prods = ccs.S.iter().zip(&ccs.c).map(|(S_i, &c_i)| {
            let mut prod = FpVar::<F>::one();
            for &j in S_i {
                prod *= &vec_thetas[k][j];
            }
            prod * c_i
        });
        let sum = FpVar::sum(prods);
        c += current_gamma.clone() * e_k.clone() * sum;
        current_gamma *= gamma.clone();
    }
    Ok(c)
}

/// `AugmentedFCircuit` enhances the original step function `F`, so that it can
/// be used in recursive arguments such as IVC.
///
/// The method for converting `F` to `AugmentedFCircuit` (`F'`) is defined in
/// [Nova](https://eprint.iacr.org/2021/370.pdf), where `AugmentedFCircuit` not
/// only invokes `F`, but also adds additional constraints for verifying the
/// correct folding of primary instances (i.e., the instances over `C1`).
/// In the paper, the primary instances are Nova's `CommittedInstance`, but we
/// extend this method to support using HyperNova's `LCCCS` and `CCCS` instances
/// as primary instances.
///
/// Furthermore, to reduce circuit size over `C2`, we implement the constraints
/// defined in [CycleFold](https://eprint.iacr.org/2023/1192.pdf). These extra
/// constraints verify the correct folding of CycleFold instances.
///
/// For multi-instance folding, one needs to specify the const generics below:
/// * `MU` - the number of LCCCS instances to be folded
/// * `NU` - the number of CCCS instances to be folded
#[derive(Debug, Clone)]
pub struct AugmentedFCircuit<
    C1: Curve,
    C2: Curve,
    FC: FCircuit<CF1<C1>>,
    const MU: usize,
    const NU: usize,
> {
    pub(super) poseidon_config: PoseidonConfig<CF1<C1>>,
    pub(super) ccs: CCS<C1::ScalarField>, // CCS of the AugmentedFCircuit
    pub(super) pp_hash: Option<CF1<C1>>,
    pub(super) i: Option<CF1<C1>>,
    pub(super) i_usize: Option<usize>,
    pub(super) z_0: Option<Vec<C1::ScalarField>>,
    pub(super) z_i: Option<Vec<C1::ScalarField>>,
    pub(super) external_inputs: Option<FC::ExternalInputs>,
    pub(super) U_i: Option<LCCCS<C1>>,
    pub(super) Us: Option<Vec<LCCCS<C1>>>, // other U_i's to be folded that are not the main running instance
    pub(super) u_i_C: Option<C1>,          // u_i.C
    pub(super) us: Option<Vec<CCCS<C1>>>, // other u_i's to be folded that are not the main incoming instance
    pub(super) U_i1_C: Option<C1>,        // U_{i+1}.C
    pub(super) F: FC,                     // F circuit
    pub(super) nimfs_proof: Option<NIMFSProof<C1>>,

    // cyclefold verifier on C1
    pub(super) cf_u_i_cmW: Option<C2>, // input, cf_u_i.cmW
    pub(super) cf_U_i: Option<CycleFoldCommittedInstance<C2>>, // input, RelaxedR1CS CycleFold instance
    pub(super) cf_cmT: Option<C2>,
}

impl<C1, C2, FC, const MU: usize, const NU: usize> AugmentedFCircuit<C1, C2, FC, MU, NU>
where
    C1: Curve<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    C2: Curve,
    FC: FCircuit<CF1<C1>>,
{
    pub fn default(
        poseidon_config: &PoseidonConfig<CF1<C1>>,
        F_circuit: FC,
        ccs: CCS<C1::ScalarField>,
    ) -> Result<Self, Error> {
        if MU < 1 || NU < 1 {
            return Err(Error::CantBeZero("mu,nu".to_string()));
        }
        Ok(Self {
            poseidon_config: poseidon_config.clone(),
            ccs,
            pp_hash: None,
            i: None,
            i_usize: None,
            z_0: None,
            z_i: None,
            external_inputs: None,
            U_i: None,
            Us: None,
            u_i_C: None,
            us: None,
            U_i1_C: None,
            F: F_circuit,
            nimfs_proof: None,
            cf_u_i_cmW: None,
            cf_U_i: None,
            cf_cmT: None,
        })
    }

    pub fn empty(
        poseidon_config: &PoseidonConfig<CF1<C1>>,
        F: FC, // FCircuit
        ccs: Option<CCS<C1::ScalarField>>,
    ) -> Result<Self, Error> {
        // create the initial ccs by converting from a dummy r1cs with m = 0,
        // n = 0, and l = 2 (i.e., 0 constraints, and 0 variables, and 2 public
        // inputs).
        // Here, `m` and `n` will be overwritten by the `compute_concrete_ccs`
        // method.
        let mut initial_ccs = CCS::from(R1CS::dummy((0, 0, 2)));
        // Although `s = log(m)` is undefined for `m = 0`, we set it to 1 here
        // because the circuit internally calls `IOPSumCheck::extract_sum` which
        // will panic if `s = 0` (0 is arkworks' fallback value for `log(0)`).
        // Similarly, `s` will also be overwritten by `compute_concrete_ccs`.
        initial_ccs.s = 1;
        let mut augmented_f_circuit = Self::default(poseidon_config, F, initial_ccs)?;
        augmented_f_circuit.ccs = ccs
            .ok_or(())
            .or_else(|_| augmented_f_circuit.compute_concrete_ccs())?;
        Ok(augmented_f_circuit)
    }

    /// This method computes the CCS parameters. This is used because there is a circular
    /// dependency between the AugmentedFCircuit CCS and the CCS parameters m & n & s.
    /// For a stable FCircuit circuit, the CCS parameters can be computed in advance and can be
    /// feed in as parameter for the AugmentedFCircuit::empty method to avoid computing them there.
    pub fn compute_concrete_ccs(&self) -> Result<CCS<C1::ScalarField>, Error> {
        let r1cs = get_r1cs_from_cs::<CF1<C1>>(self.clone())?;
        let mut ccs = CCS::from(r1cs);

        let z_0 = vec![C1::ScalarField::zero(); self.F.state_len()];
        let mut W_i = Witness::<C1::ScalarField>::dummy(&ccs);
        let mut U_i = LCCCS::<C1>::dummy(&ccs);
        let mut w_i = W_i.clone();
        let mut u_i = CCCS::<C1>::dummy(&ccs);

        let n_iters = 2;
        for _ in 0..n_iters {
            let Us = vec![U_i.clone(); MU - 1];
            let Ws = vec![W_i.clone(); MU - 1];
            let us = vec![u_i.clone(); NU - 1];
            let ws = vec![w_i.clone(); NU - 1];

            let all_Us = [vec![U_i.clone()], Us.clone()].concat();
            let all_us = [vec![u_i.clone()], us.clone()].concat();
            let all_Ws = [vec![W_i.clone()], Ws].concat();
            let all_ws = [vec![w_i.clone()], ws].concat();

            let mut transcript_p = PoseidonSponge::new_with_pp_hash(
                &self.poseidon_config.clone(),
                C1::ScalarField::zero(),
            );
            let (nimfs_proof, U_i1, _, _) = NIMFS::<C1, PoseidonSponge<C1::ScalarField>>::prove(
                &mut transcript_p,
                &ccs,
                &all_Us,
                &all_us,
                &all_Ws,
                &all_ws,
            )?;

            let augmented_f_circuit = Self {
                poseidon_config: self.poseidon_config.clone(),
                ccs: ccs.clone(),
                pp_hash: Some(C1::ScalarField::zero()),
                i: Some(C1::ScalarField::zero()),
                i_usize: Some(0),
                z_0: Some(z_0.clone()),
                z_i: Some(z_0.clone()),
                external_inputs: Some(FC::ExternalInputs::default()),
                U_i: Some(U_i.clone()),
                Us: Some(Us),
                u_i_C: Some(u_i.C),
                us: Some(us),
                U_i1_C: Some(U_i1.C),
                F: self.F.clone(),
                nimfs_proof: Some(nimfs_proof),
                // cyclefold values
                cf_u_i_cmW: None,
                cf_U_i: None,
                cf_cmT: None,
            };

            let cs: ConstraintSystem<C1::ScalarField>;
            (cs, ccs) = augmented_f_circuit.compute_cs_ccs()?;
            // prepare instances for next loop iteration
            use crate::arith::r1cs::extract_w_x;
            let (r1cs_w_i1, r1cs_x_i1) = extract_w_x::<C1::ScalarField>(&cs);
            u_i = CCCS::<C1> {
                C: u_i.C,
                x: r1cs_x_i1,
            };
            w_i = Witness::<C1::ScalarField> {
                w: r1cs_w_i1.clone(),
                r_w: C1::ScalarField::one(),
            };
            W_i = Witness::<C1::ScalarField>::dummy(&ccs);
            U_i = LCCCS::<C1>::dummy(&ccs);
        }
        Ok(ccs)
    }

    /// Returns the cs (ConstraintSystem) and the CCS out of the AugmentedFCircuit.
    /// Notice that in order to be able to internally call the `extract_r1cs` function, this method
    /// calls the `cs.finalize` method which consumes a noticeable portion of the time. If the CCS
    /// is not needed, directly generate the ConstraintSystem without calling the `finalize` method
    /// will save computing time.
    #[allow(clippy::type_complexity)]
    pub fn compute_cs_ccs(
        &self,
    ) -> Result<(ConstraintSystem<C1::ScalarField>, CCS<C1::ScalarField>), Error> {
        let cs = ConstraintSystem::<C1::ScalarField>::new_ref();
        self.clone().generate_constraints(cs.clone())?;
        cs.finalize();
        let cs = cs.into_inner().ok_or(Error::NoInnerConstraintSystem)?;
        let r1cs = extract_r1cs::<C1::ScalarField>(&cs)?;
        let ccs = CCS::from(r1cs);

        Ok((cs, ccs))
    }
}

impl<C1, C2, FC, const MU: usize, const NU: usize> AugmentedFCircuit<C1, C2, FC, MU, NU>
where
    C1: Curve<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    C2: Curve,
    FC: FCircuit<CF1<C1>>,
{
    pub fn compute_next_state(
        self,
        cs: ConstraintSystemRef<CF1<C1>>,
    ) -> Result<Vec<FpVar<CF1<C1>>>, SynthesisError> {
        let pp_hash = FpVar::<CF1<C1>>::new_witness(cs.clone(), || {
            Ok(self.pp_hash.unwrap_or_else(CF1::<C1>::zero))
        })?;
        let i = FpVar::<CF1<C1>>::new_witness(cs.clone(), || {
            Ok(self.i.unwrap_or_else(CF1::<C1>::zero))
        })?;
        let z_0 = Vec::<FpVar<CF1<C1>>>::new_witness(cs.clone(), || {
            Ok(self
                .z_0
                .unwrap_or(vec![CF1::<C1>::zero(); self.F.state_len()]))
        })?;
        let z_i = Vec::<FpVar<CF1<C1>>>::new_witness(cs.clone(), || {
            Ok(self
                .z_i
                .unwrap_or(vec![CF1::<C1>::zero(); self.F.state_len()]))
        })?;
        let external_inputs = FC::ExternalInputsVar::new_witness(cs.clone(), || {
            Ok(self.external_inputs.unwrap_or_default())
        })?;

        let U_dummy = LCCCS::<C1>::dummy(&self.ccs);
        let u_dummy = CCCS::<C1>::dummy(&self.ccs);

        let U_i =
            LCCCSVar::<C1>::new_witness(cs.clone(), || Ok(self.U_i.unwrap_or(U_dummy.clone())))?;
        let Us = Vec::<LCCCSVar<C1>>::new_witness(cs.clone(), || {
            Ok(self.Us.unwrap_or(vec![U_dummy.clone(); MU - 1]))
        })?;
        let us = Vec::<CCCSVar<C1>>::new_witness(cs.clone(), || {
            Ok(self.us.unwrap_or(vec![u_dummy.clone(); NU - 1]))
        })?;
        let U_i1_C = NonNativeAffineVar::new_witness(cs.clone(), || {
            Ok(self.U_i1_C.unwrap_or_else(C1::zero))
        })?;
        let nimfs_proof_dummy = NIMFSProof::<C1>::dummy((&self.ccs, MU, NU));
        let nimfs_proof = ProofVar::<C1>::new_witness(cs.clone(), || {
            Ok(self.nimfs_proof.unwrap_or(nimfs_proof_dummy))
        })?;

        let cf_u_dummy =
            CycleFoldCommittedInstance::dummy(HyperNovaCycleFoldConfig::<C1, MU, NU>::IO_LEN);
        let cf_U_i = CycleFoldCommittedInstanceVar::<C2>::new_witness(cs.clone(), || {
            Ok(self.cf_U_i.unwrap_or(cf_u_dummy.clone()))
        })?;
        let cf_cmT = C2::Var::new_witness(cs.clone(), || Ok(self.cf_cmT.unwrap_or_else(C2::zero)))?;

        let sponge = PoseidonSpongeVar::<C1::ScalarField>::new_with_pp_hash(
            &self.poseidon_config,
            &pp_hash,
        )?;
        let mut transcript = sponge.clone();

        let is_basecase = i.is_zero()?;
        let is_not_basecase = !&is_basecase;

        // Primary Part
        // P.1. Compute u_i.x
        // u_i.x[0] = H(i, z_0, z_i, U_i)
        let (u_i_x, _) = U_i.clone().hash(&sponge, &i, &z_0, &z_i)?;
        // u_i.x[1] = H(cf_U_i)
        let (cf_u_i_x, _) = cf_U_i.clone().hash(&sponge)?;

        // P.2. Construct u_i
        let u_i = CCCSVar::<C1> {
            // u_i.C is provided by the prover as witness
            C: NonNativeAffineVar::<C1>::new_witness(cs.clone(), || {
                Ok(self.u_i_C.unwrap_or(C1::zero()))
            })?,
            // u_i.x is computed in step 1
            x: vec![u_i_x, cf_u_i_x],
        };

        let all_Us = [vec![U_i.clone()], Us].concat();
        let all_us = [vec![u_i.clone()], us].concat();

        // P.3. NIMFS.verify, obtains U_{i+1} by folding [U_i] & [u_i].
        // Notice that NIMFSGadget::fold_committed_instance does not fold C. We set `U_i1.C` to
        // unconstrained witnesses `U_i1_C` respectively. Its correctness will be checked on the
        // other curve.
        let (mut U_i1, rho_bits) = NIMFSGadget::<C1>::verify(
            cs.clone(),
            &self.ccs.clone(),
            &mut transcript,
            &all_Us,
            &all_us,
            nimfs_proof,
            is_not_basecase.clone(),
        )?;
        U_i1.C = U_i1_C;

        // P.4.a compute and check the first output of F'

        // get z_{i+1} from the F circuit
        let i_usize = self.i_usize.unwrap_or(0);
        let z_i1 = self
            .F
            .generate_step_constraints(cs.clone(), i_usize, z_i, external_inputs)?;

        let (u_i1_x, _) =
            U_i1.clone()
                .hash(&sponge, &(i + FpVar::<CF1<C1>>::one()), &z_0, &z_i1)?;
        let (u_i1_x_base, _) = LCCCSVar::new_constant(cs.clone(), U_dummy)?.hash(
            &sponge,
            &FpVar::<CF1<C1>>::one(),
            &z_0,
            &z_i1,
        )?;
        let x = is_basecase.select(&u_i1_x_base, &u_i1_x)?;
        // This line "converts" `x` from a witness to a public input.
        // Instead of directly modifying the constraint system, we explicitly
        // allocate a public input and enforce that its value is indeed `x`.
        // While comparing `x` with itself seems redundant, this is necessary
        // because:
        // - `.value()` allows an honest prover to extract public inputs without
        //   computing them outside the circuit.
        // - `.enforce_equal()` prevents a malicious prover from claiming wrong
        //   public inputs that are not the honest `x` computed in-circuit.
        FpVar::new_input(cs.clone(), || x.value())?.enforce_equal(&x)?;

        // CycleFold part
        // C.1. Compute `cf_u_i.x`
        // C.2. Construct `cf_u_i`
        let cf_u_i = CycleFoldCommittedInstanceVar::new_incoming_from_components(
            // `cf_u_i.cmW` is provided by the prover as witness.
            C2::Var::new_witness(cs.clone(), || Ok(self.cf_u_i_cmW.unwrap_or(C2::zero())))?,
            // To construct `cf_u_i.x`, we need to provide the randomness
            // `rho_bits` and the `C` component in LCCCS and CCCS instances
            // `all_Us`, `all_us` and `U_{i+1}`.
            &rho_bits,
            all_Us
                .into_iter()
                .map(|U| U.C)
                .chain(all_us.into_iter().map(|u| u.C))
                .chain(vec![U_i1.C])
                .collect(),
        )?;

        // C.3. nifs.verify (fold_committed_instance), obtains cf_U_{i+1} by folding cf_u_i & cf_U_i.
        let cf_U_i1 = CycleFoldAugmentationGadget::fold_gadget(
            &mut transcript,
            cf_U_i,
            vec![cf_u_i],
            vec![cf_cmT],
        )?;

        // Back to Primary Part
        // P.4.b compute and check the second output of F'
        // Base case: u_{i+1}.x[1] == H(cf_U_{\bot})
        // Non-base case: u_{i+1}.x[1] == H(cf_U_{i+1})
        let (cf_u_i1_x, _) = cf_U_i1.clone().hash(&sponge)?;
        let (cf_u_i1_x_base, _) =
            CycleFoldCommittedInstanceVar::<C2>::new_constant(cs.clone(), cf_u_dummy)?
                .hash(&sponge)?;
        let cf_x = is_basecase.select(&cf_u_i1_x_base, &cf_u_i1_x)?;
        // This line "converts" `cf_x` from a witness to a public input.
        // Instead of directly modifying the constraint system, we explicitly
        // allocate a public input and enforce that its value is indeed `cf_x`.
        // While comparing `cf_x` with itself seems redundant, this is necessary
        // because:
        // - `.value()` allows an honest prover to extract public inputs without
        //   computing them outside the circuit.
        // - `.enforce_equal()` prevents a malicious prover from claiming wrong
        //   public inputs that are not the honest `cf_x` computed in-circuit.
        FpVar::new_input(cs.clone(), || cf_x.value())?.enforce_equal(&cf_x)?;

        Ok(z_i1)
    }
}

impl<C1, C2, FC, const MU: usize, const NU: usize> ConstraintSynthesizer<CF1<C1>>
    for AugmentedFCircuit<C1, C2, FC, MU, NU>
where
    C1: Curve<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    C2: Curve,
    FC: FCircuit<CF1<C1>>,
{
    fn generate_constraints(self, cs: ConstraintSystemRef<CF1<C1>>) -> Result<(), SynthesisError> {
        self.compute_next_state(cs).map(|_| ())
    }
}

#[cfg(test)]
mod tests {
    use ark_bn254::{Fq, Fr, G1Projective as Projective};
    use ark_crypto_primitives::sponge::Absorb;
    use ark_grumpkin::Projective as Projective2;
    use ark_std::{cmp::max, test_rng, time::Instant, UniformRand};

    use super::*;
    use crate::{
        arith::{
            ccs::tests::{get_test_ccs, get_test_z},
            r1cs::extract_w_x,
            ArithRelation,
        },
        commitment::{pedersen::Pedersen, CommitmentScheme},
        folding::{
            circuits::cyclefold::{CycleFoldCircuit, CycleFoldWitness},
            hypernova::utils::{compute_c, compute_sigmas_thetas},
            traits::CommittedInstanceOps,
        },
        frontend::utils::{cubic_step_native, CubicFCircuit},
        transcript::{poseidon::poseidon_canonical_config, Transcript},
    };

    #[test]
    pub fn test_compute_c_gadget() -> Result<(), Error> {
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

        let (pedersen_params, _) = Pedersen::<Projective>::setup(&mut rng, ccs.n_witnesses())?;

        // Create the LCCCS instances out of z_lcccs
        let mut lcccs_instances = Vec::new();
        for z_i in z_lcccs.iter() {
            let (inst, _) = ccs.to_lcccs::<_, _, Pedersen<Projective, true>, true>(
                &mut rng,
                &pedersen_params,
                z_i,
            )?;
            lcccs_instances.push(inst);
        }
        // Create the CCCS instance out of z_cccs
        let mut cccs_instances = Vec::new();
        for z_i in z_cccs.iter() {
            let (inst, _) =
                ccs.to_cccs::<_, _, Pedersen<Projective>, false>(&mut rng, &pedersen_params, z_i)?;
            cccs_instances.push(inst);
        }

        let sigmas_thetas = compute_sigmas_thetas(&ccs, &z_lcccs, &z_cccs, &r_x_prime)?;

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
        )?;

        let cs = ConstraintSystem::<Fr>::new_ref();
        let mut vec_sigmas = Vec::new();
        let mut vec_thetas = Vec::new();
        for sigmas in sigmas_thetas.0 {
            vec_sigmas.push(Vec::<FpVar<Fr>>::new_witness(cs.clone(), || {
                Ok(sigmas.clone())
            })?);
        }
        for thetas in sigmas_thetas.1 {
            vec_thetas.push(Vec::<FpVar<Fr>>::new_witness(cs.clone(), || {
                Ok(thetas.clone())
            })?);
        }
        let vec_r_x: Vec<Vec<FpVar<Fr>>> = lcccs_instances
            .iter()
            .map(|lcccs| Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(lcccs.r_x.clone())))
            .collect::<Result<Vec<_>, _>>()?;
        let vec_r_x_prime = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(r_x_prime.clone()))?;
        let gamma_var = FpVar::<Fr>::new_witness(cs.clone(), || Ok(gamma))?;
        let beta_var = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(beta.clone()))?;

        let computed_c = compute_c_gadget(
            &ccs,
            vec_sigmas,
            vec_thetas,
            gamma_var,
            beta_var,
            vec_r_x,
            vec_r_x_prime,
        )?;

        assert_eq!(expected_c, computed_c.value()?);
        Ok(())
    }

    /// Test that generates mu>1 and nu>1 instances, and folds them in a single multifolding step,
    /// to verify the folding in the NIMFSGadget circuit
    #[test]
    pub fn test_nimfs_gadget_verify() -> Result<(), Error> {
        let mut rng = test_rng();

        // Create a basic CCS circuit
        let ccs = get_test_ccs::<Fr>();
        let (pedersen_params, _) = Pedersen::<Projective>::setup(&mut rng, ccs.n_witnesses())?;

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
            let (running_instance, w) = ccs.to_lcccs::<_, _, Pedersen<Projective, false>, false>(
                &mut rng,
                &pedersen_params,
                z_i,
            )?;
            lcccs_instances.push(running_instance);
            w_lcccs.push(w);
        }
        // Create the CCCS instance out of z_cccs
        let mut cccs_instances = Vec::new();
        let mut w_cccs = Vec::new();
        for z_i in z_cccs.iter() {
            let (new_instance, w) =
                ccs.to_cccs::<_, _, Pedersen<Projective>, false>(&mut rng, &pedersen_params, z_i)?;
            cccs_instances.push(new_instance);
            w_cccs.push(w);
        }

        // Prover's transcript
        let poseidon_config = poseidon_canonical_config::<Fr>();
        let pp_hash = Fr::from(42u32); // only for test
        let mut transcript_p: PoseidonSponge<Fr> =
            PoseidonSponge::<Fr>::new_with_pp_hash(&poseidon_config, pp_hash);
        // Verifier's transcript
        let mut transcript_v: PoseidonSponge<Fr> = transcript_p.clone();

        // Run the prover side of the multifolding
        let (proof, folded_lcccs, folded_witness, _) =
            NIMFS::<Projective, PoseidonSponge<Fr>>::prove(
                &mut transcript_p,
                &ccs,
                &lcccs_instances,
                &cccs_instances,
                &w_lcccs,
                &w_cccs,
            )?;

        // Run the verifier side of the multifolding
        let folded_lcccs_v = NIMFS::<Projective, PoseidonSponge<Fr>>::verify(
            &mut transcript_v,
            &ccs,
            &lcccs_instances,
            &cccs_instances,
            proof.clone(),
        )?;
        assert_eq!(folded_lcccs, folded_lcccs_v);

        // Check that the folded LCCCS instance is a valid instance with respect to the folded witness
        ccs.check_relation(&folded_witness, &folded_lcccs)?;

        // allocate circuit inputs
        let cs = ConstraintSystem::<Fr>::new_ref();
        let lcccs_instancesVar =
            Vec::<LCCCSVar<Projective>>::new_witness(cs.clone(), || Ok(lcccs_instances.clone()))?;
        let cccs_instancesVar =
            Vec::<CCCSVar<Projective>>::new_witness(cs.clone(), || Ok(cccs_instances.clone()))?;
        let proofVar = ProofVar::<Projective>::new_witness(cs.clone(), || Ok(proof.clone()))?;
        let pp_hashVar = FpVar::<Fr>::new_witness(cs.clone(), || Ok(pp_hash))?;
        let mut transcriptVar =
            PoseidonSpongeVar::<Fr>::new_with_pp_hash(&poseidon_config, &pp_hashVar)?;

        let enabled = Boolean::<Fr>::new_witness(cs.clone(), || Ok(true))?;
        let (folded_lcccsVar, _) = NIMFSGadget::<Projective>::verify(
            cs.clone(),
            &ccs,
            &mut transcriptVar,
            &lcccs_instancesVar,
            &cccs_instancesVar,
            proofVar,
            enabled,
        )?;
        assert!(cs.is_satisfied()?);
        assert_eq!(folded_lcccsVar.u.value()?, folded_lcccs.u);
        Ok(())
    }

    /// test that checks the native LCCCS.to_sponge_{bytes,field_elements} vs
    /// the R1CS constraints version
    #[test]
    pub fn test_lcccs_to_sponge_preimage() -> Result<(), Error> {
        let mut rng = test_rng();

        let ccs = get_test_ccs();
        let z1 = get_test_z::<Fr>(3);

        let (pedersen_params, _) = Pedersen::<Projective>::setup(&mut rng, ccs.n_witnesses())?;

        let (lcccs, _) = ccs.to_lcccs::<_, _, Pedersen<Projective, true>, true>(
            &mut rng,
            &pedersen_params,
            &z1,
        )?;
        let bytes = lcccs.to_sponge_bytes_as_vec();
        let field_elements = lcccs.to_sponge_field_elements_as_vec();

        let cs = ConstraintSystem::<Fr>::new_ref();

        let lcccsVar = LCCCSVar::<Projective>::new_witness(cs.clone(), || Ok(lcccs))?;
        let bytes_var = lcccsVar.to_sponge_bytes()?;
        let field_elements_var = lcccsVar.to_sponge_field_elements()?;

        assert!(cs.is_satisfied()?);

        // check that the natively computed and in-circuit computed hashes match
        assert_eq!(bytes_var.value()?, bytes);
        assert_eq!(field_elements_var.value()?, field_elements);
        Ok(())
    }

    /// test that checks the native LCCCS.hash vs the R1CS constraints version
    #[test]
    pub fn test_lcccs_hash() -> Result<(), Error> {
        let mut rng = test_rng();
        let poseidon_config = poseidon_canonical_config::<Fr>();
        let pp_hash = Fr::from(42u32); // only for test
        let sponge = PoseidonSponge::<Fr>::new_with_pp_hash(&poseidon_config, pp_hash);

        let ccs = get_test_ccs();
        let z1 = get_test_z::<Fr>(3);

        let (pedersen_params, _) = Pedersen::<Projective>::setup(&mut rng, ccs.n_witnesses())?;

        let i = Fr::from(3_u32);
        let z_0 = vec![Fr::from(3_u32)];
        let z_i = vec![Fr::from(3_u32)];
        let (lcccs, _) = ccs.to_lcccs::<_, _, Pedersen<Projective, true>, true>(
            &mut rng,
            &pedersen_params,
            &z1,
        )?;
        let h = lcccs.clone().hash(&sponge, i, &z_0, &z_i);

        let cs = ConstraintSystem::<Fr>::new_ref();

        let pp_hashVar = FpVar::<Fr>::new_witness(cs.clone(), || Ok(pp_hash))?;
        let spongeVar = PoseidonSpongeVar::<Fr>::new_with_pp_hash(&poseidon_config, &pp_hashVar)?;
        let iVar = FpVar::<Fr>::new_witness(cs.clone(), || Ok(i))?;
        let z_0Var = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(z_0.clone()))?;
        let z_iVar = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(z_i.clone()))?;
        let lcccsVar = LCCCSVar::<Projective>::new_witness(cs.clone(), || Ok(lcccs))?;
        let (hVar, _) = lcccsVar.clone().hash(&spongeVar, &iVar, &z_0Var, &z_iVar)?;
        assert!(cs.is_satisfied()?);

        // check that the natively computed and in-circuit computed hashes match
        assert_eq!(hVar.value()?, h);
        Ok(())
    }

    #[test]
    pub fn test_augmented_f_circuit() -> Result<(), Error> {
        let mut rng = test_rng();
        let poseidon_config = poseidon_canonical_config::<Fr>();
        // public params hash
        let pp_hash = Fr::from(42u32); // only for test
        let sponge = PoseidonSponge::<Fr>::new_with_pp_hash(&poseidon_config, pp_hash);

        const MU: usize = 3;
        const NU: usize = 3;

        let start = Instant::now();
        let F_circuit = CubicFCircuit::<Fr>::new(())?;
        let mut augmented_f_circuit =
            AugmentedFCircuit::<Projective, Projective2, CubicFCircuit<Fr>, MU, NU>::empty(
                &poseidon_config,
                F_circuit,
                None,
            )?;
        let ccs = augmented_f_circuit.ccs.clone();
        println!("AugmentedFCircuit & CCS generation: {:?}", start.elapsed());
        println!("CCS m x n: {} x {}", ccs.n_constraints(), ccs.n_variables());

        // CycleFold circuit
        let cs2 = ConstraintSystem::<Fq>::new_ref();
        let cf_circuit =
            CycleFoldCircuit::<_, HyperNovaCycleFoldConfig<Projective, MU, NU>>::default();
        cf_circuit.generate_constraints(cs2.clone())?;
        cs2.finalize();
        let cs2 = cs2.into_inner().ok_or(Error::NoInnerConstraintSystem)?;
        let cf_r1cs = extract_r1cs::<Fq>(&cs2)?;
        println!(
            "CF m x n: {} x {}",
            cf_r1cs.n_constraints(),
            cf_r1cs.n_variables()
        );

        let (pedersen_params, _) = Pedersen::<Projective>::setup(&mut rng, ccs.n_witnesses())?;
        let (cf_pedersen_params, _) = Pedersen::<Projective2>::setup(
            &mut rng,
            max(cf_r1cs.n_constraints(), cf_r1cs.n_witnesses()),
        )?;

        // first step
        let z_0 = vec![Fr::from(3_u32)];
        let mut z_i = z_0.clone();

        // prepare the dummy instances
        let W_dummy = Witness::<Fr>::dummy(&ccs);
        let U_dummy = LCCCS::<Projective>::dummy(&ccs);
        let w_dummy = W_dummy.clone();
        let u_dummy = CCCS::<Projective>::dummy(&ccs);
        let (cf_W_dummy, cf_U_dummy): (
            CycleFoldWitness<Projective2>,
            CycleFoldCommittedInstance<Projective2>,
        ) = cf_r1cs.dummy_witness_instance();

        // set the initial dummy instances
        let mut W_i = W_dummy.clone();
        let mut U_i = U_dummy.clone();
        let mut w_i = w_dummy.clone();
        let mut u_i = u_dummy.clone();
        let mut cf_W_i = cf_W_dummy.clone();
        let mut cf_U_i = cf_U_dummy.clone();
        u_i.x = vec![
            U_i.hash(&sponge, Fr::zero(), &z_0, &z_i),
            cf_U_i.hash_cyclefold(&sponge),
        ];

        let n_steps: usize = 4;
        let mut iFr = Fr::zero();
        for i in 0..n_steps {
            let start = Instant::now();

            // for this test, let Us & us be just an array of copies of the U_i & u_i respectively
            let Us = vec![U_i.clone(); MU - 1];
            let Ws = vec![W_i.clone(); MU - 1];
            let us = vec![u_i.clone(); NU - 1];
            let ws = vec![w_i.clone(); NU - 1];
            let all_Us = [vec![U_i.clone()], Us.clone()].concat();
            let all_us = [vec![u_i.clone()], us.clone()].concat();
            let all_Ws = [vec![W_i.clone()], Ws].concat();
            let all_ws = [vec![w_i.clone()], ws].concat();

            let z_i1 = cubic_step_native(z_i.clone());

            let (U_i1, W_i1);

            let u_i1_x;
            let cf_u_i1_x;

            if i == 0 {
                W_i1 = Witness::<Fr>::dummy(&ccs);
                U_i1 = LCCCS::dummy(&ccs);

                u_i1_x = U_i1.hash(&sponge, Fr::one(), &z_0, &z_i1);

                // hash the initial (dummy) CycleFold instance, which is used as the 2nd public
                // input in the AugmentedFCircuit
                cf_u_i1_x = cf_U_i.hash_cyclefold(&sponge);

                augmented_f_circuit =
                    AugmentedFCircuit::<Projective, Projective2, CubicFCircuit<Fr>, MU, NU> {
                        poseidon_config: poseidon_config.clone(),
                        ccs: ccs.clone(),
                        pp_hash: Some(pp_hash),
                        i: Some(Fr::zero()),
                        i_usize: Some(0),
                        z_0: Some(z_0.clone()),
                        z_i: Some(z_i.clone()),
                        external_inputs: Some(()),
                        U_i: Some(U_i.clone()),
                        Us: Some(Us.clone()),
                        u_i_C: Some(u_i.C),
                        us: Some(us.clone()),
                        U_i1_C: Some(U_i1.C),
                        F: F_circuit,
                        nimfs_proof: None,

                        // cyclefold values
                        cf_u_i_cmW: None,
                        cf_U_i: None,
                        cf_cmT: None,
                    };
            } else {
                let mut transcript_p: PoseidonSponge<Fr> = sponge.clone();
                let (rho, nimfs_proof);
                (nimfs_proof, U_i1, W_i1, rho) = NIMFS::<Projective, PoseidonSponge<Fr>>::prove(
                    &mut transcript_p,
                    &ccs,
                    &all_Us,
                    &all_us,
                    &all_Ws,
                    &all_ws,
                )?;

                // sanity check: check the folded instance relation
                ccs.check_relation(&W_i1, &U_i1)?;

                u_i1_x = U_i1.hash(&sponge, iFr + Fr::one(), &z_0, &z_i1);

                // CycleFold part:
                let cf_config = HyperNovaCycleFoldConfig::<Projective, MU, NU> {
                    r: rho,
                    points: [
                        vec![U_i.clone().C],
                        Us.iter().map(|Us_i| Us_i.C).collect(),
                        vec![u_i.clone().C],
                        us.iter().map(|us_i| us_i.C).collect(),
                    ]
                    .concat(),
                };

                // ensure that the CycleFoldCircuit is well defined
                assert_eq!(
                    cf_config.points.len(),
                    HyperNovaCycleFoldConfig::<Projective, MU, NU>::N_INPUT_POINTS
                );

                let (cf_w_i, cf_u_i) = cf_config
                    .build_circuit()
                    .generate_incoming_instance_witness::<_, Pedersen<_>, false>(
                        &cf_pedersen_params,
                        &mut rng,
                    )?;
                let (cf_W_i1, cf_U_i1, cf_cmTs) =
                    CycleFoldAugmentationGadget::fold_native::<_, Pedersen<_>, false>(
                        &mut transcript_p,
                        &cf_r1cs,
                        &cf_pedersen_params,
                        cf_W_i,
                        cf_U_i.clone(),
                        vec![cf_w_i],
                        vec![cf_u_i.clone()],
                    )?;

                // hash the CycleFold folded instance, which is used as the 2nd public input in the
                // AugmentedFCircuit
                cf_u_i1_x = cf_U_i1.hash_cyclefold(&sponge);

                augmented_f_circuit =
                    AugmentedFCircuit::<Projective, Projective2, CubicFCircuit<Fr>, MU, NU> {
                        poseidon_config: poseidon_config.clone(),
                        ccs: ccs.clone(),
                        pp_hash: Some(pp_hash),
                        i: Some(iFr),
                        i_usize: Some(i),
                        z_0: Some(z_0.clone()),
                        z_i: Some(z_i.clone()),
                        external_inputs: Some(()),
                        U_i: Some(U_i.clone()),
                        Us: Some(Us.clone()),
                        u_i_C: Some(u_i.C),
                        us: Some(us.clone()),
                        U_i1_C: Some(U_i1.C),
                        F: F_circuit,
                        nimfs_proof: Some(nimfs_proof),

                        // cyclefold values
                        cf_u_i_cmW: Some(cf_u_i.cmW),
                        cf_U_i: Some(cf_U_i),
                        cf_cmT: Some(cf_cmTs[0]),
                    };

                // assign the next round instances
                cf_W_i = cf_W_i1;
                cf_U_i = cf_U_i1;
            }

            let cs = ConstraintSystem::<Fr>::new_ref();
            augmented_f_circuit
                .clone()
                .generate_constraints(cs.clone())?;
            let cs = cs.into_inner().ok_or(Error::NoInnerConstraintSystem)?;
            assert!(cs.is_satisfied()?);

            let (r1cs_w_i1, r1cs_x_i1) = extract_w_x::<Fr>(&cs); // includes 1 and public inputs
            assert_eq!(r1cs_x_i1[0], u_i1_x);
            let r1cs_z = [vec![Fr::one()], r1cs_x_i1.clone(), r1cs_w_i1.clone()].concat();
            // compute committed instances, w_{i+1}, u_{i+1}, which will be used as w_i, u_i, so we
            // assign them directly to w_i, u_i.
            (u_i, w_i) = ccs.to_cccs::<_, _, Pedersen<Projective>, false>(
                &mut rng,
                &pedersen_params,
                &r1cs_z,
            )?;
            ccs.check_relation(&w_i, &u_i)?;

            // sanity checks
            assert_eq!(w_i.w, r1cs_w_i1);
            assert_eq!(u_i.x, r1cs_x_i1);
            assert_eq!(u_i.x[0], u_i1_x);
            assert_eq!(u_i.x[1], cf_u_i1_x);
            let expected_u_i1_x = U_i1.hash(&sponge, iFr + Fr::one(), &z_0, &z_i1);
            let expected_cf_U_i1_x = cf_U_i.hash_cyclefold(&sponge);
            // u_i is already u_i1 at this point, check that has the expected value at x[0]
            assert_eq!(u_i.x[0], expected_u_i1_x);
            assert_eq!(u_i.x[1], expected_cf_U_i1_x);

            // set values for next iteration
            iFr += Fr::one();
            // assign z_{i+1} into z_i
            z_i = z_i1.clone();
            U_i = U_i1.clone();
            W_i = W_i1.clone();

            // check the new LCCCS instance relation
            ccs.check_relation(&W_i, &U_i)?;
            // check the new CCCS instance relation
            ccs.check_relation(&w_i, &u_i)?;

            // check the CycleFold instance relation
            cf_r1cs.check_relation(&cf_W_i, &cf_U_i)?;

            println!("augmented_f_circuit step {}: {:?}", i, start.elapsed());
        }
        Ok(())
    }
}
