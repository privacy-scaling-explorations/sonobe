use ark_crypto_primitives::sponge::{
    constraints::CryptographicSpongeVar,
    poseidon::{constraints::PoseidonSpongeVar, PoseidonConfig},
    CryptographicSponge,
};
use ark_poly::{univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain};
use ark_r1cs_std::{
    alloc::AllocVar,
    convert::ToBitsGadget,
    eq::EqGadget,
    fields::{fp::FpVar, FieldVar},
    poly::polynomial::univariate::dense::DensePolynomialVar,
    R1CSVar,
};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_std::{fmt::Debug, Zero};

use super::{
    folding::lagrange_polys,
    utils::{all_powers_var, betas_star_var, exponential_powers_var},
    CommittedInstance, CommittedInstanceVar, ProtoGalaxyCycleFoldConfig,
};
use crate::{
    folding::{
        circuits::{
            cyclefold::{
                CycleFoldAugmentationGadget, CycleFoldCommittedInstance,
                CycleFoldCommittedInstanceVar, CycleFoldConfig,
            },
            nonnative::affine::NonNativeAffineVar,
            CF1,
        },
        traits::{CommittedInstanceVarOps, Dummy},
    },
    frontend::FCircuit,
    transcript::TranscriptVar,
    utils::gadgets::VectorGadget,
    Curve,
};

pub struct FoldingGadget {}

impl FoldingGadget {
    #[allow(clippy::type_complexity)]
    pub fn fold_committed_instance<C: Curve, S: CryptographicSponge>(
        transcript: &mut impl TranscriptVar<C::ScalarField, S>,
        // running instance
        instance: &CommittedInstanceVar<C, true>,
        // incoming instances
        vec_instances: &[CommittedInstanceVar<C, false>],
        // polys from P
        F_coeffs: Vec<FpVar<C::ScalarField>>,
        K_coeffs: Vec<FpVar<C::ScalarField>>,
    ) -> Result<(CommittedInstanceVar<C, true>, Vec<FpVar<C::ScalarField>>), SynthesisError> {
        let t = instance.betas.len();

        // absorb the committed instances
        transcript.absorb(instance)?;
        transcript.absorb(&vec_instances)?;

        let delta = transcript.get_challenge()?;
        let deltas = exponential_powers_var(delta, t);

        transcript.absorb(&F_coeffs)?;

        let alpha = transcript.get_challenge()?;
        let alphas = all_powers_var(alpha.clone(), t);

        // F(alpha) = e + \sum_t F_i * alpha^i
        let mut F_alpha = instance.e.clone();
        for (i, F_i) in F_coeffs.iter().skip(1).enumerate() {
            F_alpha += F_i * &alphas[i + 1];
        }

        let betas_star = betas_star_var(&instance.betas, &deltas, &alpha);

        let k = vec_instances.len();
        let H =
            GeneralEvaluationDomain::new(k + 1).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let L_X = lagrange_polys(H)
            .into_iter()
            .map(|poly| {
                DensePolynomialVar::from_coefficients_vec(
                    poly.coeffs
                        .into_iter()
                        .map(FpVar::constant)
                        .collect::<Vec<_>>(),
                )
            })
            .collect::<Vec<_>>();
        let Z_X = DensePolynomialVar::from_coefficients_vec(
            DensePolynomial::from(H.vanishing_polynomial())
                .coeffs
                .into_iter()
                .map(FpVar::constant)
                .collect::<Vec<_>>(),
        );
        let K_X = DensePolynomialVar { coeffs: K_coeffs };

        transcript.absorb(&K_X.coeffs)?;

        let gamma = transcript.get_challenge()?;

        let L_X_evals = L_X
            .iter()
            .take(k + 1)
            .map(|L| L.evaluate(&gamma))
            .collect::<Result<Vec<_>, _>>()?;

        let e_star = F_alpha * &L_X_evals[0] + Z_X.evaluate(&gamma)? * K_X.evaluate(&gamma)?;

        let mut x_star = instance.x.mul_scalar(&L_X_evals[0])?;
        for i in 0..k {
            x_star = x_star.add(&vec_instances[i].x.mul_scalar(&L_X_evals[i + 1])?)?;
        }

        // return the folded instance
        Ok((
            CommittedInstanceVar {
                betas: betas_star,
                // phi will be computed in CycleFold
                phi: NonNativeAffineVar::new_constant(ConstraintSystemRef::None, C::zero())?,
                e: e_star,
                x: x_star,
            },
            L_X_evals,
        ))
    }
}

pub struct AugmentationGadget;

impl AugmentationGadget {
    #[allow(clippy::type_complexity)]
    pub fn prepare_and_fold_primary<C: Curve, S: CryptographicSponge>(
        transcript: &mut impl TranscriptVar<CF1<C>, S>,
        U: CommittedInstanceVar<C, true>,
        u_phis: Vec<NonNativeAffineVar<C>>,
        u_xs: Vec<Vec<FpVar<CF1<C>>>>,
        new_U_phi: NonNativeAffineVar<C>,
        F_coeffs: Vec<FpVar<CF1<C>>>,
        K_coeffs: Vec<FpVar<CF1<C>>>,
    ) -> Result<(CommittedInstanceVar<C, true>, Vec<FpVar<CF1<C>>>), SynthesisError> {
        assert_eq!(u_phis.len(), u_xs.len());

        // Prepare the incoming instances.
        // For each instance `u`, we have `u.betas = []`, `u.e = 0`.
        let us = u_phis
            .into_iter()
            .zip(u_xs)
            .map(|(phi, x)| CommittedInstanceVar {
                phi,
                betas: vec![],
                e: FpVar::zero(),
                x,
            })
            .collect::<Vec<_>>();

        // Fold the incoming instances `us` into the running instance `U`.
        let (mut U, L_X_evals) =
            FoldingGadget::fold_committed_instance(transcript, &U, &us, F_coeffs, K_coeffs)?;
        // Notice that FoldingGadget::fold_committed_instance does not fold phi.
        // We set `U.phi` to unconstrained witnesses `U_phi` here, whose
        // correctness will be checked on the other curve.
        U.phi = new_U_phi;

        Ok((U, L_X_evals))
    }
}

/// `AugmentedFCircuit` enhances the original step function `F`, so that it can
/// be used in recursive arguments such as IVC.
///
/// The method for converting `F` to `AugmentedFCircuit` (`F'`) is defined in
/// [Nova](https://eprint.iacr.org/2021/370.pdf), where `AugmentedFCircuit` not
/// only invokes `F`, but also adds additional constraints for verifying the
/// correct folding of primary instances (i.e., the instances over `C1`).
/// In the paper, the primary instances are Nova's `CommittedInstance`, but we
/// extend this method to support using ProtoGalaxy's `CommittedInstance` as
/// primary instances.
///
/// Furthermore, to reduce circuit size over `C2`, we implement the constraints
/// defined in [CycleFold](https://eprint.iacr.org/2023/1192.pdf). These extra
/// constraints verify the correct folding of CycleFold instances.
#[derive(Debug, Clone)]
pub struct AugmentedFCircuit<C1: Curve, C2: Curve, FC: FCircuit<CF1<C1>>> {
    pub(super) poseidon_config: PoseidonConfig<CF1<C1>>,
    pub(super) pp_hash: CF1<C1>,
    pub(super) i: CF1<C1>,
    pub(super) i_usize: usize,
    pub(super) z_0: Vec<CF1<C1>>,
    pub(super) z_i: Vec<CF1<C1>>,
    pub(super) external_inputs: FC::ExternalInputs,
    pub(super) F: FC, // F circuit
    pub(super) u_i_phi: C1,
    pub(super) U_i: CommittedInstance<C1, true>,
    pub(super) U_i1_phi: C1,
    pub(super) F_coeffs: Vec<CF1<C1>>,
    pub(super) K_coeffs: Vec<CF1<C1>>,

    pub(super) cf_u_i_cmW: C2,                         // input
    pub(super) cf_U_i: CycleFoldCommittedInstance<C2>, // input
    pub(super) cf_cmT: C2,
}

impl<C1: Curve, C2: Curve, FC: FCircuit<CF1<C1>>> AugmentedFCircuit<C1, C2, FC> {
    pub fn empty(
        poseidon_config: &PoseidonConfig<CF1<C1>>,
        F_circuit: FC,
        t: usize,
        d: usize,
        k: usize,
    ) -> Self {
        let u_dummy = CommittedInstance::dummy((2, t));
        let cf_u_dummy =
            CycleFoldCommittedInstance::dummy(ProtoGalaxyCycleFoldConfig::<C1>::IO_LEN);

        Self {
            poseidon_config: poseidon_config.clone(),
            pp_hash: CF1::<C1>::zero(),
            i: CF1::<C1>::zero(),
            i_usize: 0,
            z_0: vec![CF1::<C1>::zero(); F_circuit.state_len()],
            z_i: vec![CF1::<C1>::zero(); F_circuit.state_len()],
            external_inputs: FC::ExternalInputs::default(),
            u_i_phi: C1::zero(),
            U_i: u_dummy,
            U_i1_phi: C1::zero(),
            F_coeffs: vec![CF1::<C1>::zero(); t],
            K_coeffs: vec![CF1::<C1>::zero(); d * k + 1],
            F: F_circuit,
            // cyclefold values
            cf_u_i_cmW: C2::zero(),
            cf_U_i: cf_u_dummy,
            cf_cmT: C2::zero(),
        }
    }
}

impl<C1, C2, FC> AugmentedFCircuit<C1, C2, FC>
where
    C1: Curve<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    C2: Curve,
    FC: FCircuit<CF1<C1>>,
{
    pub fn compute_next_state(
        self,
        cs: ConstraintSystemRef<CF1<C1>>,
    ) -> Result<Vec<FpVar<CF1<C1>>>, SynthesisError> {
        let pp_hash = FpVar::<CF1<C1>>::new_witness(cs.clone(), || Ok(self.pp_hash))?;
        let i = FpVar::<CF1<C1>>::new_witness(cs.clone(), || Ok(self.i))?;
        let z_0 = Vec::<FpVar<CF1<C1>>>::new_witness(cs.clone(), || Ok(self.z_0))?;
        let z_i = Vec::<FpVar<CF1<C1>>>::new_witness(cs.clone(), || Ok(self.z_i))?;
        let external_inputs =
            FC::ExternalInputsVar::new_witness(cs.clone(), || Ok(self.external_inputs))?;

        let u_dummy = CommittedInstance::<C1, true>::dummy((2, self.U_i.betas.len()));
        let U_i = CommittedInstanceVar::<C1, true>::new_witness(cs.clone(), || Ok(self.U_i))?;
        let u_i_phi = NonNativeAffineVar::new_witness(cs.clone(), || Ok(self.u_i_phi))?;
        let U_i1_phi = NonNativeAffineVar::new_witness(cs.clone(), || Ok(self.U_i1_phi))?;

        let cf_u_dummy =
            CycleFoldCommittedInstance::dummy(ProtoGalaxyCycleFoldConfig::<C1>::IO_LEN);
        let cf_U_i =
            CycleFoldCommittedInstanceVar::<C2>::new_witness(cs.clone(), || Ok(self.cf_U_i))?;
        let cf_cmT = C2::Var::new_witness(cs.clone(), || Ok(self.cf_cmT))?;

        let F_coeffs = Vec::new_witness(cs.clone(), || Ok(self.F_coeffs))?;
        let K_coeffs = Vec::new_witness(cs.clone(), || Ok(self.K_coeffs))?;

        // `sponge` is for digest computation.
        let sponge = PoseidonSpongeVar::<C1::ScalarField>::new(cs.clone(), &self.poseidon_config);
        // `transcript` is for challenge generation.
        let mut transcript = sponge.clone();

        let is_basecase = i.is_zero()?;

        // Primary Part
        // P.1. Compute u_i.x
        // u_i.x[0] = H(i, z_0, z_i, U_i)
        let (u_i_x, _) = U_i.clone().hash(&sponge, &pp_hash, &i, &z_0, &z_i)?;
        // u_i.x[1] = H(cf_U_i)
        let (cf_u_i_x, _) = cf_U_i.clone().hash(&sponge, pp_hash.clone())?;

        // P.2. Prepare incoming primary instances
        // P.3. Fold incoming primary instances into the running instance
        let (U_i1, r) = AugmentationGadget::prepare_and_fold_primary(
            &mut transcript,
            U_i.clone(),
            vec![u_i_phi.clone()],
            vec![vec![u_i_x, cf_u_i_x]],
            U_i1_phi,
            F_coeffs,
            K_coeffs,
        )?;

        // P.4.a compute and check the first output of F'

        // get z_{i+1} from the F circuit
        let z_i1 =
            self.F
                .generate_step_constraints(cs.clone(), self.i_usize, z_i, external_inputs)?;

        // Base case: u_{i+1}.x[0] == H((i+1, z_0, z_{i+1}, U_{\bot})
        // Non-base case: u_{i+1}.x[0] == H((i+1, z_0, z_{i+1}, U_{i+1})
        let (u_i1_x, _) = U_i1.clone().hash(
            &sponge,
            &pp_hash,
            &(i + FpVar::<CF1<C1>>::one()),
            &z_0,
            &z_i1,
        )?;
        let (u_i1_x_base, _) = CommittedInstanceVar::new_constant(cs.clone(), u_dummy)?.hash(
            &sponge,
            &pp_hash,
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
            C2::Var::new_witness(cs.clone(), || Ok(self.cf_u_i_cmW))?,
            // To construct `cf_u_i.x`, we need to provide the randomness `r` as
            // well as the `phi` component in committed instances `U_i`, `u_i`,
            // and `U_{i+1}`.
            // Note that the randomness `r` is converted to `r_0, r_1 / r_0` due
            // to how `ProtoGalaxyCycleFoldConfig::alloc_randomnesses` creates
            // randomness in the CycleFold circuit.
            &[
                r[0].to_bits_le()?,
                r[1].mul_by_inverse(&r[0])?.to_bits_le()?,
            ]
            .concat(),
            vec![U_i.phi, u_i_phi, U_i1.phi],
        )?;

        // C.2. Prepare incoming CycleFold instances
        // C.3. Fold incoming CycleFold instances into the running instance
        let cf_U_i1 = CycleFoldAugmentationGadget::fold_gadget(
            &mut transcript,
            &pp_hash,
            cf_U_i,
            vec![cf_u_i],
            vec![cf_cmT],
        )?;

        // Back to Primary Part
        // P.4.b compute and check the second output of F'
        // Base case: u_{i+1}.x[1] == H(cf_U_{\bot})
        // Non-base case: u_{i+1}.x[1] == H(cf_U_{i+1})
        let (cf_u_i1_x, _) = cf_U_i1.clone().hash(&sponge, pp_hash.clone())?;
        let (cf_u_i1_x_base, _) =
            CycleFoldCommittedInstanceVar::<C2>::new_constant(cs.clone(), cf_u_dummy)?
                .hash(&sponge, pp_hash.clone())?;
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

impl<C1, C2, FC> ConstraintSynthesizer<CF1<C1>> for AugmentedFCircuit<C1, C2, FC>
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

    use super::*;
    use crate::{
        arith::r1cs::tests::get_test_r1cs,
        folding::protogalaxy::folding::{tests::prepare_inputs, Folding},
        transcript::poseidon::poseidon_canonical_config,
        Error,
    };

    use ark_bn254::{Fr, G1Projective as Projective};
    use ark_crypto_primitives::sponge::poseidon::PoseidonSponge;
    use ark_relations::r1cs::ConstraintSystem;

    #[test]
    fn test_folding_gadget() -> Result<(), Error> {
        let k = 7;
        let (witness, instance, witnesses, instances) = prepare_inputs(k)?;
        let r1cs = get_test_r1cs::<Fr>();

        // init Prover & Verifier's transcript
        let poseidon_config = poseidon_canonical_config::<Fr>();
        let mut transcript_p = PoseidonSponge::new(&poseidon_config);
        let mut transcript_v = PoseidonSponge::new(&poseidon_config);

        let (_, _, proof, _) = Folding::<Projective>::prove(
            &mut transcript_p,
            &r1cs,
            &instance,
            &witness,
            &instances,
            &witnesses,
        )?;

        let folded_instance =
            Folding::<Projective>::verify(&mut transcript_v, &instance, &instances, proof.clone())?;

        let cs = ConstraintSystem::new_ref();
        let mut transcript_var = PoseidonSpongeVar::new(cs.clone(), &poseidon_config);
        let instance_var = CommittedInstanceVar::new_witness(cs.clone(), || Ok(instance))?;
        let instances_var = Vec::new_witness(cs.clone(), || Ok(instances))?;
        let F_coeffs_var = Vec::new_witness(cs.clone(), || Ok(proof.F_coeffs))?;
        let K_coeffs_var = Vec::new_witness(cs.clone(), || Ok(proof.K_coeffs))?;

        let (folded_instance_var, _) = FoldingGadget::fold_committed_instance(
            &mut transcript_var,
            &instance_var,
            &instances_var,
            F_coeffs_var,
            K_coeffs_var,
        )?;
        assert_eq!(folded_instance.betas, folded_instance_var.betas.value()?);
        assert_eq!(folded_instance.e, folded_instance_var.e.value()?);
        assert_eq!(folded_instance.x, folded_instance_var.x.value()?);
        assert!(cs.is_satisfied()?);
        Ok(())
    }
}
