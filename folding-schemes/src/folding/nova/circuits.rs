/// contains [Nova](https://eprint.iacr.org/2021/370.pdf) related circuits
use ark_crypto_primitives::sponge::poseidon::{
    constraints::PoseidonSpongeVar, PoseidonConfig, PoseidonSponge,
};
use ark_r1cs_std::{
    alloc::AllocVar,
    eq::EqGadget,
    fields::{fp::FpVar, FieldVar},
    R1CSVar,
};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_std::{fmt::Debug, Zero};

use super::{
    nifs::{
        nova_circuits::{CommittedInstanceVar, NIFSGadget},
        NIFSGadgetTrait,
    },
    CommittedInstance, NovaCycleFoldConfig,
};
use crate::frontend::{logup::LogUp, FCircuit};
use crate::Curve;
use crate::{
    folding::circuits::{
        cyclefold::{
            CycleFoldAugmentationGadget, CycleFoldCommittedInstance, CycleFoldCommittedInstanceVar,
            CycleFoldConfig,
        },
        nonnative::affine::NonNativeAffineVar,
        CF1,
    },
    transcript::TranscriptVar,
};
use crate::{
    folding::traits::{CommittedInstanceVarOps, Dummy},
    frontend::alloc::{ConstraintSystemStatistics, Query},
};

/// `AugmentedFCircuit` enhances the original step function `F`, so that it can
/// be used in recursive arguments such as IVC.
///
/// The method for converting `F` to `AugmentedFCircuit` (`F'`) is defined in
/// [Nova](https://eprint.iacr.org/2021/370.pdf), where `AugmentedFCircuit` not
/// only invokes `F`, but also adds additional constraints for verifying the
/// correct folding of primary instances (i.e., Nova's `CommittedInstance`s over
/// `C1`).
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
    pub(super) z_0: Vec<C1::ScalarField>,
    pub(super) z_i: Vec<C1::ScalarField>,
    pub(super) external_inputs: FC::ExternalInputs,
    pub(super) u_i_cmW: C1,
    pub(super) u_i_cmV: Option<C1>,
    pub(super) U_i: Option<CommittedInstance<C1>>,
    pub(super) U_i1_cmW: C1,
    pub(super) U_i1_cmV: Option<C1>,
    pub(super) U_i1_cmE: C1,
    pub(super) cmT: C1,
    pub(super) F: FC, // F circuit

    // cyclefold verifier on C1
    // Here 'cf1, cf2' are for each of the CycleFold circuits, corresponding to the fold of cmW and
    // cmE respectively
    pub(super) cf1_u_i_cmW: C2,                        // input
    pub(super) cf2_u_i_cmW: C2,                        // input
    pub(super) cf3_u_i_cmW: Option<C2>,                // input
    pub(super) cf_U_i: CycleFoldCommittedInstance<C2>, // input
    pub(super) cf1_cmT: C2,
    pub(super) cf2_cmT: C2,
    pub(super) cf3_cmT: Option<C2>,
}

impl<C1: Curve, C2: Curve, FC: FCircuit<CF1<C1>>> AugmentedFCircuit<C1, C2, FC> {
    pub fn empty(poseidon_config: &PoseidonConfig<CF1<C1>>, F_circuit: FC) -> Self {
        let cf_u_dummy =
            CycleFoldCommittedInstance::dummy((NovaCycleFoldConfig::<C1>::IO_LEN, false));

        Self {
            poseidon_config: poseidon_config.clone(),
            pp_hash: Zero::zero(),
            i: Zero::zero(),
            i_usize: 0,
            z_0: vec![Zero::zero(); F_circuit.state_len()],
            z_i: vec![Zero::zero(); F_circuit.state_len()],
            external_inputs: FC::ExternalInputs::default(),
            u_i_cmW: Zero::zero(),
            u_i_cmV: None,
            U_i: None,
            U_i1_cmW: Zero::zero(),
            U_i1_cmV: None,
            U_i1_cmE: Zero::zero(),
            cmT: Zero::zero(),
            F: F_circuit,
            // cyclefold values
            cf1_u_i_cmW: Zero::zero(),
            cf2_u_i_cmW: Zero::zero(),
            cf3_u_i_cmW: None,
            cf_U_i: cf_u_dummy,
            cf1_cmT: Zero::zero(),
            cf2_cmT: Zero::zero(),
            cf3_cmT: None,
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

        // get z_{i+1} from the F circuit
        let z_i1 = self.F.generate_step_constraints(
            cs.clone(),
            self.i_usize,
            z_i.clone(),
            external_inputs,
        )?;

        let lookup_enabled = cs.has_variables_of_type::<Query>();

        let u_dummy = CommittedInstance::dummy(if lookup_enabled {
            (3, true)
        } else {
            (2, false)
        });
        let U_i = CommittedInstanceVar::<C1>::new_witness(cs.clone(), || {
            if cs.is_in_setup_mode() {
                Ok(u_dummy.clone())
            } else {
                self.U_i.ok_or(SynthesisError::AssignmentMissing)
            }
        })?;
        let u_i_cmW = NonNativeAffineVar::new_witness(cs.clone(), || Ok(self.u_i_cmW))?;
        let u_i_cmV = if lookup_enabled {
            Some(NonNativeAffineVar::new_witness(cs.clone(), || {
                if cs.is_in_setup_mode() {
                    Ok(Zero::zero())
                } else {
                    self.u_i_cmV.ok_or(SynthesisError::AssignmentMissing)
                }
            })?)
        } else {
            None
        };

        let cmT = NonNativeAffineVar::new_witness(cs.clone(), || Ok(self.cmT))?;

        let cf_u_dummy =
            CycleFoldCommittedInstance::dummy((NovaCycleFoldConfig::<C1>::IO_LEN, false));
        let cf_U_i =
            CycleFoldCommittedInstanceVar::<C2>::new_witness(cs.clone(), || Ok(self.cf_U_i))?;
        let cf1_cmT = C2::Var::new_witness(cs.clone(), || Ok(self.cf1_cmT))?;
        let cf2_cmT = C2::Var::new_witness(cs.clone(), || Ok(self.cf2_cmT))?;
        let cf3_cmT = if lookup_enabled {
            Some(C2::Var::new_witness(cs.clone(), || {
                if cs.is_in_setup_mode() {
                    Ok(Zero::zero())
                } else {
                    self.cf3_cmT.ok_or(SynthesisError::AssignmentMissing)
                }
            })?)
        } else {
            None
        };

        // `sponge` is for digest computation.
        let sponge = PoseidonSpongeVar::<C1::ScalarField>::new_with_pp_hash(
            &self.poseidon_config,
            &pp_hash,
        )?;
        // `transcript` is for challenge generation.
        let mut transcript = sponge.clone();

        let is_basecase = i.is_zero()?;

        // Primary Part
        // P.1. Compute u_i.x
        // u_i.x[0] = H(i, z_0, z_i, U_i)
        let (x0, U_i_vec) = U_i.clone().hash(&sponge, &i, &z_0, &z_i)?;
        // u_i.x[1] = H(cf_U_i)
        let (x1, _) = cf_U_i.clone().hash(&sponge)?;
        // u_i.x[2] = H...
        let x2 = if lookup_enabled {
            Some(LogUp::challenge_gadget(&sponge, &u_i_cmW)?)
        } else {
            None
        };

        // P.2. Construct u_i
        let u_i = CommittedInstanceVar {
            // u_i.cmE = cm(0)
            cmE: NonNativeAffineVar::new_constant(cs.clone(), C1::zero())?,
            // u_i.u = 1
            u: FpVar::one(),
            // u_i.cmW is provided by the prover as witness
            cmW: u_i_cmW,
            cmV: u_i_cmV,
            // u_i.x is computed in step 1
            x: if let Some(x2) = x2 {
                vec![x0, x1, x2]
            } else {
                vec![x0, x1]
            },
        };

        // P.3. nifs.verify, obtains U_{i+1} by folding u_i & U_i.
        // Notice that NIFSGadget::verify does not fold cmE & cmW.
        // We set `U_i1.cmE` and `U_i1.cmW` to unconstrained witnesses `U_i1_cmE` and `U_i1_cmW`
        // respectively.
        // The correctness of them will be checked on the other curve.
        let (mut U_i1, r_bits) = NIFSGadget::<
            C1,
            PoseidonSponge<C1::ScalarField>,
            PoseidonSpongeVar<C1::ScalarField>,
        >::verify(
            &mut transcript,
            U_i.clone(),
            U_i_vec,
            u_i.clone(),
            Some(cmT.clone()),
        )?;
        U_i1.cmE = NonNativeAffineVar::new_witness(cs.clone(), || Ok(self.U_i1_cmE))?;
        U_i1.cmW = NonNativeAffineVar::new_witness(cs.clone(), || Ok(self.U_i1_cmW))?;
        U_i1.cmV = if lookup_enabled {
            Some(NonNativeAffineVar::new_witness(cs.clone(), || {
                if cs.is_in_setup_mode() {
                    Ok(Zero::zero())
                } else {
                    self.U_i1_cmV.ok_or(SynthesisError::AssignmentMissing)
                }
            })?)
        } else {
            None
        };

        // P.4.a compute and check the first output of F'
        // Base case: u_{i+1}.x[0] == H((i+1, z_0, z_{i+1}, U_{\bot})
        // Non-base case: u_{i+1}.x[0] == H((i+1, z_0, z_{i+1}, U_{i+1})
        let (u_i1_x, _) =
            U_i1.clone()
                .hash(&sponge, &(i + FpVar::<CF1<C1>>::one()), &z_0, &z_i1)?;
        let (u_i1_x_base, _) = CommittedInstanceVar::new_constant(cs.clone(), u_dummy)?.hash(
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
        // C.1. Compute cf1_u_i.x and cf2_u_i.x
        // C.2. Construct `cf1_u_i` and `cf2_u_i`
        let cf1_u_i = CycleFoldCommittedInstanceVar::new_incoming_from_components(
            // `cf1_u_i.cmW` is provided by the prover as witness.
            C2::Var::new_witness(cs.clone(), || Ok(self.cf1_u_i_cmW))?,
            // To construct `cf1_u_i.x`, we need to provide the randomness
            // `r_bits`, the `cmE` component in running instances `U_i` and
            // `U_{i+1}`, and the cross term commitment `cmT`.
            &r_bits,
            vec![U_i.cmE, cmT, U_i1.cmE],
        )?;
        let cf2_u_i = CycleFoldCommittedInstanceVar::new_incoming_from_components(
            // `cf2_u_i.cmW` is provided by the prover as witness.
            C2::Var::new_witness(cs.clone(), || Ok(self.cf2_u_i_cmW))?,
            // To construct `cf2_u_i.x`, we need to provide the randomness
            // `r_bits` and the `cmW` component in committed instances `U_i`,
            // `u_i`, and `U_{i+1}`.
            &r_bits,
            vec![U_i.cmW, u_i.cmW, U_i1.cmW],
        )?;
        let cf3_u_i = if lookup_enabled {
            Some(CycleFoldCommittedInstanceVar::new_incoming_from_components(
                // `cf3_u_i.cmW` is provided by the prover as witness.
                C2::Var::new_witness(cs.clone(), || {
                    if cs.is_in_setup_mode() {
                        Ok(Zero::zero())
                    } else {
                        self.cf3_u_i_cmW.ok_or(SynthesisError::AssignmentMissing)
                    }
                })?,
                // To construct `cf3_u_i.x`, we need to provide the randomness
                // `r_bits` and the `cmW` component in committed instances `U_i`,
                // `u_i`, and `U_{i+1}`.
                &r_bits,
                vec![U_i.cmV.unwrap(), u_i.cmV.unwrap(), U_i1.cmV.unwrap()],
            )?)
        } else {
            None
        };

        // C.3. nifs.verify, obtains cf_U_{i+1} by folding cf1_u_i and cf2_u_i into cf_U.
        let cf_U_i1 = CycleFoldAugmentationGadget::fold_gadget(
            &mut transcript,
            cf_U_i,
            if let Some(cf3_u_i) = cf3_u_i {
                vec![cf1_u_i, cf2_u_i, cf3_u_i]
            } else {
                vec![cf1_u_i, cf2_u_i]
            },
            if let Some(cf3_cmT) = cf3_cmT {
                vec![cf1_cmT, cf2_cmT, cf3_cmT]
            } else {
                vec![cf1_cmT, cf2_cmT]
            },
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
pub mod tests {
    use super::*;
    use ark_bn254::{Fr, G1Projective as Projective};
    use ark_crypto_primitives::sponge::{constraints::AbsorbGadget, poseidon::PoseidonSponge};
    use ark_ff::{BigInteger, PrimeField};

    use ark_r1cs_std::prelude::Boolean;
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::UniformRand;

    use crate::folding::nova::nifs::nova::ChallengeGadget;
    use crate::transcript::{poseidon::poseidon_canonical_config, Transcript};
    use crate::Error;

    // checks that the gadget and native implementations of the challenge computation match
    #[test]
    fn test_challenge_gadget() -> Result<(), Error> {
        let mut rng = ark_std::test_rng();
        let poseidon_config = poseidon_canonical_config::<Fr>();
        let pp_hash = Fr::from(42u32); // only for testing
        let mut transcript = PoseidonSponge::<Fr>::new_with_pp_hash(&poseidon_config, pp_hash);

        let u_i = CommittedInstance::<Projective> {
            cmE: Projective::rand(&mut rng),
            u: Fr::rand(&mut rng),
            cmW: Projective::rand(&mut rng),
            cmV: None,
            x: vec![Fr::rand(&mut rng); 1],
        };
        let U_i = CommittedInstance::<Projective> {
            cmE: Projective::rand(&mut rng),
            u: Fr::rand(&mut rng),
            cmW: Projective::rand(&mut rng),
            cmV: None,
            x: vec![Fr::rand(&mut rng); 1],
        };
        let cmT = Projective::rand(&mut rng);

        // compute the challenge natively
        let r_bits =
            ChallengeGadget::<Projective, CommittedInstance<Projective>>::get_challenge_native(
                &mut transcript,
                &U_i,
                &u_i,
                Some(&cmT),
            );
        let r = Fr::from_bigint(BigInteger::from_bits_le(&r_bits)).ok_or(Error::OutOfBounds)?;

        let cs = ConstraintSystem::<Fr>::new_ref();
        let pp_hashVar = FpVar::<Fr>::new_witness(cs.clone(), || Ok(pp_hash))?;
        let u_iVar =
            CommittedInstanceVar::<Projective>::new_witness(cs.clone(), || Ok(u_i.clone()))?;
        let U_iVar =
            CommittedInstanceVar::<Projective>::new_witness(cs.clone(), || Ok(U_i.clone()))?;
        let cmTVar = NonNativeAffineVar::<Projective>::new_witness(cs.clone(), || Ok(cmT))?;
        let mut transcriptVar =
            PoseidonSpongeVar::<Fr>::new_with_pp_hash(&poseidon_config, &pp_hashVar)?;

        // compute the challenge in-circuit
        let r_bitsVar =
            ChallengeGadget::<Projective, CommittedInstance<Projective>>::get_challenge_gadget(
                &mut transcriptVar,
                U_iVar.to_sponge_field_elements()?,
                u_iVar,
                Some(cmTVar),
            )?;
        assert!(cs.is_satisfied()?);

        // check that the natively computed and in-circuit computed hashes match
        let rVar = Boolean::le_bits_to_fp(&r_bitsVar)?;
        assert_eq!(rVar.value()?, r);
        assert_eq!(r_bitsVar.value()?, r_bits);
        Ok(())
    }
}
