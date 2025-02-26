/// contains [Nova](https://eprint.iacr.org/2021/370.pdf) NIFS related circuits
use ark_crypto_primitives::sponge::{constraints::AbsorbGadget, CryptographicSponge};
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    boolean::Boolean,
    eq::EqGadget,
    fields::{fp::FpVar, FieldVar},
    uint8::UInt8,
};
use ark_relations::r1cs::{ConstraintSystemRef, Namespace, SynthesisError};
use ark_std::{fmt::Debug, Zero};
use core::{borrow::Borrow, marker::PhantomData};

use super::NIFSGadgetTrait;
use crate::folding::traits::CommittedInstanceVarOps;
use crate::transcript::TranscriptVar;
use crate::{
    folding::circuits::{
        nonnative::{affine::NonNativeAffineVar, uint::NonNativeUintVar},
        CF1, CF2,
    },
    Curve,
};
use crate::{folding::nova::CommittedInstance, transcript::AbsorbNonNativeGadget};

use super::nova::ChallengeGadget;

/// CommittedInstanceVar contains the u, x, cmE and cmW values which are folded on the main Nova
/// constraints field (E1::Fr, where E1 is the main curve). The peculiarity is that cmE and cmW are
/// represented non-natively over the constraint field.
#[derive(Debug, Clone)]
pub struct CommittedInstanceVar<C: Curve> {
    pub u: FpVar<C::ScalarField>,
    pub x: Vec<FpVar<C::ScalarField>>,
    pub cmE: NonNativeAffineVar<C>,
    pub cmW: NonNativeAffineVar<C>,
}

impl<C: Curve> AllocVar<CommittedInstance<C>, CF1<C>> for CommittedInstanceVar<C> {
    fn new_variable<T: Borrow<CommittedInstance<C>>>(
        cs: impl Into<Namespace<CF1<C>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|val| {
            let cs = cs.into();

            let u = FpVar::<C::ScalarField>::new_variable(cs.clone(), || Ok(val.borrow().u), mode)?;
            let x: Vec<FpVar<C::ScalarField>> =
                Vec::new_variable(cs.clone(), || Ok(val.borrow().x.clone()), mode)?;

            let cmE =
                NonNativeAffineVar::<C>::new_variable(cs.clone(), || Ok(val.borrow().cmE), mode)?;
            let cmW =
                NonNativeAffineVar::<C>::new_variable(cs.clone(), || Ok(val.borrow().cmW), mode)?;

            Ok(Self { u, x, cmE, cmW })
        })
    }
}

impl<C: Curve> AbsorbGadget<C::ScalarField> for CommittedInstanceVar<C> {
    fn to_sponge_bytes(&self) -> Result<Vec<UInt8<C::ScalarField>>, SynthesisError> {
        FpVar::batch_to_sponge_bytes(&self.to_sponge_field_elements()?)
    }

    fn to_sponge_field_elements(&self) -> Result<Vec<FpVar<C::ScalarField>>, SynthesisError> {
        Ok([
            vec![self.u.clone()],
            self.x.clone(),
            self.cmE.to_native_sponge_field_elements()?,
            self.cmW.to_native_sponge_field_elements()?,
        ]
        .concat())
    }
}

impl<C: Curve> CommittedInstanceVarOps<C> for CommittedInstanceVar<C> {
    type PointVar = NonNativeAffineVar<C>;

    fn get_commitments(&self) -> Vec<Self::PointVar> {
        vec![self.cmW.clone(), self.cmE.clone()]
    }

    fn get_public_inputs(&self) -> &[FpVar<CF1<C>>] {
        &self.x
    }

    fn enforce_incoming(&self) -> Result<(), SynthesisError> {
        let zero = NonNativeUintVar::new_constant(ConstraintSystemRef::None, CF2::<C>::zero())?;
        self.cmE.x.enforce_equal_unaligned(&zero)?;
        self.cmE.y.enforce_equal_unaligned(&zero)?;
        self.u.enforce_equal(&FpVar::one())
    }

    fn enforce_partial_equal(&self, other: &Self) -> Result<(), SynthesisError> {
        self.u.enforce_equal(&other.u)?;
        self.x.enforce_equal(&other.x)
    }
}

/// Implements the circuit that does the checks of the Non-Interactive Folding Scheme Verifier
/// described in section 4 of [Nova](https://eprint.iacr.org/2021/370.pdf), where the cmE & cmW checks are
/// delegated to the NIFSCycleFoldGadget.
pub struct NIFSGadget<C: Curve, S: CryptographicSponge, T: TranscriptVar<CF1<C>, S>> {
    _c: PhantomData<C>,
    _s: PhantomData<S>,
    _t: PhantomData<T>,
}

impl<C, S, T> NIFSGadgetTrait<C, S, T> for NIFSGadget<C, S, T>
where
    C: Curve,
    S: CryptographicSponge,
    T: TranscriptVar<CF1<C>, S>,
{
    type CommittedInstance = CommittedInstance<C>;
    type CommittedInstanceVar = CommittedInstanceVar<C>;
    type Proof = C;
    type ProofVar = NonNativeAffineVar<C>;

    fn verify(
        transcript: &mut T,
        U_i: Self::CommittedInstanceVar,
        // U_i_vec is passed to reuse the already computed U_i_vec from previous methods
        U_i_vec: Vec<FpVar<CF1<C>>>,
        u_i: Self::CommittedInstanceVar,
        cmT: Option<Self::ProofVar>,
    ) -> Result<(Self::CommittedInstanceVar, Vec<Boolean<CF1<C>>>), SynthesisError> {
        let r_bits = ChallengeGadget::<C, CommittedInstance<C>>::get_challenge_gadget(
            transcript,
            U_i_vec,
            u_i.clone(),
            cmT.clone(),
        )?;
        let r = Boolean::le_bits_to_fp(&r_bits)?;

        Ok((
            Self::CommittedInstanceVar {
                cmE: NonNativeAffineVar::new_constant(ConstraintSystemRef::None, C::zero())?,
                cmW: NonNativeAffineVar::new_constant(ConstraintSystemRef::None, C::zero())?,
                // ci3.u = U_i.u + r * u_i.u
                u: U_i.u + &r * u_i.u,
                // ci3.x = U_i.x + r * u_i.x
                x: U_i
                    .x
                    .iter()
                    .zip(u_i.x)
                    .map(|(a, b)| a + &r * &b)
                    .collect::<Vec<FpVar<CF1<C>>>>(),
            },
            r_bits,
        ))
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use ark_crypto_primitives::sponge::poseidon::constraints::PoseidonSpongeVar;
    use ark_crypto_primitives::sponge::poseidon::PoseidonSponge;
    use ark_pallas::{Fr, Projective};
    use ark_r1cs_std::R1CSVar;
    use ark_std::UniformRand;

    use crate::commitment::pedersen::Pedersen;
    use crate::folding::nova::nifs::{
        nova::NIFS,
        tests::{
            test_committed_instance_hash_opt, test_committed_instance_to_sponge_preimage_opt,
            test_nifs_gadget_opt,
        },
    };
    use crate::Error;

    #[test]
    fn test_nifs_gadget() -> Result<(), Error> {
        let mut rng = ark_std::test_rng();
        // prepare the committed instances to test in-circuit
        let ci: Vec<CommittedInstance<Projective>> = (0..2)
            .into_iter()
            .map(|_| CommittedInstance::<Projective> {
                cmE: Projective::rand(&mut rng),
                u: Fr::rand(&mut rng),
                cmW: Projective::rand(&mut rng),
                x: vec![Fr::rand(&mut rng); 1],
            })
            .collect();
        let cmT = Projective::rand(&mut rng);

        let (ci_out, ciVar_out) = test_nifs_gadget_opt::<
            NIFS<Projective, Pedersen<Projective>, PoseidonSponge<Fr>>,
            NIFSGadget<Projective, PoseidonSponge<Fr>, PoseidonSpongeVar<Fr>>,
        >(ci, cmT)?;
        assert_eq!(ciVar_out.u.value()?, ci_out.u);
        assert_eq!(ciVar_out.x.value()?, ci_out.x);
        Ok(())
    }

    #[test]
    fn test_committed_instance_to_sponge_preimage() -> Result<(), Error> {
        let mut rng = ark_std::test_rng();
        let ci = CommittedInstance::<Projective> {
            cmE: Projective::rand(&mut rng),
            u: Fr::rand(&mut rng),
            cmW: Projective::rand(&mut rng),
            x: vec![Fr::rand(&mut rng); 1],
        };

        test_committed_instance_to_sponge_preimage_opt::<
            NIFS<Projective, Pedersen<Projective>, PoseidonSponge<Fr>>,
            NIFSGadget<Projective, PoseidonSponge<Fr>, PoseidonSpongeVar<Fr>>,
        >(ci)?;
        Ok(())
    }

    #[test]
    fn test_committed_instance_hash() -> Result<(), Error> {
        let mut rng = ark_std::test_rng();
        let ci = CommittedInstance::<Projective> {
            cmE: Projective::rand(&mut rng),
            u: Fr::rand(&mut rng),
            cmW: Projective::rand(&mut rng),
            x: vec![Fr::rand(&mut rng); 1],
        };
        test_committed_instance_hash_opt::<
            NIFS<Projective, Pedersen<Projective>, PoseidonSponge<Fr>>,
            NIFSGadget<Projective, PoseidonSponge<Fr>, PoseidonSpongeVar<Fr>>,
        >(ci)?;
        Ok(())
    }
}
