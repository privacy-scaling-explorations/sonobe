use ark_crypto_primitives::sponge::{constraints::AbsorbGadget, Absorb};
use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use ark_r1cs_std::{fields::fp::FpVar, uint8::UInt8, ToConstraintFieldGadget};
use ark_relations::r1cs::SynthesisError;
use ark_std::{cfg_iter, log2, rand::RngCore, One, Zero};
use rayon::prelude::*;

use super::{folding::pow_i, CommittedInstance, CommittedInstanceVar, Witness};
use crate::{
    arith::r1cs::{RelaxedR1CS, R1CS},
    transcript::AbsorbNonNative,
    Error,
};

// Implements the trait for absorbing ProtoGalaxy's CommittedInstance.
impl<C: CurveGroup> Absorb for CommittedInstance<C>
where
    C::ScalarField: Absorb,
{
    fn to_sponge_bytes(&self, _dest: &mut Vec<u8>) {
        unimplemented!()
    }

    fn to_sponge_field_elements<F: PrimeField>(&self, dest: &mut Vec<F>) {
        self.phi
            .to_native_sponge_field_elements_as_vec()
            .to_sponge_field_elements(dest);
        self.betas.to_sponge_field_elements(dest);
        self.e.to_sponge_field_elements(dest);
        self.x.to_sponge_field_elements(dest);
    }
}

// Implements the trait for absorbing ProtoGalaxy's CommittedInstanceVar in-circuit.
impl<C: CurveGroup> AbsorbGadget<C::ScalarField> for CommittedInstanceVar<C> {
    fn to_sponge_bytes(&self) -> Result<Vec<UInt8<C::ScalarField>>, SynthesisError> {
        unimplemented!()
    }

    fn to_sponge_field_elements(&self) -> Result<Vec<FpVar<C::ScalarField>>, SynthesisError> {
        Ok([
            self.phi.to_constraint_field()?,
            self.betas.to_sponge_field_elements()?,
            self.e.to_sponge_field_elements()?,
            self.x.to_sponge_field_elements()?,
        ]
        .concat())
    }
}

impl<C: CurveGroup> RelaxedR1CS<C, Witness<C::ScalarField>, CommittedInstance<C>>
    for R1CS<C::ScalarField>
{
    fn dummy_running_instance(&self) -> (Witness<C::ScalarField>, CommittedInstance<C>) {
        let w_len = self.A.n_cols - 1 - self.l;
        let w_dummy = Witness::new(vec![C::ScalarField::zero(); w_len]);
        let u_dummy = CommittedInstance::<C>::dummy_running(self.l, log2(self.A.n_rows) as usize);
        (w_dummy, u_dummy)
    }

    fn dummy_incoming_instance(&self) -> (Witness<C::ScalarField>, CommittedInstance<C>) {
        let w_len = self.A.n_cols - 1 - self.l;
        let w_dummy = Witness::new(vec![C::ScalarField::zero(); w_len]);
        let u_dummy = CommittedInstance::<C>::dummy_incoming(self.l);
        (w_dummy, u_dummy)
    }

    fn is_relaxed(_w: &Witness<C::ScalarField>, u: &CommittedInstance<C>) -> bool {
        u.e != C::ScalarField::zero() || !u.betas.is_empty()
    }

    fn extract_z(w: &Witness<C::ScalarField>, u: &CommittedInstance<C>) -> Vec<C::ScalarField> {
        [&[C::ScalarField::one()][..], &u.x, &w.w].concat()
    }

    fn check_error_terms(
        _w: &Witness<C::ScalarField>,
        u: &CommittedInstance<C>,
        e: Vec<C::ScalarField>,
    ) -> Result<(), Error> {
        if u.betas.len() != log2(e.len()) as usize {
            return Err(Error::NotSameLength(
                "instance.betas.len()".to_string(),
                u.betas.len(),
                "log2(e.len())".to_string(),
                log2(e.len()) as usize,
            ));
        }

        let r = cfg_iter!(e)
            .enumerate()
            .map(|(i, e_i)| pow_i(i, &u.betas) * e_i)
            .sum();
        if u.e == r {
            Ok(())
        } else {
            Err(Error::NotSatisfied)
        }
    }

    fn sample<CS>(
        &self,
        _params: &CS::ProverParams,
        _rng: impl RngCore,
    ) -> Result<(Witness<C::ScalarField>, CommittedInstance<C>), Error>
    where
        CS: crate::commitment::CommitmentScheme<C, true>,
    {
        // Sampling a random pair of witness and committed instance is required
        // for the zero-knowledge layer for ProtoGalaxy, which is not supported
        // yet.
        // Tracking issue: https://github.com/privacy-scaling-explorations/sonobe/issues/82
        unimplemented!()
    }
}
