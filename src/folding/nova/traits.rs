use ark_crypto_primitives::{
    crh::{poseidon::CRH, CRHScheme},
    sponge::{poseidon::PoseidonConfig, Absorb},
};
use ark_ec::{CurveGroup, Group};
use ark_std::fmt::Debug;
use ark_std::{One, Zero};

use super::{CommittedInstance, Witness};
use crate::ccs::r1cs::R1CS;
use crate::folding::circuits::nonnative::point_to_nonnative_limbs;
use crate::pedersen::{Params as PedersenParams, Pedersen};
use crate::transcript::{poseidon::PoseidonTranscript, Transcript};
use crate::utils::vec::is_zero_vec;
use crate::Error;

/// NovaR1CS extends R1CS methods with Nova specific methods
pub trait NovaR1CS<C: CurveGroup> {
    /// returns a dummy instance (Witness and CommittedInstance) for the current R1CS structure
    fn dummy_instance(&self) -> (Witness<C>, CommittedInstance<C>);

    /// checks the Relaxed R1CS relation (corresponding to the current R1CS) for the given Witness
    /// and CommittedInstance.
    fn check_instance_relation(
        &self,
        W: &Witness<C>,
        U: &CommittedInstance<C>,
    ) -> Result<(), Error>;
}

impl<C: CurveGroup> NovaR1CS<C> for R1CS<C::ScalarField>
where
    <C as Group>::ScalarField: Absorb,
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
{
    fn dummy_instance(&self) -> (Witness<C>, CommittedInstance<C>) {
        let w_len = self.A.n_cols - 1 - self.l;
        let w_dummy = Witness::<C>::new(vec![C::ScalarField::zero(); w_len], self.A.n_rows);
        let u_dummy = CommittedInstance::<C>::dummy(self.l);
        (w_dummy, u_dummy)
    }

    fn check_instance_relation(
        &self,
        W: &Witness<C>,
        U: &CommittedInstance<C>,
    ) -> Result<(), Error> {
        let mut rel_r1cs = self.clone().relax();
        rel_r1cs.u = U.u;
        rel_r1cs.E = W.E.clone();

        let Z: Vec<C::ScalarField> = [vec![U.u], U.x.to_vec(), W.W.to_vec()].concat();
        rel_r1cs.check_relation(&Z)
    }
}

/// NovaTranscript extends Transcript with the method to absorb CommittedInstance.
pub trait NovaTranscript<C: CurveGroup>: Transcript<C> {
    fn absorb_committed_instance(&mut self, ci: CommittedInstance<C>) -> Result<(), Error> {
        self.absorb_point(&ci.cmE)?;
        self.absorb(&ci.u);
        self.absorb_point(&ci.cmW)?;
        self.absorb_vec(&ci.x);
        Ok(())
    }
}

// implements NovaTranscript for PoseidonTranscript
impl<C: CurveGroup> NovaTranscript<C> for PoseidonTranscript<C> where
    <C as Group>::ScalarField: Absorb
{
}
