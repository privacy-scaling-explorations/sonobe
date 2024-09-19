use crate::arith::r1cs::R1CS;
use crate::folding::mova::{CommittedInstance, Witness};
use crate::Error;
use ark_crypto_primitives::sponge::Absorb;
use ark_ec::{CurveGroup, Group};

///MovaR1CS extends R1CS methods with Mova specific methods
pub trait MovaR1CS<C: CurveGroup> {
    /// checks the R1CS relation (un-relaxed) for the given Witness and CommittedInstance.
    fn check_instance_relation(
        &self,
        W: &Witness<C>,
        U: &CommittedInstance<C>,
    ) -> Result<(), Error>;

    /// checks the Relaxed R1CS relation (corresponding to the current R1CS) for the given Witness
    /// and CommittedInstance.
    fn check_relaxed_instance_relation(
        &self,
        W: &Witness<C>,
        U: &CommittedInstance<C>,
    ) -> Result<(), Error>;
}

impl<C: CurveGroup> MovaR1CS<C> for R1CS<C::ScalarField>
where
    <C as Group>::ScalarField: Absorb,
    <C as CurveGroup>::BaseField: ark_ff::PrimeField,
{
    fn check_instance_relation(
        &self,
        _W: &Witness<C>,
        _U: &CommittedInstance<C>,
    ) -> Result<(), Error> {
        // This is never called
        unimplemented!()
    }

    fn check_relaxed_instance_relation(
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
