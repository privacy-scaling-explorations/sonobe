use ark_ec::CurveGroup;
use ark_std::One;

use super::{CommittedInstance, Witness};
use crate::arith::r1cs::{RelaxedR1CS, R1CS};
use crate::Error;

impl<C: CurveGroup> RelaxedR1CS<C::ScalarField, Witness<C>, CommittedInstance<C>>
    for R1CS<C::ScalarField>
{
    fn dummy_instance(&self) -> (Witness<C>, CommittedInstance<C>) {
        let w_len = self.A.n_cols - 1 - self.l;
        let w_dummy = Witness::<C>::dummy(w_len, self.A.n_rows);
        let u_dummy = CommittedInstance::<C>::dummy(self.l);
        (w_dummy, u_dummy)
    }

    fn is_relaxed(_w: &Witness<C>, u: &CommittedInstance<C>) -> bool {
        u.cmE != C::zero() || u.u != C::ScalarField::one()
    }

    fn extract_z(w: &Witness<C>, u: &CommittedInstance<C>) -> Vec<C::ScalarField> {
        [&[u.u][..], &u.x, &w.W].concat()
    }

    fn check_error_terms(
        w: &Witness<C>,
        _u: &CommittedInstance<C>,
        e: Vec<C::ScalarField>,
    ) -> Result<(), Error> {
        if w.E == e {
            Ok(())
        } else {
            Err(Error::NotSatisfied)
        }
    }
}
