use crate::arith::ccs::CCS;
use crate::arith::{r1cs::R1CS, Arith};
use crate::folding::circuits::CF1;
use crate::folding::mova::{CommittedInstance, Witness};
use crate::utils::mle::dense_vec_to_dense_mle;
use crate::utils::vec::mat_vec_mul;
use crate::Error;
use ark_ec::CurveGroup;

impl<C: CurveGroup> Arith<Witness<C>, CommittedInstance<C>> for R1CS<CF1<C>> {
    type Evaluation = Vec<CF1<C>>;

    fn eval_relation(
        &self,
        w: &Witness<C>,
        u: &CommittedInstance<C>,
    ) -> Result<Self::Evaluation, Error> {
        self.eval_at_z(&[&[u.u][..], &u.x, &w.W].concat())
    }

    fn check_evaluation(
        w: &Witness<C>,
        _u: &CommittedInstance<C>,
        e: Self::Evaluation,
    ) -> Result<(), Error> {
        (w.E == e).then_some(()).ok_or(Error::NotSatisfied)
    }
}
