use ark_ec::CurveGroup;
use ark_std::{rand::RngCore, UniformRand};

use super::{CommittedInstance, Witness};
use crate::arith::ArithSampler;
use crate::arith::{r1cs::R1CS, Arith};
use crate::commitment::CommitmentScheme;
use crate::folding::circuits::CF1;
use crate::Error;

impl<C: CurveGroup> Arith<Witness<C>, CommittedInstance<C>> for R1CS<CF1<C>> {
    type Evaluation = Vec<CF1<C>>;

    fn eval_relation(
        &self,
        w: &Witness<C>,
        u: &CommittedInstance<C>,
    ) -> Result<Self::Evaluation, Error> {
        self.eval_core(&[&[u.u][..], &u.x, &w.W].concat())
    }

    fn check_evaluation(
        w: &Witness<C>,
        _u: &CommittedInstance<C>,
        e: Self::Evaluation,
    ) -> Result<(), Error> {
        (w.E == e).then_some(()).ok_or(Error::NotSatisfied)
    }
}

impl<C: CurveGroup> ArithSampler<C, Witness<C>, CommittedInstance<C>> for R1CS<CF1<C>> {
    fn sample_witness_instance<CS: CommitmentScheme<C, true>>(
        &self,
        params: &CS::ProverParams,
        mut rng: impl RngCore,
    ) -> Result<(Witness<C>, CommittedInstance<C>), Error> {
        // Implements sampling a (committed) RelaxedR1CS
        // See construction 5 in https://eprint.iacr.org/2023/573.pdf
        let u = C::ScalarField::rand(&mut rng);
        let rE = C::ScalarField::rand(&mut rng);
        let rW = C::ScalarField::rand(&mut rng);

        let W = (0..self.A.n_cols - self.l - 1)
            .map(|_| C::ScalarField::rand(&mut rng))
            .collect();
        let x = (0..self.l)
            .map(|_| C::ScalarField::rand(&mut rng))
            .collect::<Vec<C::ScalarField>>();
        let mut z = vec![u];
        z.extend(&x);
        z.extend(&W);

        let E = self.eval_core(&z)?;

        let witness = Witness { E, rE, W, rW };
        let mut cm_witness = witness.commit::<CS, true>(params, x)?;

        // witness.commit() sets u to 1, we set it to the sampled u value
        cm_witness.u = u;

        debug_assert!(
            self.check_relation(&witness, &cm_witness).is_ok(),
            "Sampled a non satisfiable relaxed R1CS, sampled u: {}, computed E: {:?}",
            u,
            witness.E
        );

        Ok((witness, cm_witness))
    }
}
