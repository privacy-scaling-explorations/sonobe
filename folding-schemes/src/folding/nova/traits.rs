use ark_ec::CurveGroup;
use ark_std::{rand::RngCore, One, UniformRand};

use super::{CommittedInstance, Witness};
use crate::arith::r1cs::{RelaxedR1CS, R1CS};
use crate::Error;

impl<C: CurveGroup> RelaxedR1CS<C, Witness<C>, CommittedInstance<C>> for R1CS<C::ScalarField> {
    fn dummy_running_instance(&self) -> (Witness<C>, CommittedInstance<C>) {
        let w_len = self.A.n_cols - 1 - self.l;
        let w_dummy = Witness::<C>::dummy(w_len, self.A.n_rows);
        let u_dummy = CommittedInstance::<C>::dummy(self.l);
        (w_dummy, u_dummy)
    }

    fn dummy_incoming_instance(&self) -> (Witness<C>, CommittedInstance<C>) {
        self.dummy_running_instance()
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

    fn sample<CS>(
        &self,
        params: &CS::ProverParams,
        mut rng: impl RngCore,
    ) -> Result<(Witness<C>, CommittedInstance<C>), Error>
    where
        CS: crate::commitment::CommitmentScheme<C, true>,
    {
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

        let E = <Self as RelaxedR1CS<C, Witness<C>, CommittedInstance<C>>>::compute_E(
            &self.A, &self.B, &self.C, &z, &u,
        )?;

        debug_assert!(
            z.len() == self.A.n_cols,
            "Length of z is {}, while A has {} columns.",
            z.len(),
            self.A.n_cols
        );

        let witness = Witness { E, rE, W, rW };
        let mut cm_witness = witness.commit::<CS, true>(params, x)?;

        // witness.commit() sets u to 1, we set it to the sampled u value
        cm_witness.u = u;

        debug_assert!(
            self.check_relaxed_relation(&witness, &cm_witness).is_ok(),
            "Sampled a non satisfiable relaxed R1CS, sampled u: {}, computed E: {:?}",
            u,
            witness.E
        );

        Ok((witness, cm_witness))
    }
}
