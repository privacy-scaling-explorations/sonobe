use ark_crypto_primitives::sponge::Absorb;
use ark_ff::PrimeField;
use ark_serialize::CanonicalDeserialize;
use ark_serialize::CanonicalSerialize;
use ark_std::{rand::Rng, sync::Arc, One, Zero};

use super::circuits::CCCSVar;
use super::Witness;
use crate::arith::{ccs::CCS, Arith, ArithRelation};
use crate::commitment::CommitmentScheme;
use crate::folding::circuits::CF1;
use crate::folding::traits::Inputize;
use crate::folding::traits::{CommittedInstanceOps, Dummy};
use crate::utils::mle::dense_vec_to_dense_mle;
use crate::utils::vec::{is_zero_vec, mat_vec_mul};
use crate::utils::virtual_polynomial::{build_eq_x_r_vec, VirtualPolynomial};
use crate::{Curve, Error};

/// Committed CCS instance
#[derive(Debug, Clone, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct CCCS<C: Curve> {
    // Commitment to witness
    pub C: C,
    // Public input/output
    pub x: Vec<C::ScalarField>,
}

impl<F: PrimeField> CCS<F> {
    pub fn to_cccs<R: Rng, C, CS: CommitmentScheme<C, H>, const H: bool>(
        &self,
        rng: &mut R,
        cs_params: &CS::ProverParams,
        z: &[F],
    ) -> Result<(CCCS<C>, Witness<F>), Error>
    where
        // enforce that CCS's F is the C::ScalarField
        C: Curve<ScalarField = F>,
    {
        let (w, x) = self.split_z(z);

        // if the commitment scheme is set to be hiding, set the random blinding parameter
        let r_w = if CS::is_hiding() {
            F::rand(rng)
        } else {
            F::zero()
        };
        let C = CS::commit(cs_params, &w, &r_w)?;

        Ok((CCCS::<C> { C, x }, Witness::<F> { w, r_w }))
    }

    /// Computes q(x) = \sum^q c_i * \prod_{j \in S_i} ( \sum_{y \in {0,1}^s'} M_j(x, y) * z(y) )
    /// polynomial over x
    pub fn compute_q(&self, z: &[F]) -> Result<VirtualPolynomial<F>, Error> {
        let mut q_x = VirtualPolynomial::<F>::new(self.s);
        for (S_i, &c_i) in self.S.iter().zip(&self.c) {
            let mut Q_k = vec![];
            for &j in S_i {
                Q_k.push(Arc::new(dense_vec_to_dense_mle(
                    self.s,
                    &mat_vec_mul(&self.M[j], z)?,
                )));
            }
            q_x.add_mle_list(Q_k, c_i)?;
        }
        Ok(q_x)
    }

    /// Computes Q(x) = eq(beta, x) * q(x)
    ///               = eq(beta, x) * \sum^q c_i * \prod_{j \in S_i} ( \sum_{y \in {0,1}^s'} M_j(x, y) * z(y) )
    /// polynomial over x
    pub fn compute_Q(&self, z: &[F], beta: &[F]) -> Result<VirtualPolynomial<F>, Error> {
        let eq_beta = build_eq_x_r_vec(beta)?;
        let eq_beta_mle = Arc::new(dense_vec_to_dense_mle(self.s, &eq_beta));

        let mut Q = VirtualPolynomial::<F>::new(self.s);
        for (S_i, &c_i) in self.S.iter().zip(&self.c) {
            let mut Q_k = vec![];
            for &j in S_i {
                Q_k.push(Arc::new(dense_vec_to_dense_mle(
                    self.s,
                    &mat_vec_mul(&self.M[j], z)?,
                )));
            }
            Q_k.push(eq_beta_mle.clone());
            Q.add_mle_list(Q_k, c_i)?;
        }
        Ok(Q)
    }
}

impl<C: Curve> Dummy<&CCS<CF1<C>>> for CCCS<C> {
    fn dummy(ccs: &CCS<CF1<C>>) -> Self {
        Self {
            C: C::zero(),
            x: vec![CF1::<C>::zero(); ccs.n_public_inputs()],
        }
    }
}

impl<C: Curve> ArithRelation<Witness<CF1<C>>, CCCS<C>> for CCS<CF1<C>> {
    type Evaluation = Vec<CF1<C>>;

    fn eval_relation(&self, w: &Witness<CF1<C>>, u: &CCCS<C>) -> Result<Self::Evaluation, Error> {
        // evaluate CCCS relation
        self.eval_at_z(&[&[CF1::<C>::one()][..], &u.x, &w.w].concat())
    }

    /// Perform the check of the CCCS instance described at section 4.1,
    /// notice that this method does not check the commitment correctness
    fn check_evaluation(
        _w: &Witness<CF1<C>>,
        _u: &CCCS<C>,
        e: Self::Evaluation,
    ) -> Result<(), Error> {
        // A CCCS relation is satisfied if the q(x) multivariate polynomial evaluates to zero in
        // the hypercube, evaluating over the whole boolean hypercube for a normal-sized instance
        // would take too much, this checks the CCS relation of the CCCS.
        is_zero_vec(&e).then_some(()).ok_or(Error::NotSatisfied)
    }
}

impl<C: Curve> Absorb for CCCS<C> {
    fn to_sponge_bytes(&self, dest: &mut Vec<u8>) {
        C::ScalarField::batch_to_sponge_bytes(&self.to_sponge_field_elements_as_vec(), dest);
    }

    fn to_sponge_field_elements<F: PrimeField>(&self, dest: &mut Vec<F>) {
        self.C.to_native_sponge_field_elements(dest);
        self.x.to_sponge_field_elements(dest);
    }
}

impl<C: Curve> CommittedInstanceOps<C> for CCCS<C> {
    type Var = CCCSVar<C>;

    fn get_commitments(&self) -> Vec<C> {
        vec![self.C]
    }

    fn is_incoming(&self) -> bool {
        true
    }
}

impl<C: Curve> Inputize<CF1<C>> for CCCS<C> {
    /// Returns the internal representation in the same order as how the value
    /// is allocated in `CCCSVar::new_input`.
    fn inputize(&self) -> Vec<CF1<C>> {
        [&self.C.inputize_nonnative()[..], &self.x].concat()
    }
}

#[cfg(test)]
pub mod tests {
    use ark_pallas::Fr;
    use ark_std::test_rng;
    use ark_std::UniformRand;

    use super::*;
    use crate::arith::ccs::tests::{get_test_ccs, get_test_z};
    use crate::utils::hypercube::BooleanHypercube;

    /// Do some sanity checks on q(x). It's a multivariable polynomial and it should evaluate to zero inside the
    /// hypercube, but to not-zero outside the hypercube.
    #[test]
    fn test_compute_q() -> Result<(), Error> {
        let mut rng = test_rng();

        let ccs = get_test_ccs::<Fr>();
        let z = get_test_z(3);

        let q = ccs.compute_q(&z)?;

        // Evaluate inside the hypercube
        for x in BooleanHypercube::new(ccs.s) {
            assert_eq!(Fr::zero(), q.evaluate(&x)?);
        }

        // Evaluate outside the hypercube
        let beta: Vec<Fr> = (0..ccs.s).map(|_| Fr::rand(&mut rng)).collect();
        assert_ne!(Fr::zero(), q.evaluate(&beta)?);
        Ok(())
    }

    /// Perform some sanity checks on Q(x).
    #[test]
    fn test_compute_Q() -> Result<(), Error> {
        let mut rng = test_rng();

        let ccs: CCS<Fr> = get_test_ccs();
        let z = get_test_z(3);
        let (w, x) = ccs.split_z(&z);
        ccs.check_relation(&w, &x)?;

        let beta: Vec<Fr> = (0..ccs.s).map(|_| Fr::rand(&mut rng)).collect();

        // Compute Q(x) = eq(beta, x) * q(x).
        let Q = ccs.compute_Q(&z, &beta)?;

        // Let's consider the multilinear polynomial G(x) = \sum_{y \in {0, 1}^s} eq(x, y) q(y)
        // which interpolates the multivariate polynomial q(x) inside the hypercube.
        //
        // Observe that summing Q(x) inside the hypercube, directly computes G(\beta).
        //
        // Now, G(x) is multilinear and agrees with q(x) inside the hypercube. Since q(x) vanishes inside the
        // hypercube, this means that G(x) also vanishes in the hypercube. Since G(x) is multilinear and vanishes
        // inside the hypercube, this makes it the zero polynomial.
        //
        // Hence, evaluating G(x) at a random beta should give zero.

        // Now sum Q(x) evaluations in the hypercube and expect it to be 0
        let r = BooleanHypercube::new(ccs.s)
            .map(|x| Q.evaluate(&x))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .fold(Fr::zero(), |acc, result| acc + result);
        assert_eq!(r, Fr::zero());
        Ok(())
    }

    /// The polynomial G(x) (see above) interpolates q(x) inside the hypercube.
    /// Summing Q(x) over the hypercube is equivalent to evaluating G(x) at some point.
    /// This test makes sure that G(x) agrees with q(x) inside the hypercube, but not outside
    #[test]
    fn test_Q_against_q() -> Result<(), Error> {
        let mut rng = test_rng();

        let ccs: CCS<Fr> = get_test_ccs();
        let z = get_test_z(3);
        let (w, x) = ccs.split_z(&z);
        ccs.check_relation(&w, &x)?;

        // Now test that if we create Q(x) with eq(d,y) where d is inside the hypercube, \sum Q(x) should be G(d) which
        // should be equal to q(d), since G(x) interpolates q(x) inside the hypercube
        let q = ccs.compute_q(&z)?;
        for d in BooleanHypercube::new(ccs.s) {
            let Q_at_d = ccs.compute_Q(&z, &d)?;

            // Get G(d) by summing over Q_d(x) over the hypercube
            let G_at_d = BooleanHypercube::new(ccs.s)
                .map(|x| Q_at_d.evaluate(&x))
                .collect::<Result<Vec<_>, _>>()?
                .into_iter()
                .fold(Fr::zero(), |acc, result| acc + result);
            assert_eq!(G_at_d, q.evaluate(&d)?);
        }

        // Now test that they should disagree outside of the hypercube
        let r: Vec<Fr> = (0..ccs.s).map(|_| Fr::rand(&mut rng)).collect();
        let Q_at_r = ccs.compute_Q(&z, &r)?;

        // Get G(d) by summing over Q_d(x) over the hypercube
        let G_at_r = BooleanHypercube::new(ccs.s)
            .map(|x| Q_at_r.evaluate(&x))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .fold(Fr::zero(), |acc, result| acc + result);

        assert_ne!(G_at_r, q.evaluate(&r)?);
        Ok(())
    }
}
