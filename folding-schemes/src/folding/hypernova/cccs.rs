use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use ark_std::One;
use ark_std::Zero;
use std::ops::Add;
use std::sync::Arc;

use ark_std::{rand::Rng, UniformRand};

use super::utils::compute_sum_Mz;
use crate::ccs::CCS;
use crate::commitment::{
    pedersen::{Params as PedersenParams, Pedersen},
    CommitmentScheme,
};
use crate::utils::hypercube::BooleanHypercube;
use crate::utils::mle::matrix_to_mle;
use crate::utils::mle::vec_to_mle;
use crate::utils::virtual_polynomial::VirtualPolynomial;
use crate::Error;

/// Witness for the LCCCS & CCCS, containing the w vector, and the r_w used as randomness in the Pedersen commitment.
#[derive(Debug, Clone)]
pub struct Witness<F: PrimeField> {
    pub w: Vec<F>,
    pub r_w: F, // randomness used in the Pedersen commitment of w
}

/// Committed CCS instance
#[derive(Debug, Clone)]
pub struct CCCS<C: CurveGroup> {
    // Commitment to witness
    pub C: C,
    // Public input/output
    pub x: Vec<C::ScalarField>,
}

impl<C: CurveGroup> CCS<C> {
    pub fn to_cccs<R: Rng>(
        &self,
        rng: &mut R,
        pedersen_params: &PedersenParams<C>,
        z: &[C::ScalarField],
    ) -> Result<(CCCS<C>, Witness<C::ScalarField>), Error> {
        let w: Vec<C::ScalarField> = z[(1 + self.l)..].to_vec();
        let r_w = C::ScalarField::rand(rng);
        let C = Pedersen::<C, true>::commit(pedersen_params, &w, &r_w)?;

        Ok((
            CCCS::<C> {
                C,
                x: z[1..(1 + self.l)].to_vec(),
            },
            Witness::<C::ScalarField> { w, r_w },
        ))
    }

    /// Computes q(x) = \sum^q c_i * \prod_{j \in S_i} ( \sum_{y \in {0,1}^s'} M_j(x, y) * z(y) )
    /// polynomial over x
    pub fn compute_q(&self, z: &Vec<C::ScalarField>) -> VirtualPolynomial<C::ScalarField> {
        let z_mle = vec_to_mle(self.s_prime, z);
        let mut q = VirtualPolynomial::<C::ScalarField>::new(self.s);

        for i in 0..self.q {
            let mut prod: VirtualPolynomial<C::ScalarField> =
                VirtualPolynomial::<C::ScalarField>::new(self.s);
            for j in self.S[i].clone() {
                let M_j = matrix_to_mle(self.M[j].clone());

                let sum_Mz = compute_sum_Mz(M_j, &z_mle, self.s_prime);

                // Fold this sum into the running product
                if prod.products.is_empty() {
                    // If this is the first time we are adding something to this virtual polynomial, we need to
                    // explicitly add the products using add_mle_list()
                    // XXX is this true? improve API
                    prod.add_mle_list([Arc::new(sum_Mz)], C::ScalarField::one())
                        .unwrap();
                } else {
                    prod.mul_by_mle(Arc::new(sum_Mz), C::ScalarField::one())
                        .unwrap();
                }
            }
            // Multiply by the product by the coefficient c_i
            prod.scalar_mul(&self.c[i]);
            // Add it to the running sum
            q = q.add(&prod);
        }
        q
    }

    /// Computes Q(x) = eq(beta, x) * q(x)
    ///               = eq(beta, x) * \sum^q c_i * \prod_{j \in S_i} ( \sum_{y \in {0,1}^s'} M_j(x, y) * z(y) )
    /// polynomial over x
    pub fn compute_Q(
        &self,
        z: &Vec<C::ScalarField>,
        beta: &[C::ScalarField],
    ) -> VirtualPolynomial<C::ScalarField> {
        let q = self.compute_q(z);
        q.build_f_hat(beta).unwrap()
    }
}

impl<C: CurveGroup> CCCS<C> {
    /// Perform the check of the CCCS instance described at section 4.1
    pub fn check_relation(
        &self,
        pedersen_params: &PedersenParams<C>,
        ccs: &CCS<C>,
        w: &Witness<C::ScalarField>,
    ) -> Result<(), Error> {
        // check that C is the commitment of w. Notice that this is not verifying a Pedersen
        // opening, but checking that the commitment comes from committing to the witness.
        if self.C != Pedersen::<C, true>::commit(pedersen_params, &w.w, &w.r_w)? {
            return Err(Error::NotSatisfied);
        }

        // check CCCS relation
        let z: Vec<C::ScalarField> =
            [vec![C::ScalarField::one()], self.x.clone(), w.w.to_vec()].concat();

        // A CCCS relation is satisfied if the q(x) multivariate polynomial evaluates to zero in the hypercube
        let q_x = ccs.compute_q(&z);
        for x in BooleanHypercube::new(ccs.s) {
            if !q_x.evaluate(&x).unwrap().is_zero() {
                return Err(Error::NotSatisfied);
            }
        }

        Ok(())
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::ccs::tests::{get_test_ccs, get_test_z};
    use ark_std::test_rng;
    use ark_std::UniformRand;

    use ark_pallas::{Fr, Projective};

    /// Do some sanity checks on q(x). It's a multivariable polynomial and it should evaluate to zero inside the
    /// hypercube, but to not-zero outside the hypercube.
    #[test]
    fn test_compute_q() {
        let mut rng = test_rng();

        let ccs = get_test_ccs::<Projective>();
        let z = get_test_z(3);

        let q = ccs.compute_q(&z);

        // Evaluate inside the hypercube
        for x in BooleanHypercube::new(ccs.s) {
            assert_eq!(Fr::zero(), q.evaluate(&x).unwrap());
        }

        // Evaluate outside the hypercube
        let beta: Vec<Fr> = (0..ccs.s).map(|_| Fr::rand(&mut rng)).collect();
        assert_ne!(Fr::zero(), q.evaluate(&beta).unwrap());
    }

    /// Perform some sanity checks on Q(x).
    #[test]
    fn test_compute_Q() {
        let mut rng = test_rng();

        let ccs: CCS<Projective> = get_test_ccs();
        let z = get_test_z(3);
        ccs.check_relation(&z).unwrap();

        let beta: Vec<Fr> = (0..ccs.s).map(|_| Fr::rand(&mut rng)).collect();

        // Compute Q(x) = eq(beta, x) * q(x).
        let Q = ccs.compute_Q(&z, &beta);

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
            .map(|x| Q.evaluate(&x).unwrap())
            .fold(Fr::zero(), |acc, result| acc + result);
        assert_eq!(r, Fr::zero());
    }

    /// The polynomial G(x) (see above) interpolates q(x) inside the hypercube.
    /// Summing Q(x) over the hypercube is equivalent to evaluating G(x) at some point.
    /// This test makes sure that G(x) agrees with q(x) inside the hypercube, but not outside
    #[test]
    fn test_Q_against_q() {
        let mut rng = test_rng();

        let ccs: CCS<Projective> = get_test_ccs();
        let z = get_test_z(3);
        ccs.check_relation(&z).unwrap();

        // Now test that if we create Q(x) with eq(d,y) where d is inside the hypercube, \sum Q(x) should be G(d) which
        // should be equal to q(d), since G(x) interpolates q(x) inside the hypercube
        let q = ccs.compute_q(&z);
        for d in BooleanHypercube::new(ccs.s) {
            let Q_at_d = ccs.compute_Q(&z, &d);

            // Get G(d) by summing over Q_d(x) over the hypercube
            let G_at_d = BooleanHypercube::new(ccs.s)
                .map(|x| Q_at_d.evaluate(&x).unwrap())
                .fold(Fr::zero(), |acc, result| acc + result);
            assert_eq!(G_at_d, q.evaluate(&d).unwrap());
        }

        // Now test that they should disagree outside of the hypercube
        let r: Vec<Fr> = (0..ccs.s).map(|_| Fr::rand(&mut rng)).collect();
        let Q_at_r = ccs.compute_Q(&z, &r);

        // Get G(d) by summing over Q_d(x) over the hypercube
        let G_at_r = BooleanHypercube::new(ccs.s)
            .map(|x| Q_at_r.evaluate(&x).unwrap())
            .fold(Fr::zero(), |acc, result| acc + result);
        assert_ne!(G_at_r, q.evaluate(&r).unwrap());
    }
}
