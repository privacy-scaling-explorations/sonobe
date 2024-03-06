use ark_ec::CurveGroup;
use ark_poly::DenseMultilinearExtension;
use ark_std::One;
use std::sync::Arc;

use ark_std::{rand::Rng, UniformRand};

use super::cccs::Witness;
use super::utils::{compute_all_sum_Mz_evals, compute_sum_Mz};
use crate::ccs::CCS;
use crate::commitment::{
    pedersen::{Params as PedersenParams, Pedersen},
    CommitmentProver,
};
use crate::utils::mle::{matrix_to_mle, vec_to_mle};
use crate::utils::virtual_polynomial::VirtualPolynomial;
use crate::Error;

/// Linearized Committed CCS instance
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct LCCCS<C: CurveGroup> {
    // Commitment to witness
    pub C: C,
    // Relaxation factor of z for folded LCCCS
    pub u: C::ScalarField,
    // Public input/output
    pub x: Vec<C::ScalarField>,
    // Random evaluation point for the v_i
    pub r_x: Vec<C::ScalarField>,
    // Vector of v_i
    pub v: Vec<C::ScalarField>,
}

impl<C: CurveGroup> CCS<C> {
    /// Compute v_j values of the linearized committed CCS form
    /// Given `r`, compute:  \sum_{y \in {0,1}^s'} M_j(r, y) * z(y)
    fn compute_v_j(&self, z: &[C::ScalarField], r: &[C::ScalarField]) -> Vec<C::ScalarField> {
        compute_all_sum_Mz_evals(&self.M, &z.to_vec(), r, self.s_prime)
    }

    pub fn to_lcccs<R: Rng>(
        &self,
        rng: &mut R,
        pedersen_params: &PedersenParams<C>,
        z: &[C::ScalarField],
    ) -> Result<(LCCCS<C>, Witness<C::ScalarField>), Error> {
        let w: Vec<C::ScalarField> = z[(1 + self.l)..].to_vec();
        let r_w = C::ScalarField::rand(rng);
        let C = Pedersen::<C>::commit(pedersen_params, &w, &r_w)?;

        let r_x: Vec<C::ScalarField> = (0..self.s).map(|_| C::ScalarField::rand(rng)).collect();
        let v = self.compute_v_j(z, &r_x);

        Ok((
            LCCCS::<C> {
                C,
                u: C::ScalarField::one(),
                x: z[1..(1 + self.l)].to_vec(),
                r_x,
                v,
            },
            Witness::<C::ScalarField> { w, r_w },
        ))
    }
}

impl<C: CurveGroup> LCCCS<C> {
    /// Compute all L_j(x) polynomials
    pub fn compute_Ls(
        &self,
        ccs: &CCS<C>,
        z: &Vec<C::ScalarField>,
    ) -> Vec<VirtualPolynomial<C::ScalarField>> {
        let z_mle = vec_to_mle(ccs.s_prime, z);
        // Convert all matrices to MLE
        let M_x_y_mle: Vec<DenseMultilinearExtension<C::ScalarField>> =
            ccs.M.clone().into_iter().map(matrix_to_mle).collect();

        let mut vec_L_j_x = Vec::with_capacity(ccs.t);
        for M_j in M_x_y_mle {
            let sum_Mz = compute_sum_Mz(M_j, &z_mle, ccs.s_prime);
            let sum_Mz_virtual =
                VirtualPolynomial::new_from_mle(&Arc::new(sum_Mz.clone()), C::ScalarField::one());
            let L_j_x = sum_Mz_virtual.build_f_hat(&self.r_x).unwrap();
            vec_L_j_x.push(L_j_x);
        }

        vec_L_j_x
    }

    /// Perform the check of the LCCCS instance described at section 4.2
    pub fn check_relation(
        &self,
        pedersen_params: &PedersenParams<C>,
        ccs: &CCS<C>,
        w: &Witness<C::ScalarField>,
    ) -> Result<(), Error> {
        // check that C is the commitment of w. Notice that this is not verifying a Pedersen
        // opening, but checking that the Commitment comes from committing to the witness.
        if self.C != Pedersen::<C>::commit(pedersen_params, &w.w, &w.r_w)? {
            return Err(Error::NotSatisfied);
        }

        // check CCS relation
        let z: Vec<C::ScalarField> = [vec![self.u], self.x.clone(), w.w.to_vec()].concat();
        let computed_v = compute_all_sum_Mz_evals(&ccs.M, &z, &self.r_x, ccs.s_prime);
        if computed_v != self.v {
            return Err(Error::NotSatisfied);
        }
        Ok(())
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use ark_std::Zero;

    use crate::ccs::tests::{get_test_ccs, get_test_z};
    use crate::utils::hypercube::BooleanHypercube;
    use ark_std::test_rng;

    use ark_pallas::{Fr, Projective};

    #[test]
    /// Test linearized CCCS v_j against the L_j(x)
    fn test_lcccs_v_j() {
        let mut rng = test_rng();

        let ccs = get_test_ccs();
        let z = get_test_z(3);
        ccs.check_relation(&z.clone()).unwrap();

        let pedersen_params = Pedersen::<Projective>::new_params(&mut rng, ccs.n - ccs.l - 1);
        let (lcccs, _) = ccs.to_lcccs(&mut rng, &pedersen_params, &z).unwrap();
        // with our test vector coming from R1CS, v should have length 3
        assert_eq!(lcccs.v.len(), 3);

        let vec_L_j_x = lcccs.compute_Ls(&ccs, &z);
        assert_eq!(vec_L_j_x.len(), lcccs.v.len());

        for (v_i, L_j_x) in lcccs.v.into_iter().zip(vec_L_j_x) {
            let sum_L_j_x = BooleanHypercube::new(ccs.s)
                .map(|y| L_j_x.evaluate(&y).unwrap())
                .fold(Fr::zero(), |acc, result| acc + result);
            assert_eq!(v_i, sum_L_j_x);
        }
    }

    /// Given a bad z, check that the v_j should not match with the L_j(x)
    #[test]
    fn test_bad_v_j() {
        let mut rng = test_rng();

        let ccs = get_test_ccs();
        let z = get_test_z(3);
        ccs.check_relation(&z.clone()).unwrap();

        // Mutate z so that the relation does not hold
        let mut bad_z = z.clone();
        bad_z[3] = Fr::zero();
        assert!(ccs.check_relation(&bad_z.clone()).is_err());

        let pedersen_params = Pedersen::<Projective>::new_params(&mut rng, ccs.n - ccs.l - 1);
        // Compute v_j with the right z
        let (lcccs, _) = ccs.to_lcccs(&mut rng, &pedersen_params, &z).unwrap();
        // with our test vector coming from R1CS, v should have length 3
        assert_eq!(lcccs.v.len(), 3);

        // Bad compute L_j(x) with the bad z
        let vec_L_j_x = lcccs.compute_Ls(&ccs, &bad_z);
        assert_eq!(vec_L_j_x.len(), lcccs.v.len());

        // Make sure that the LCCCS is not satisfied given these L_j(x)
        // i.e. summing L_j(x) over the hypercube should not give v_j for all j
        let mut satisfied = true;
        for (v_i, L_j_x) in lcccs.v.into_iter().zip(vec_L_j_x) {
            let sum_L_j_x = BooleanHypercube::new(ccs.s)
                .map(|y| L_j_x.evaluate(&y).unwrap())
                .fold(Fr::zero(), |acc, result| acc + result);
            if v_i != sum_L_j_x {
                satisfied = false;
            }
        }

        assert!(!satisfied);
    }
}
