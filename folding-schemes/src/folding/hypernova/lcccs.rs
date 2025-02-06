use ark_crypto_primitives::sponge::Absorb;
use ark_ff::PrimeField;
use ark_poly::Polynomial;
use ark_serialize::CanonicalDeserialize;
use ark_serialize::CanonicalSerialize;
use ark_std::rand::Rng;
use ark_std::Zero;

use super::circuits::LCCCSVar;
use super::Witness;
use crate::arith::ccs::CCS;
use crate::arith::{Arith, ArithRelation};
use crate::commitment::CommitmentScheme;
use crate::folding::circuits::CF1;
use crate::folding::traits::Inputize;
use crate::folding::traits::{CommittedInstanceOps, Dummy};
use crate::utils::mle::dense_vec_to_dense_mle;
use crate::utils::vec::mat_vec_mul;
use crate::{Curve, Error};

/// Linearized Committed CCS instance
#[derive(Debug, Clone, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct LCCCS<C: Curve> {
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

impl<F: PrimeField> CCS<F> {
    pub fn to_lcccs<R: Rng, C, CS: CommitmentScheme<C, H>, const H: bool>(
        &self,
        rng: &mut R,
        cs_params: &CS::ProverParams,
        z: &[F],
    ) -> Result<(LCCCS<C>, Witness<F>), Error>
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

        let r_x: Vec<F> = (0..self.s).map(|_| F::rand(rng)).collect();

        // compute v_j
        let v = self
            .M
            .iter()
            .map(|M_j| {
                let Mz = dense_vec_to_dense_mle(self.s, &mat_vec_mul(M_j, z)?);
                Ok(Mz.evaluate(&r_x))
            })
            .collect::<Result<_, Error>>()?;

        Ok((
            LCCCS::<C> {
                C,
                u: z[0],
                x,
                r_x,
                v,
            },
            Witness::<F> { w, r_w },
        ))
    }
}

impl<C: Curve> Dummy<&CCS<CF1<C>>> for LCCCS<C> {
    fn dummy(ccs: &CCS<CF1<C>>) -> Self {
        Self {
            C: C::zero(),
            u: CF1::<C>::zero(),
            x: vec![CF1::<C>::zero(); ccs.n_public_inputs()],
            r_x: vec![CF1::<C>::zero(); ccs.s],
            v: vec![CF1::<C>::zero(); ccs.t],
        }
    }
}

impl<C: Curve> ArithRelation<Witness<CF1<C>>, LCCCS<C>> for CCS<CF1<C>> {
    type Evaluation = Vec<CF1<C>>;

    /// Perform the check of the LCCCS instance described at section 4.2,
    /// notice that this method does not check the commitment correctness
    fn eval_relation(&self, w: &Witness<CF1<C>>, u: &LCCCS<C>) -> Result<Self::Evaluation, Error> {
        let z = [&[u.u][..], &u.x, &w.w].concat();

        self.M
            .iter()
            .map(|M_j| {
                let Mz_mle = dense_vec_to_dense_mle(self.s, &mat_vec_mul(M_j, &z)?);
                Ok(Mz_mle.evaluate(&u.r_x))
            })
            .collect()
    }

    fn check_evaluation(
        _w: &Witness<CF1<C>>,
        u: &LCCCS<C>,
        e: Self::Evaluation,
    ) -> Result<(), Error> {
        (u.v == e).then_some(()).ok_or(Error::NotSatisfied)
    }
}

impl<C: Curve> Absorb for LCCCS<C> {
    fn to_sponge_bytes(&self, dest: &mut Vec<u8>) {
        C::ScalarField::batch_to_sponge_bytes(&self.to_sponge_field_elements_as_vec(), dest);
    }

    fn to_sponge_field_elements<F: PrimeField>(&self, dest: &mut Vec<F>) {
        self.C.to_native_sponge_field_elements(dest);
        self.u.to_sponge_field_elements(dest);
        self.x.to_sponge_field_elements(dest);
        self.r_x.to_sponge_field_elements(dest);
        self.v.to_sponge_field_elements(dest);
    }
}

impl<C: Curve> CommittedInstanceOps<C> for LCCCS<C> {
    type Var = LCCCSVar<C>;

    fn get_commitments(&self) -> Vec<C> {
        vec![self.C]
    }

    fn is_incoming(&self) -> bool {
        false
    }
}

impl<C: Curve> Inputize<CF1<C>> for LCCCS<C> {
    /// Returns the internal representation in the same order as how the value
    /// is allocated in `LCCCS::new_input`.
    fn inputize(&self) -> Vec<CF1<C>> {
        [
            &self.C.inputize_nonnative(),
            &[self.u][..],
            &self.x,
            &self.r_x,
            &self.v,
        ]
        .concat()
    }
}

#[cfg(test)]
pub mod tests {
    use ark_pallas::{Fr, Projective};
    use ark_std::{sync::Arc, test_rng, One, UniformRand};

    use super::*;
    use crate::arith::{
        ccs::tests::{get_test_ccs, get_test_z},
        r1cs::R1CS,
        ArithRelation,
    };
    use crate::commitment::pedersen::Pedersen;
    use crate::utils::hypercube::BooleanHypercube;
    use crate::utils::virtual_polynomial::{build_eq_x_r_vec, VirtualPolynomial};

    // method for testing
    pub fn compute_Ls<C: Curve>(
        ccs: &CCS<C::ScalarField>,
        lcccs: &LCCCS<C>,
        z: &[C::ScalarField],
    ) -> Result<Vec<VirtualPolynomial<C::ScalarField>>, Error> {
        let eq_rx = build_eq_x_r_vec(&lcccs.r_x)?;
        let eq_rx_mle = Arc::new(dense_vec_to_dense_mle(ccs.s, &eq_rx));

        let Ls = ccs
            .M
            .iter()
            .map(|M_j| {
                let mut L = VirtualPolynomial::<C::ScalarField>::new(ccs.s);
                let Mz = vec![
                    Arc::new(dense_vec_to_dense_mle(ccs.s, &mat_vec_mul(M_j, z)?)),
                    eq_rx_mle.clone(),
                ];
                L.add_mle_list(Mz, C::ScalarField::one())?;
                Ok(L)
            })
            .collect::<Result<Vec<_>, Error>>()?;
        Ok(Ls)
    }

    #[test]
    /// Test linearized CCCS v_j against the L_j(x)
    fn test_lcccs_v_j() -> Result<(), Error> {
        let mut rng = test_rng();

        let n_rows = 2_u32.pow(5) as usize;
        let n_cols = 2_u32.pow(5) as usize;
        let r1cs = R1CS::<Fr>::rand(&mut rng, n_rows, n_cols);
        let ccs = CCS::from(r1cs);
        let z: Vec<Fr> = (0..n_cols).map(|_| Fr::rand(&mut rng)).collect();

        let (pedersen_params, _) = Pedersen::<Projective>::setup(&mut rng, ccs.n_witnesses())?;

        let (lcccs, _) = ccs.to_lcccs::<_, Projective, Pedersen<Projective, false>, false>(
            &mut rng,
            &pedersen_params,
            &z,
        )?;
        // with our test vector coming from R1CS, v should have length 3
        assert_eq!(lcccs.v.len(), 3);

        let vec_L_j_x = compute_Ls(&ccs, &lcccs, &z)?;
        assert_eq!(vec_L_j_x.len(), lcccs.v.len());

        for (v_i, L_j_x) in lcccs.v.into_iter().zip(vec_L_j_x) {
            let sum_L_j_x = BooleanHypercube::new(ccs.s)
                .map(|y| L_j_x.evaluate(&y))
                .collect::<Result<Vec<_>, _>>()?
                .into_iter()
                .fold(Fr::zero(), |acc, result| acc + result);
            assert_eq!(v_i, sum_L_j_x);
        }
        Ok(())
    }

    /// Given a bad z, check that the v_j should not match with the L_j(x)
    #[test]
    fn test_bad_v_j() -> Result<(), Error> {
        let mut rng = test_rng();

        let ccs = get_test_ccs();
        let z = get_test_z(3);
        let (w, x) = ccs.split_z(&z);
        ccs.check_relation(&w, &x)?;

        // Mutate z so that the relation does not hold
        let mut bad_z = z.clone();
        bad_z[3] = Fr::zero();
        let (bad_w, bad_x) = ccs.split_z(&bad_z);
        assert!(ccs.check_relation(&bad_w, &bad_x).is_err());

        let (pedersen_params, _) = Pedersen::<Projective>::setup(&mut rng, ccs.n_witnesses())?;
        // Compute v_j with the right z
        let (lcccs, _) = ccs.to_lcccs::<_, Projective, Pedersen<Projective>, false>(
            &mut rng,
            &pedersen_params,
            &z,
        )?;
        // with our test vector coming from R1CS, v should have length 3
        assert_eq!(lcccs.v.len(), 3);

        // Bad compute L_j(x) with the bad z
        let vec_L_j_x = compute_Ls(&ccs, &lcccs, &bad_z)?;
        assert_eq!(vec_L_j_x.len(), lcccs.v.len());

        // Make sure that the LCCCS is not satisfied given these L_j(x)
        // i.e. summing L_j(x) over the hypercube should not give v_j for all j
        let mut satisfied = true;
        for (v_i, L_j_x) in lcccs.v.into_iter().zip(vec_L_j_x) {
            let sum_L_j_x = BooleanHypercube::new(ccs.s)
                .map(|y| L_j_x.evaluate(&y))
                .collect::<Result<Vec<_>, _>>()?
                .into_iter()
                .fold(Fr::zero(), |acc, result| acc + result);
            if v_i != sum_L_j_x {
                satisfied = false;
            }
        }
        assert!(!satisfied);
        Ok(())
    }
}
