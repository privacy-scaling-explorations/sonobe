use ark_crypto_primitives::sponge::Absorb;
use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use ark_poly::DenseMultilinearExtension;
use ark_poly::MultilinearExtension;
use ark_serialize::CanonicalDeserialize;
use ark_serialize::CanonicalSerialize;
use ark_std::rand::Rng;
use ark_std::Zero;

use super::circuits::LCCCSVar;
use super::Witness;
use crate::arith::ccs::CCS;
use crate::arith::Arith;
use crate::commitment::CommitmentScheme;
use crate::folding::circuits::CF1;
use crate::folding::traits::{CommittedInstanceOps, Dummy};
use crate::transcript::AbsorbNonNative;
use crate::utils::mle::dense_vec_to_dense_mle;
use crate::utils::vec::mat_vec_mul;
use crate::Error;

/// Linearized Committed CCS instance
#[derive(Debug, Clone, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
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

impl<F: PrimeField> CCS<F> {
    pub fn to_lcccs<R: Rng, C, CS: CommitmentScheme<C, H>, const H: bool>(
        &self,
        rng: &mut R,
        cs_params: &CS::ProverParams,
        z: &[C::ScalarField],
    ) -> Result<(LCCCS<C>, Witness<C::ScalarField>), Error>
    where
        // enforce that CCS's F is the C::ScalarField
        C: CurveGroup<ScalarField = F>,
    {
        let w: Vec<C::ScalarField> = z[(1 + self.l)..].to_vec();
        // if the commitment scheme is set to be hiding, set the random blinding parameter
        let r_w = if CS::is_hiding() {
            C::ScalarField::rand(rng)
        } else {
            C::ScalarField::zero()
        };
        let C = CS::commit(cs_params, &w, &r_w)?;

        let r_x: Vec<C::ScalarField> = (0..self.s).map(|_| C::ScalarField::rand(rng)).collect();

        let Mzs: Vec<DenseMultilinearExtension<F>> = self
            .M
            .iter()
            .map(|M_j| Ok(dense_vec_to_dense_mle(self.s, &mat_vec_mul(M_j, z)?)))
            .collect::<Result<_, Error>>()?;

        // compute v_j
        let v: Vec<F> = Mzs
            .iter()
            .map(|Mz| Mz.evaluate(&r_x).ok_or(Error::EvaluationFail))
            .collect::<Result<_, Error>>()?;

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

impl<C: CurveGroup> Dummy<&CCS<CF1<C>>> for LCCCS<C> {
    fn dummy(ccs: &CCS<CF1<C>>) -> Self {
        Self {
            C: C::zero(),
            u: CF1::<C>::zero(),
            x: vec![CF1::<C>::zero(); ccs.l],
            r_x: vec![CF1::<C>::zero(); ccs.s],
            v: vec![CF1::<C>::zero(); ccs.t],
        }
    }
}

impl<C: CurveGroup> Arith<Witness<CF1<C>>, LCCCS<C>> for CCS<CF1<C>> {
    type Evaluation = Vec<CF1<C>>;

    /// Perform the check of the LCCCS instance described at section 4.2,
    /// notice that this method does not check the commitment correctness
    fn eval_relation(&self, w: &Witness<CF1<C>>, u: &LCCCS<C>) -> Result<Self::Evaluation, Error> {
        let z = [&[u.u][..], &u.x, &w.w].concat();

        self.M
            .iter()
            .map(|M_j| {
                let Mz_mle = dense_vec_to_dense_mle(self.s, &mat_vec_mul(M_j, &z)?);
                Mz_mle.evaluate(&u.r_x).ok_or(Error::EvaluationFail)
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

impl<C: CurveGroup> Absorb for LCCCS<C>
where
    C::ScalarField: Absorb,
{
    fn to_sponge_bytes(&self, dest: &mut Vec<u8>) {
        C::ScalarField::batch_to_sponge_bytes(&self.to_sponge_field_elements_as_vec(), dest);
    }

    fn to_sponge_field_elements<F: PrimeField>(&self, dest: &mut Vec<F>) {
        // We cannot call `to_native_sponge_field_elements(dest)` directly, as
        // `to_native_sponge_field_elements` needs `F` to be `C::ScalarField`,
        // but here `F` is a generic `PrimeField`.
        self.C
            .to_native_sponge_field_elements_as_vec()
            .to_sponge_field_elements(dest);
        self.u.to_sponge_field_elements(dest);
        self.x.to_sponge_field_elements(dest);
        self.r_x.to_sponge_field_elements(dest);
        self.v.to_sponge_field_elements(dest);
    }
}

impl<C: CurveGroup> CommittedInstanceOps<C> for LCCCS<C> {
    type Var = LCCCSVar<C>;

    fn get_commitments(&self) -> Vec<C> {
        vec![self.C]
    }

    fn is_incoming(&self) -> bool {
        false
    }
}

#[cfg(test)]
pub mod tests {
    use ark_pallas::{Fr, Projective};
    use ark_std::test_rng;
    use ark_std::One;
    use ark_std::UniformRand;
    use std::sync::Arc;

    use super::*;
    use crate::arith::{
        ccs::tests::{get_test_ccs, get_test_z},
        r1cs::R1CS,
        Arith,
    };
    use crate::commitment::pedersen::Pedersen;
    use crate::utils::hypercube::BooleanHypercube;
    use crate::utils::virtual_polynomial::{build_eq_x_r_vec, VirtualPolynomial};

    // method for testing
    pub fn compute_Ls<C: CurveGroup>(
        ccs: &CCS<C::ScalarField>,
        lcccs: &LCCCS<C>,
        z: &[C::ScalarField],
    ) -> Vec<VirtualPolynomial<C::ScalarField>> {
        let eq_rx = build_eq_x_r_vec(&lcccs.r_x).unwrap();
        let eq_rx_mle = dense_vec_to_dense_mle(ccs.s, &eq_rx);

        let mut Ls = Vec::with_capacity(ccs.t);
        for M_j in ccs.M.iter() {
            let mut L = VirtualPolynomial::<C::ScalarField>::new(ccs.s);
            let mut Mz = vec![dense_vec_to_dense_mle(ccs.s, &mat_vec_mul(M_j, z).unwrap())];
            Mz.push(eq_rx_mle.clone());
            L.add_mle_list(
                Mz.iter().map(|v| Arc::new(v.clone())),
                C::ScalarField::one(),
            )
            .unwrap();
            Ls.push(L);
        }
        Ls
    }

    #[test]
    /// Test linearized CCCS v_j against the L_j(x)
    fn test_lcccs_v_j() {
        let mut rng = test_rng();

        let n_rows = 2_u32.pow(5) as usize;
        let n_cols = 2_u32.pow(5) as usize;
        let r1cs = R1CS::<Fr>::rand(&mut rng, n_rows, n_cols);
        let ccs = CCS::from(r1cs);
        let z: Vec<Fr> = (0..n_cols).map(|_| Fr::rand(&mut rng)).collect();

        let (pedersen_params, _) =
            Pedersen::<Projective>::setup(&mut rng, ccs.n - ccs.l - 1).unwrap();

        let (lcccs, _) = ccs
            .to_lcccs::<_, Projective, Pedersen<Projective, false>, false>(
                &mut rng,
                &pedersen_params,
                &z,
            )
            .unwrap();
        // with our test vector coming from R1CS, v should have length 3
        assert_eq!(lcccs.v.len(), 3);

        let vec_L_j_x = compute_Ls(&ccs, &lcccs, &z);
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
        let (w, x) = ccs.split_z(&z);
        ccs.check_relation(&w, &x).unwrap();

        // Mutate z so that the relation does not hold
        let mut bad_z = z.clone();
        bad_z[3] = Fr::zero();
        let (bad_w, bad_x) = ccs.split_z(&bad_z);
        assert!(ccs.check_relation(&bad_w, &bad_x).is_err());

        let (pedersen_params, _) =
            Pedersen::<Projective>::setup(&mut rng, ccs.n - ccs.l - 1).unwrap();
        // Compute v_j with the right z
        let (lcccs, _) = ccs
            .to_lcccs::<_, Projective, Pedersen<Projective>, false>(&mut rng, &pedersen_params, &z)
            .unwrap();
        // with our test vector coming from R1CS, v should have length 3
        assert_eq!(lcccs.v.len(), 3);

        // Bad compute L_j(x) with the bad z
        let vec_L_j_x = compute_Ls(&ccs, &lcccs, &bad_z);
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
