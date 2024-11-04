/// This module contains the implementation the NIFSTrait for the
/// [Nova](https://eprint.iacr.org/2021/370.pdf) NIFS (Non-Interactive Folding Scheme).
use ark_crypto_primitives::sponge::Absorb;
use ark_ec::{CurveGroup, Group};
use ark_ff::{BigInteger, PrimeField};
use ark_std::rand::RngCore;
use ark_std::Zero;
use std::marker::PhantomData;

use super::NIFSTrait;
use crate::arith::r1cs::R1CS;
use crate::commitment::CommitmentScheme;
use crate::folding::circuits::cyclefold::{CycleFoldCommittedInstance, CycleFoldWitness};
use crate::folding::nova::circuits::ChallengeGadget;
use crate::folding::nova::{CommittedInstance, Witness};
use crate::transcript::Transcript;
use crate::utils::vec::{hadamard, mat_vec_mul, vec_add, vec_scalar_mul, vec_sub};
use crate::Error;

/// Implements the Non-Interactive Folding Scheme described in section 4 of
/// [Nova](https://eprint.iacr.org/2021/370.pdf).
/// `H` specifies whether the NIFS will use a blinding factor
pub struct NIFS<
    C: CurveGroup,
    CS: CommitmentScheme<C, H>,
    T: Transcript<C::ScalarField>,
    const H: bool = false,
> {
    _c: PhantomData<C>,
    _cp: PhantomData<CS>,
    _t: PhantomData<T>,
}

impl<C: CurveGroup, CS: CommitmentScheme<C, H>, T: Transcript<C::ScalarField>, const H: bool>
    NIFSTrait<C, CS, T, H> for NIFS<C, CS, T, H>
where
    <C as Group>::ScalarField: Absorb,
{
    type CommittedInstance = CommittedInstance<C>;
    type Witness = Witness<C>;
    type ProverAux = Vec<C::ScalarField>;
    type Proof = C;

    fn new_witness(w: Vec<C::ScalarField>, e_len: usize, rng: impl RngCore) -> Self::Witness {
        Witness::new::<H>(w, e_len, rng)
    }

    fn new_instance(
        _rng: impl RngCore,
        params: &CS::ProverParams,
        W: &Self::Witness,
        x: Vec<C::ScalarField>,
        _aux: Vec<C::ScalarField>,
    ) -> Result<Self::CommittedInstance, Error> {
        W.commit::<CS, H>(params, x)
    }

    fn fold_witness(
        r: C::ScalarField,
        W_i: &Self::Witness,
        w_i: &Self::Witness,
        aux: &Self::ProverAux, // T in Nova's notation
    ) -> Result<Self::Witness, Error> {
        let r2 = r * r;
        let E: Vec<C::ScalarField> = vec_add(
            &vec_add(&W_i.E, &vec_scalar_mul(aux, &r))?, // aux is Nova's T
            &vec_scalar_mul(&w_i.E, &r2),
        )?;
        // use r_T=0 since we don't need hiding property for cm(T)
        let rT = C::ScalarField::zero();
        let rE = W_i.rE + r * rT + r2 * w_i.rE;
        let W: Vec<C::ScalarField> = W_i
            .W
            .iter()
            .zip(&w_i.W)
            .map(|(a, b)| *a + (r * b))
            .collect();

        let rW = W_i.rW + r * w_i.rW;
        Ok(Self::Witness { E, rE, W, rW })
    }

    fn prove(
        cs_prover_params: &CS::ProverParams,
        r1cs: &R1CS<C::ScalarField>,
        transcript: &mut T,
        pp_hash: C::ScalarField,
        W_i: &Self::Witness,
        U_i: &Self::CommittedInstance,
        w_i: &Self::Witness,
        u_i: &Self::CommittedInstance,
    ) -> Result<
        (
            Self::Witness,
            Self::CommittedInstance,
            Self::Proof,
            Vec<bool>,
        ),
        Error,
    > {
        // compute the cross terms
        let z1: Vec<C::ScalarField> = [vec![U_i.u], U_i.x.to_vec(), W_i.W.to_vec()].concat();
        let z2: Vec<C::ScalarField> = [vec![u_i.u], u_i.x.to_vec(), w_i.W.to_vec()].concat();
        let T = Self::compute_T(r1cs, U_i.u, u_i.u, &z1, &z2)?;

        // use r_T=0 since we don't need hiding property for cm(T)
        let cmT = CS::commit(cs_prover_params, &T, &C::ScalarField::zero())?;

        let r_bits = ChallengeGadget::<C, Self::CommittedInstance>::get_challenge_native(
            transcript,
            pp_hash,
            U_i,
            u_i,
            Some(&cmT),
        );
        let r_Fr = C::ScalarField::from_bigint(BigInteger::from_bits_le(&r_bits))
            .ok_or(Error::OutOfBounds)?;

        let w = Self::fold_witness(r_Fr, W_i, w_i, &T)?;

        let ci = Self::fold_committed_instances(r_Fr, U_i, u_i, &cmT);

        Ok((w, ci, cmT, r_bits))
    }

    fn verify(
        transcript: &mut T,
        pp_hash: C::ScalarField,
        U_i: &Self::CommittedInstance,
        u_i: &Self::CommittedInstance,
        cmT: &C, // Proof
    ) -> Result<(Self::CommittedInstance, Vec<bool>), Error> {
        let r_bits = ChallengeGadget::<C, Self::CommittedInstance>::get_challenge_native(
            transcript,
            pp_hash,
            U_i,
            u_i,
            Some(cmT),
        );
        let r = C::ScalarField::from_bigint(BigInteger::from_bits_le(&r_bits))
            .ok_or(Error::OutOfBounds)?;

        Ok((Self::fold_committed_instances(r, U_i, u_i, cmT), r_bits))
    }
}

impl<C: CurveGroup, CS: CommitmentScheme<C, H>, T: Transcript<C::ScalarField>, const H: bool>
    NIFS<C, CS, T, H>
where
    <C as Group>::ScalarField: Absorb,
{
    /// compute_T: compute cross-terms T
    pub fn compute_T(
        r1cs: &R1CS<C::ScalarField>,
        u1: C::ScalarField,
        u2: C::ScalarField,
        z1: &[C::ScalarField],
        z2: &[C::ScalarField],
    ) -> Result<Vec<C::ScalarField>, Error> {
        let (A, B, C) = (r1cs.A.clone(), r1cs.B.clone(), r1cs.C.clone());

        // this is parallelizable (for the future)
        let Az1 = mat_vec_mul(&A, z1)?;
        let Bz1 = mat_vec_mul(&B, z1)?;
        let Cz1 = mat_vec_mul(&C, z1)?;
        let Az2 = mat_vec_mul(&A, z2)?;
        let Bz2 = mat_vec_mul(&B, z2)?;
        let Cz2 = mat_vec_mul(&C, z2)?;

        let Az1_Bz2 = hadamard(&Az1, &Bz2)?;
        let Az2_Bz1 = hadamard(&Az2, &Bz1)?;
        let u1Cz2 = vec_scalar_mul(&Cz2, &u1);
        let u2Cz1 = vec_scalar_mul(&Cz1, &u2);

        vec_sub(&vec_sub(&vec_add(&Az1_Bz2, &Az2_Bz1)?, &u1Cz2)?, &u2Cz1)
    }

    pub fn compute_cyclefold_cmT(
        cs_prover_params: &CS::ProverParams,
        r1cs: &R1CS<C::ScalarField>, // R1CS over C2.Fr=C1.Fq (here C=C2)
        w1: &CycleFoldWitness<C>,
        ci1: &CycleFoldCommittedInstance<C>,
        w2: &CycleFoldWitness<C>,
        ci2: &CycleFoldCommittedInstance<C>,
    ) -> Result<(Vec<C::ScalarField>, C), Error>
    where
        <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
    {
        let z1: Vec<C::ScalarField> = [vec![ci1.u], ci1.x.to_vec(), w1.W.to_vec()].concat();
        let z2: Vec<C::ScalarField> = [vec![ci2.u], ci2.x.to_vec(), w2.W.to_vec()].concat();

        // compute cross terms
        let T = Self::compute_T(r1cs, ci1.u, ci2.u, &z1, &z2)?;
        // use r_T=0 since we don't need hiding property for cm(T)
        let cmT = CS::commit(cs_prover_params, &T, &C::ScalarField::zero())?;
        Ok((T, cmT))
    }

    /// folds two committed instances with the given r and cmT. This method is used by
    /// Nova::verify, but also by Nova::prove and the CycleFoldNIFS::verify.
    pub fn fold_committed_instances(
        r: C::ScalarField,
        U_i: &CommittedInstance<C>,
        u_i: &CommittedInstance<C>,
        cmT: &C,
    ) -> CommittedInstance<C> {
        let r2 = r * r;
        let cmE = U_i.cmE + cmT.mul(r) + u_i.cmE.mul(r2);
        let u = U_i.u + r * u_i.u;
        let cmW = U_i.cmW + u_i.cmW.mul(r);
        let x = U_i
            .x
            .iter()
            .zip(&u_i.x)
            .map(|(a, b)| *a + (r * b))
            .collect::<Vec<C::ScalarField>>();

        CommittedInstance { cmE, u, cmW, x }
    }

    pub fn prove_commitments(
        tr: &mut impl Transcript<C::ScalarField>,
        cs_prover_params: &CS::ProverParams,
        w: &Witness<C>,
        ci: &CommittedInstance<C>,
        T: Vec<C::ScalarField>,
        cmT: &C,
    ) -> Result<[CS::Proof; 3], Error> {
        let cmE_proof = CS::prove(cs_prover_params, tr, &ci.cmE, &w.E, &w.rE, None)?;
        let cmW_proof = CS::prove(cs_prover_params, tr, &ci.cmW, &w.W, &w.rW, None)?;
        let cmT_proof = CS::prove(cs_prover_params, tr, cmT, &T, &C::ScalarField::zero(), None)?; // cm(T) is committed with rT=0
        Ok([cmE_proof, cmW_proof, cmT_proof])
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use ark_crypto_primitives::sponge::poseidon::PoseidonSponge;
    use ark_pallas::{Fr, Projective};

    use crate::arith::{r1cs::tests::get_test_r1cs, Arith};
    use crate::commitment::pedersen::Pedersen;
    use crate::folding::nova::nifs::tests::test_nifs_opt;

    #[test]
    fn test_nifs_nova() {
        let (W, U) = test_nifs_opt::<NIFS<Projective, Pedersen<Projective>, PoseidonSponge<Fr>>>();

        // check the last folded instance relation
        let r1cs = get_test_r1cs();
        r1cs.check_relation(&W, &U).unwrap();
    }
}
