use ark_crypto_primitives::sponge::Absorb;
use ark_ec::{CurveGroup, Group};
use ark_ff::PrimeField;
use ark_std::rand::RngCore;
use ark_std::Zero;
use std::marker::PhantomData;

use super::circuits::ChallengeGadget;
use super::traits::NIFSTrait;
use super::{CommittedInstance, Witness};
use crate::arith::r1cs::R1CS;
use crate::commitment::CommitmentScheme;
use crate::folding::circuits::cyclefold::{CycleFoldCommittedInstance, CycleFoldWitness};
use crate::transcript::Transcript;
use crate::utils::vec::{hadamard, mat_vec_mul, vec_add, vec_scalar_mul, vec_sub};
use crate::Error;

/// Implements the Non-Interactive Folding Scheme described in section 4 of
/// [Nova](https://eprint.iacr.org/2021/370.pdf)
/// `H` specifies whether the NIFS will use a blinding factor
pub struct NIFS<C: CurveGroup, CS: CommitmentScheme<C, H>, const H: bool = false> {
    _c: PhantomData<C>,
    _cp: PhantomData<CS>,
}

impl<C: CurveGroup, CS: CommitmentScheme<C, H>, const H: bool> NIFSTrait<C, CS, H>
    for NIFS<C, CS, H>
where
    <C as Group>::ScalarField: Absorb,
    <C as CurveGroup>::BaseField: PrimeField,
{
    type CommittedInstance = CommittedInstance<C>;
    type Witness = Witness<C>;
    type ProverAux = Vec<C::ScalarField>;
    type VerifierAux = C;

    fn new_witness(w: Vec<C::ScalarField>, e_len: usize, rng: impl RngCore) -> Self::Witness {
        Witness::new::<H>(w, e_len, rng)
    }

    fn new_instance(
        W: &Self::Witness,
        params: &CS::ProverParams,
        x: Vec<C::ScalarField>,
        _aux: Vec<C::ScalarField>,
    ) -> Result<Self::CommittedInstance, Error> {
        W.commit::<CS, H>(params, x)
    }

    fn fold_witness(
        r: C::ScalarField,
        W_i: &Self::Witness,
        w_i: &Self::Witness,
        aux: &Self::ProverAux,
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

    fn compute_aux(
        cs_prover_params: &CS::ProverParams,
        r1cs: &R1CS<C::ScalarField>,
        W_i: &Self::Witness,
        U_i: &Self::CommittedInstance,
        w_i: &Self::Witness,
        u_i: &Self::CommittedInstance,
    ) -> Result<(Self::ProverAux, Self::VerifierAux), Error> {
        let z1: Vec<C::ScalarField> = [vec![U_i.u], U_i.x.to_vec(), W_i.W.to_vec()].concat();
        let z2: Vec<C::ScalarField> = [vec![u_i.u], u_i.x.to_vec(), w_i.W.to_vec()].concat();

        // compute cross terms
        let T = Self::compute_T(r1cs, U_i.u, u_i.u, &z1, &z2)?;
        // use r_T=0 since we don't need hiding property for cm(T)
        let cmT = CS::commit(cs_prover_params, &T, &C::ScalarField::zero())?;
        Ok((T, cmT))
    }

    fn get_challenge<T: Transcript<C::ScalarField>>(
        transcript: &mut T,
        pp_hash: C::ScalarField, // public params hash
        U_i: &Self::CommittedInstance,
        u_i: &Self::CommittedInstance,
        aux: &Self::VerifierAux, // cmT
    ) -> Vec<bool> {
        ChallengeGadget::<C, Self::CommittedInstance>::get_challenge_native(
            transcript,
            pp_hash,
            U_i,
            u_i,
            Some(aux),
        )
    }

    // Notice: `prove` method is implemented at the trait level.

    fn verify(
        // r comes from the transcript, and is a n-bit (N_BITS_CHALLENGE) element
        r: C::ScalarField,
        U_i: &Self::CommittedInstance,
        u_i: &Self::CommittedInstance,
        cmT: &C, // VerifierAux
    ) -> Self::CommittedInstance {
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

        Self::CommittedInstance { cmE, u, cmW, x }
    }
}

impl<C: CurveGroup, CS: CommitmentScheme<C, H>, const H: bool> NIFS<C, CS, H>
where
    <C as Group>::ScalarField: Absorb,
    <C as CurveGroup>::BaseField: PrimeField,
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

    /// In Nova, NIFS.P is the consecutive combination of compute_cmT with fold_instances,
    /// ie. compute_cmT is part of the NIFS.P logic.
    pub fn compute_cmT(
        cs_prover_params: &CS::ProverParams,
        r1cs: &R1CS<C::ScalarField>,
        w1: &Witness<C>,
        ci1: &CommittedInstance<C>,
        w2: &Witness<C>,
        ci2: &CommittedInstance<C>,
    ) -> Result<(Vec<C::ScalarField>, C), Error> {
        let z1: Vec<C::ScalarField> = [vec![ci1.u], ci1.x.to_vec(), w1.W.to_vec()].concat();
        let z2: Vec<C::ScalarField> = [vec![ci2.u], ci2.x.to_vec(), w2.W.to_vec()].concat();

        // compute cross terms
        let T = Self::compute_T(r1cs, ci1.u, ci2.u, &z1, &z2)?;
        // use r_T=0 since we don't need hiding property for cm(T)
        let cmT = CS::commit(cs_prover_params, &T, &C::ScalarField::zero())?;
        Ok((T, cmT))
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

    /// Verify committed folded instance (ci) relations. Notice that this method does not open the
    /// commitments, but just checks that the given committed instances (ci1, ci2) when folded
    /// result in the folded committed instance (ci3) values.
    pub fn verify_folded_instance(
        r: C::ScalarField,
        ci1: &CommittedInstance<C>,
        ci2: &CommittedInstance<C>,
        ci3: &CommittedInstance<C>,
        cmT: &C,
    ) -> Result<(), Error> {
        let expected = Self::verify(r, ci1, ci2, cmT);
        if ci3.cmE != expected.cmE
            || ci3.u != expected.u
            || ci3.cmW != expected.cmW
            || ci3.x != expected.x
        {
            return Err(Error::NotSatisfied);
        }
        Ok(())
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
    use crate::transcript::poseidon::poseidon_canonical_config;
    use ark_crypto_primitives::sponge::{poseidon::PoseidonSponge, CryptographicSponge};
    use ark_ff::{BigInteger, PrimeField};
    use ark_pallas::{Fr, Projective};
    use ark_std::{test_rng, UniformRand};

    use crate::arith::{
        r1cs::tests::{get_test_r1cs, get_test_z},
        Arith,
    };
    use crate::commitment::pedersen::Pedersen;
    use crate::folding::nova::traits::NIFSTrait;

    #[test]
    fn test_nifs_nova() {
        let (W, U) = test_nifs_opt::<NIFS<Projective, Pedersen<Projective>>>();

        // check the last folded instance relation
        let r1cs = get_test_r1cs();
        r1cs.check_relation(&W, &U).unwrap();
    }

    /// runs a loop using the NIFS trait, and returns the last Witness and CommittedInstance so
    /// that their relation can be checked.
    pub(crate) fn test_nifs_opt<N: NIFSTrait<Projective, Pedersen<Projective>>>(
    ) -> (N::Witness, N::CommittedInstance) {
        let r1cs = get_test_r1cs();
        let z = get_test_z(3);
        let (w, x) = r1cs.split_z(&z);

        let mut rng = ark_std::test_rng();
        let (pedersen_params, _) = Pedersen::<Projective>::setup(&mut rng, r1cs.A.n_cols).unwrap();

        let poseidon_config = poseidon_canonical_config::<Fr>();
        let mut transcript = PoseidonSponge::<Fr>::new(&poseidon_config);
        let pp_hash = Fr::rand(&mut rng);

        // prepare the running instance
        let mut running_witness = N::new_witness(w.clone(), r1cs.A.n_rows, test_rng());
        let mut running_committed_instance =
            N::new_instance(&running_witness, &pedersen_params, x, vec![]).unwrap();

        let num_iters = 10;
        for i in 0..num_iters {
            // prepare the incoming instance
            let incoming_instance_z = get_test_z(i + 4);
            let (w, x) = r1cs.split_z(&incoming_instance_z);
            let incoming_witness = N::new_witness(w.clone(), r1cs.A.n_rows, test_rng());
            let incoming_committed_instance =
                N::new_instance(&incoming_witness, &pedersen_params, x, vec![]).unwrap();

            let (aux_p, aux_v) = N::compute_aux(
                &pedersen_params,
                &r1cs,
                &running_witness,
                &running_committed_instance,
                &incoming_witness,
                &incoming_committed_instance,
            )
            .unwrap();

            let r_bits = N::get_challenge(
                &mut transcript,
                pp_hash,
                &running_committed_instance,
                &incoming_committed_instance,
                &aux_v,
            );
            let r = Fr::from_bigint(BigInteger::from_bits_le(&r_bits)).unwrap();

            // NIFS.P
            let (folded_witness, _) = N::prove(
                r,
                &running_witness,
                &running_committed_instance,
                &incoming_witness,
                &incoming_committed_instance,
                &aux_p,
                &aux_v,
            )
            .unwrap();

            // NIFS.V
            let folded_committed_instance = N::verify(
                r,
                &running_committed_instance,
                &incoming_committed_instance,
                &aux_v,
            );

            // set running_instance for next loop iteration
            running_witness = folded_witness;
            running_committed_instance = folded_committed_instance;
        }

        (running_witness, running_committed_instance)
    }
}
