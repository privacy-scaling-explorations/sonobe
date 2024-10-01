/// contains [Nova](https://eprint.iacr.org/2021/370.pdf) related circuits
///
///
use super::CommittedInstance;
use crate::constants::NOVA_N_BITS_RO;
use crate::transcript::Transcript;
use ark_crypto_primitives::sponge::Absorb;
use ark_ec::{CurveGroup, Group};
use ark_ff::PrimeField;
use core::marker::PhantomData;

pub struct ChallengeGadget<C: CurveGroup> {
    _c: PhantomData<C>,
}
impl<C: CurveGroup> ChallengeGadget<C>
where
    C: CurveGroup,
    <C as CurveGroup>::BaseField: PrimeField,
    <C as Group>::ScalarField: Absorb,
{
    pub fn get_challenge_native<T: Transcript<C::ScalarField>>(
        transcript: &mut T,
        pp_hash: C::ScalarField, // public params hash
        // Running instance
        U_i: CommittedInstance<C>,
        // Incoming instance
        u_i: CommittedInstance<C>,
    ) -> Vec<bool> {
        // NOTICE: This isn't following the order of the HackMD.
        // As long as we match it. We should not have any issues.
        transcript.absorb(&pp_hash);
        transcript.absorb(&U_i);
        transcript.absorb(&u_i);
        transcript.squeeze_bits(NOVA_N_BITS_RO)
    }
}
