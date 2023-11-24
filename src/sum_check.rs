use crate::transcript::Transcript;
use crate::transcript::TranscriptWithAppendableMessagesExt;
use crate::utils::sum_check::structs::{IOPProof, IOPProverMessage, IOPProverState};
use crate::utils::sum_check::SumCheckProver;
use crate::utils::virtual_polynomial::VirtualPolynomial;
use ark_crypto_primitives::sponge::Absorb;
use ark_ec::{CurveGroup, Group};
use ark_ff::PrimeField;
use ark_serialize::CanonicalSerialize;
use ark_std::fmt::Debug;
use espresso_subroutines::PolyIOPErrors;
use espresso_transcript::to_bytes;
use std::marker::PhantomData;

#[derive(Clone, Debug, Default, Copy, PartialEq, Eq)]
pub struct SumCheck<C: CurveGroup, T: Transcript<C>> {
    #[doc(hidden)]
    phantom: PhantomData<C>,
    #[doc(hidden)]
    phantom2: PhantomData<T>,
}

pub struct SumCheckTranscript<C: CurveGroup, T: Transcript<C>> {
    #[doc(hidden)]
    phantom: PhantomData<C>,
    transcript: T,
    // We need an additional field to store challenges
    transcript_data: Vec<C::ScalarField>,
}

/// We implement two missing functions from the Transcript trait
/// This is primarily done for compatibility with the Espresso's hpyerplonk implem
/// TODO: Should have proper Option<> return types
impl<C: CurveGroup, T: Transcript<C>> TranscriptWithAppendableMessagesExt<C>
    for SumCheckTranscript<C, T>
where
    <C as Group>::ScalarField: Absorb,
{
    fn append_serializable_element<S: CanonicalSerialize>(
        &mut self,
        label: &'static [u8],
        group_elem: &S,
    ) {
        // TODO: hyperplonk uses Merlin Transcripts, figure out how to abstract the used hash function using it (or not)
        // For now, we omit the label parameter
        let message = &to_bytes!(group_elem).unwrap();
        let element = C::ScalarField::from_be_bytes_mod_order(message);
        self.transcript_data.push(element);
    }

    fn get_and_append_challenge(&mut self, label: &'static [u8]) -> C::ScalarField {
        // TODO: hyperplonk uses Merlin Transcripts, figure out how to abstract the used hash function using it (or not)
        // For now, we go for the naive solution of hashing the first previous appended message (unsecure)
        let challenge = self.transcript_data.last().unwrap();
        self.transcript.absorb(challenge);
        self.transcript.get_challenge()
    }
}

impl<C: CurveGroup, T: Transcript<C>> SumCheck<C, T>
where
    <C as ark_ec::Group>::ScalarField: Absorb,
{
    /// Generate a proof of the sum of polynomial over {0,1}^`num_vars`
    /// Mutates the transcript in the process
    pub fn prove(
        poly: &VirtualPolynomial<C::ScalarField>,
        transcript: &mut SumCheckTranscript<C, T>,
    ) -> Result<IOPProof<C::ScalarField>, PolyIOPErrors> {
        transcript.append_serializable_element(b"aux info", &poly.aux_info);
        let mut prover_state: IOPProverState<C::ScalarField> = IOPProverState::prover_init(poly)?;
        let mut challenge: Option<C::ScalarField> = None;
        let mut prover_msgs: Vec<IOPProverMessage<C::ScalarField>> =
            Vec::with_capacity(poly.aux_info.num_variables);
        for _ in 0..poly.aux_info.num_variables {
            let prover_msg: IOPProverMessage<C::ScalarField> =
                IOPProverState::prove_round_and_update_state(&mut prover_state, &challenge)?;
            transcript.append_serializable_element(b"prover msg", &prover_msg);
            prover_msgs.push(prover_msg);
            challenge = Some(transcript.get_and_append_challenge(b"Internal round"));
        }
        if let Some(p) = challenge {
            prover_state.challenges.push(p)
        };
        Ok(IOPProof {
            point: prover_state.challenges,
            proofs: prover_msgs,
        })
    }
}

#[cfg(test)]
pub mod tests {
    use std::sync::Arc;

    use ark_ff::Field;
    use ark_pallas::Fr;
    use ark_pallas::Projective;
    use ark_poly::DenseMultilinearExtension;
    use ark_poly::MultilinearExtension;
    use ark_std::test_rng;

    use crate::transcript::poseidon::tests::poseidon_test_config;
    use crate::transcript::poseidon::PoseidonTranscript;
    use crate::transcript::Transcript;
    use crate::utils::virtual_polynomial::VirtualPolynomial;

    use super::SumCheck;
    use super::SumCheckTranscript;

    #[test]
    pub fn sumcheck_poseidon() {
        let mut rng = test_rng();
        let poly_mle = DenseMultilinearExtension::rand(5, &mut rng);
        let virtual_poly = VirtualPolynomial::new_from_mle(&Arc::new(poly_mle), Fr::ONE);
        let poseidon_config = poseidon_test_config::<Fr>();
        let poseidon_transcript: PoseidonTranscript<Projective> =
            PoseidonTranscript::<Projective>::new(&poseidon_config);
        let mut transcript: SumCheckTranscript<Projective, PoseidonTranscript<Projective>> = SumCheckTranscript {
            phantom: Default::default(),
            transcript: poseidon_transcript,
            transcript_data: Vec::new(),
        };
        let _sum_check = SumCheck::prove(&virtual_poly, &mut transcript).unwrap();
    }
}
