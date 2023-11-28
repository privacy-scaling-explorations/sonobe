use crate::transcript::Transcript;
use crate::utils::sum_check::structs::{
    IOPProof, IOPProverMessage, IOPProverState, IOPVerifierStateGeneric,
};
use crate::utils::sum_check::{
    SumCheckGeneric, SumCheckProver, SumCheckSubClaim, SumCheckVerifierGeneric,
};
use crate::utils::virtual_polynomial::{VPAuxInfo, VirtualPolynomial};
use ark_crypto_primitives::sponge::Absorb;
use ark_ec::{CurveGroup, Group};
use ark_poly::DenseMultilinearExtension;
use ark_std::fmt::Debug;
use espresso_subroutines::PolyIOPErrors;
use std::marker::PhantomData;
use std::sync::Arc;

#[derive(Clone, Debug, Default, Copy, PartialEq, Eq)]
pub struct SumCheck<C: CurveGroup, T: Transcript<C>> {
    #[doc(hidden)]
    phantom: PhantomData<C>,
    #[doc(hidden)]
    phantom2: PhantomData<T>,
}

impl<C: CurveGroup, T: Transcript<C>> SumCheckGeneric<C> for SumCheck<C, T>
where
    <C as ark_ec::Group>::ScalarField: Absorb,
{
    type VirtualPolynomial = VirtualPolynomial<C::ScalarField>;
    type VPAuxInfo = VPAuxInfo<C::ScalarField>;
    type MultilinearExtension = Arc<DenseMultilinearExtension<C::ScalarField>>;
    type SumCheckProof = IOPProof<C::ScalarField>;
    type SumCheckSubClaim = SumCheckSubClaim<C::ScalarField>;

    /// Generate a proof of the sum of polynomial over {0,1}^`num_vars`
    /// Mutates the transcript in the process
    fn prove(
        poly: &VirtualPolynomial<C::ScalarField>,
        transcript: &mut impl Transcript<C>,
    ) -> Result<IOPProof<C::ScalarField>, PolyIOPErrors> {
        transcript.absorb(&<C as Group>::ScalarField::from(
            poly.aux_info.num_variables as u64,
        ));
        transcript.absorb(&<C as Group>::ScalarField::from(
            poly.aux_info.max_degree as u64,
        ));
        let mut prover_state: IOPProverState<C::ScalarField> = IOPProverState::prover_init(poly)?;
        let mut challenge: Option<C::ScalarField> = None;
        let mut prover_msgs: Vec<IOPProverMessage<C::ScalarField>> =
            Vec::with_capacity(poly.aux_info.num_variables);
        for _ in 0..poly.aux_info.num_variables {
            let prover_msg: IOPProverMessage<C::ScalarField> =
                IOPProverState::prove_round_and_update_state(&mut prover_state, &challenge)?;
            transcript.absorb_vec(&prover_msg.evaluations);
            prover_msgs.push(prover_msg);
            challenge = Some(transcript.get_challenge());
        }
        if let Some(p) = challenge {
            prover_state.challenges.push(p)
        };
        Ok(IOPProof {
            point: prover_state.challenges,
            proofs: prover_msgs,
        })
    }

    fn verify(
        claimed_sum: C::ScalarField,
        proof: &IOPProof<C::ScalarField>,
        aux_info: &VPAuxInfo<C::ScalarField>,
        transcript: &mut impl Transcript<C>,
    ) -> Result<SumCheckSubClaim<C::ScalarField>, PolyIOPErrors> {
        transcript.absorb(&<C as Group>::ScalarField::from(
            aux_info.num_variables as u64,
        ));
        transcript.absorb(&<C as Group>::ScalarField::from(aux_info.max_degree as u64));
        let mut verifier_state = IOPVerifierStateGeneric::verifier_init(aux_info);
        for i in 0..aux_info.num_variables {
            let prover_msg = proof.proofs.get(i).expect("proof is incomplete");
            transcript.absorb_vec(&prover_msg.evaluations);
            IOPVerifierStateGeneric::verify_round_and_update_state(
                &mut verifier_state,
                prover_msg,
                transcript,
            )?;
        }

        IOPVerifierStateGeneric::check_and_generate_subclaim(&verifier_state, &claimed_sum)
    }

    fn extract_sum(proof: &Self::SumCheckProof) -> C::ScalarField {
        proof.proofs[0].evaluations[0] + proof.proofs[0].evaluations[1]
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
    use crate::utils::sum_check::SumCheckGeneric;
    use crate::utils::virtual_polynomial::VirtualPolynomial;

    use super::SumCheck;

    #[test]
    pub fn sumcheck_poseidon() {
        let mut rng = test_rng();
        let poly_mle = DenseMultilinearExtension::rand(5, &mut rng);
        let virtual_poly = VirtualPolynomial::new_from_mle(&Arc::new(poly_mle), Fr::ONE);
        let poseidon_config = poseidon_test_config::<Fr>();

        // sum-check prove
        let mut poseidon_transcript_prove: PoseidonTranscript<Projective> =
            PoseidonTranscript::<Projective>::new(&poseidon_config);
        let sum_check = SumCheck::<Projective, PoseidonTranscript<Projective>>::prove(
            &virtual_poly,
            &mut poseidon_transcript_prove,
        )
        .unwrap();

        // sum-check verify
        let claimed_sum =
            SumCheck::<Projective, PoseidonTranscript<Projective>>::extract_sum(&sum_check);
        let mut poseidon_transcript_verify: PoseidonTranscript<Projective> =
            PoseidonTranscript::<Projective>::new(&poseidon_config);
        let res_verify = SumCheck::<Projective, PoseidonTranscript<Projective>>::verify(
            claimed_sum,
            &sum_check,
            &virtual_poly.aux_info,
            &mut poseidon_transcript_verify,
        );

        assert!(res_verify.is_ok());
    }
}
