use crate::transcript::Transcript;
use crate::utils::sum_check::structs::{IOPProof, IOPProverMessage, IOPProverState};
use crate::utils::sum_check::SumCheckProver;
use crate::utils::virtual_polynomial::VirtualPolynomial;
use ark_crypto_primitives::sponge::Absorb;
use ark_ec::{CurveGroup, Group};
use ark_std::fmt::Debug;
use espresso_subroutines::PolyIOPErrors;
use std::marker::PhantomData;

#[derive(Clone, Debug, Default, Copy, PartialEq, Eq)]
pub struct SumCheck<C: CurveGroup, T: Transcript<C>> {
    #[doc(hidden)]
    phantom: PhantomData<C>,
    #[doc(hidden)]
    phantom2: PhantomData<T>,
}

impl<C: CurveGroup, T: Transcript<C>> SumCheck<C, T>
where
    <C as ark_ec::Group>::ScalarField: Absorb,
{
    /// Generate a proof of the sum of polynomial over {0,1}^`num_vars`
    /// Mutates the transcript in the process
    pub fn prove(
        poly: &VirtualPolynomial<C::ScalarField>,
        transcript: &mut impl Transcript<C>,
    ) -> Result<IOPProof<C::ScalarField>, PolyIOPErrors> {
        transcript.absorb(&<C as Group>::ScalarField::from(poly.aux_info.num_variables as u64));
        transcript.absorb(&<C as Group>::ScalarField::from(poly.aux_info.max_degree as u64));
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

    #[test]
    pub fn sumcheck_poseidon() {
        let mut rng = test_rng();
        let poly_mle = DenseMultilinearExtension::rand(5, &mut rng);
        let virtual_poly = VirtualPolynomial::new_from_mle(&Arc::new(poly_mle), Fr::ONE);
        let poseidon_config = poseidon_test_config::<Fr>();
        let mut poseidon_transcript: PoseidonTranscript<Projective> =
            PoseidonTranscript::<Projective>::new(&poseidon_config);
        let sum_check = SumCheck::<Projective, PoseidonTranscript<Projective>>::prove(&virtual_poly, &mut poseidon_transcript).unwrap();
        println!("sum check proof: {:?}", sum_check);
    }
}
