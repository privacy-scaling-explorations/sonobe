use crate::transcript::Transcript;
use crate::utils::sum_check::verifier::interpolate_uni_poly_fs;
use ark_ec::CurveGroup;
use ark_ff::Field;
use ark_ff::PrimeField;
use ark_poly::{DenseMultilinearExtension, MultilinearExtension};

use rayon::iter::IndexedParallelIterator;
use rayon::iter::IntoParallelIterator;
use rayon::iter::ParallelIterator;
use thiserror::Error;

#[derive(Debug, Error, PartialEq)]
pub enum IOPError<F: PrimeField> {
    #[error("At verify step {0}, p_j-1(r) != p_0 + p_1 (p_j-1(r) = {1}, p_0 = {2}, p_1 = {3})")]
    SumCheckVerifyError(usize, F, F, F),

    #[error("Expected 0 challenges for verifier, got {0}")]
    VerifierChallengesAlreadyInitialized(usize),
}

#[derive(Clone, Debug)]
pub struct Message<F: PrimeField> {
    pub p_0: F, // P(0)
    pub p_1: F, // P(1)
}

pub struct Prover<F: PrimeField> {
    pub claimed_sum: F,
    pub current_poly: DenseMultilinearExtension<F>, // polynomial at step `current_step`
    pub current_step: usize,
}

pub struct Verifier<F: PrimeField> {
    pub verified: bool,
    pub current_step: usize,
    pub current_challenge: F,
}

pub struct SumCheck<C: CurveGroup> {
    pub prover: Prover<C::ScalarField>,
    pub verifier: Verifier<C::ScalarField>,
    pub rounds: usize,
    pub poly: DenseMultilinearExtension<C::ScalarField>,
    pub max_degree: u8,
    pub prover_messages: Vec<Message<C::ScalarField>>,
    pub verifier_challenges: Vec<C::ScalarField>,
    pub prover_finished: bool,
}

impl<C: CurveGroup> SumCheck<C> {
    /// Creates a new SumCheck instance.
    /// Assumes claimed sum is the sum of the evaluations of the polynomial over the hypercube.
    pub fn new(poly: &DenseMultilinearExtension<C::ScalarField>) -> Self {
        let claimed_sum: C::ScalarField = poly.evaluations.iter().sum::<C::ScalarField>();
        let n_vars = poly.num_vars;
        let poly = poly.clone();
        let prover = Prover {
            claimed_sum,
            current_poly: poly.clone(),
            current_step: 0,
        };
        let verifier = Verifier {
            verified: false,
            current_step: 0,
            current_challenge: C::ScalarField::ZERO,
        };
        SumCheck {
            prover,
            verifier,
            rounds: n_vars,
            poly,
            max_degree: 0,
            prover_messages: Vec::with_capacity(n_vars),
            verifier_challenges: Vec::with_capacity(n_vars),
            prover_finished: false,
        }
    }

    pub fn prove(
        &mut self,
        transcript: &mut impl Transcript<C>,
    ) -> Result<(), IOPError<C::ScalarField>> {
        let mut challenge: Option<C::ScalarField> = None;
        transcript.absorb(&C::ScalarField::from(self.poly.num_vars as u64));
        transcript.absorb(&C::ScalarField::from(self.max_degree as u64));
        for _ in 0..self.rounds {
            let message: Message<C::ScalarField> = self.perform_prover_round(challenge);
            self.prover_messages.push(message.clone());
            transcript.absorb_vec(&[message.p_0, message.p_1]);
            let verifier_challenge = transcript.get_challenge();
            challenge = Some(verifier_challenge); // see above, since its an Option, need to wrap it in Some
        }
        self.prover_finished = true;
        Ok(())
    }

    pub fn verify(
        &mut self,
        transcript: &mut impl Transcript<C>,
    ) -> Result<(), IOPError<C::ScalarField>> {
        if !self.verifier_challenges.is_empty() {
            return Err(IOPError::VerifierChallengesAlreadyInitialized(
                self.verifier_challenges.len(),
            ));
        }
        transcript.absorb(&C::ScalarField::from(self.poly.num_vars as u64));
        transcript.absorb(&C::ScalarField::from(self.max_degree as u64));

        // Verifier computes challenges
        for message in self.prover_messages.iter() {
            transcript.absorb_vec(&[message.p_0, message.p_1]);
            self.verifier_challenges.push(transcript.get_challenge());
        }

        // Verifier computes P_{j-1}(r)
        #[cfg(feature = "parallel")]
        let mut p_j_minus_1_r_vec: Vec<C::ScalarField> = self
            .prover_messages
            .clone()
            .into_par_iter()
            .zip(self.verifier_challenges.clone())
            .map(|(message, challenge)| {
                interpolate_uni_poly_fs::<C::ScalarField>(&[message.p_0, message.p_1], challenge)
            })
            .collect();

        // At index 0, P_{j-1}(r) = claimed sum
        p_j_minus_1_r_vec.insert(0, self.prover.claimed_sum);

        // Verifier checks P_{j-1}(r) = P_j(0) + P_j(1)
        // Returns IOPError as soon as one of the checks fails
        for (p_j_minus_1_r, message) in p_j_minus_1_r_vec
            .clone()
            .iter()
            .zip(self.prover_messages.clone())
        {
            if message.p_0 + message.p_1 != *p_j_minus_1_r {
                return Err(IOPError::<C::ScalarField>::SumCheckVerifyError(
                    self.verifier.current_step,
                    *p_j_minus_1_r,
                    message.p_0,
                    message.p_1,
                ));
            }
        }

        Ok(())
    }

    /// Increases current step, fixes one additional variable in the polynomial resulting in updating the prover's current polynomial.
    fn perform_prover_round(
        &mut self,
        challenge: Option<C::ScalarField>,
    ) -> Message<C::ScalarField> {
        if let Some(challenge) = challenge {
            // in first round, challenge is None
            self.prover.current_poly = self.prover.current_poly.fix_variables(&[challenge]);
        }
        let p_0 = self
            .prover
            .current_poly
            .fix_variables(&[C::ScalarField::ZERO])
            .iter()
            .sum::<C::ScalarField>();
        let p_1 = self
            .prover
            .current_poly
            .fix_variables(&[C::ScalarField::ONE])
            .iter()
            .sum::<C::ScalarField>();
        self.prover.current_step += 1;
        Message { p_0, p_1 }
    }
}

#[cfg(test)]
mod tests {
    use ark_pallas::{Fr, Projective};
    use ark_poly::{DenseMultilinearExtension, MultilinearExtension};

    use crate::transcript::{
        poseidon::{tests::poseidon_test_config, PoseidonTranscript},
        Transcript,
    };

    #[test]
    fn test_init_sumcheck() {
        let mut rng = ark_std::test_rng();
        let n_vars = 5;
        let poly = DenseMultilinearExtension::<Fr>::rand(n_vars, &mut rng);
        let sumcheck = super::SumCheck::<Projective>::new(&poly);
        assert_eq!(sumcheck.prover.current_step, 0);
        assert_eq!(sumcheck.verifier.current_step, 0);
        assert!(!sumcheck.verifier.verified);
        assert_eq!(
            sumcheck.prover.claimed_sum,
            sumcheck.poly.evaluations.iter().sum()
        );
        assert_eq!(sumcheck.verifier_challenges.len(), 0);
        assert_eq!(sumcheck.prover_messages.len(), 0);
        assert!(!sumcheck.prover_finished);
    }

    #[test]
    fn test_sumcheck() {
        let mut rng = ark_std::test_rng();
        let n_vars = 5;
        let poly = DenseMultilinearExtension::<Fr>::rand(n_vars, &mut rng);
        let mut sumcheck = super::SumCheck::<Projective>::new(&poly);
        let transcript_config = poseidon_test_config();
        let mut prover_transcript = PoseidonTranscript::<Projective>::new(&transcript_config);
        let mut verifier_transcript = PoseidonTranscript::<Projective>::new(&transcript_config);

        sumcheck.prove(&mut prover_transcript).unwrap();
        let verify = sumcheck.verify(&mut verifier_transcript);
        assert!(verify.is_ok());
    }
}
