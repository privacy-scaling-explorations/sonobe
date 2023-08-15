use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use ark_std::{fmt::Debug, rand::RngCore};

pub mod transcript;

#[derive(Debug)]
pub enum Error {}

pub trait Transcript<F: PrimeField> {
    type TranscriptConfig: Debug;

    fn new(config: &Self::TranscriptConfig) -> Self;
    fn absorb(&mut self, v: &F);
    fn absorb_vec(&mut self, v: &[F]);
    fn get_challenge(&mut self) -> F;
    fn get_challenges(&mut self, n: usize) -> Vec<F>;
}

pub trait FoldingScheme<C: CurveGroup>: Clone + Debug {
    // type PCS: PolynomialCommitmentScheme<C>; // maybe not needed, just PedersenCommitment
    type PreprocessorParam: Debug;
    type ProverParam: Debug;
    type VerifierParam: Debug;
    type FreshInstance: Debug;
    type PublicInput: Debug;
    type CommittedInstanceWithWitness: Debug;
    type CommittedInstance: Clone + Debug;

    fn preprocess(
        // pcs_param: &<Self::CS as PolynomialCommitmentScheme<C>>::Param,
        prep_param: &Self::PreprocessorParam,
    ) -> Result<(Self::ProverParam, Self::VerifierParam), Error>;

    fn init_accumulator(
        pp: &Self::ProverParam,
    ) -> Result<Self::CommittedInstanceWithWitness, Error>;

    fn prove(
        pp: &Self::ProverParam,
        running_instance: &mut Self::CommittedInstanceWithWitness,
        incomming_instances: &[Self::FreshInstance],
        transcript: &mut impl Transcript<C::ScalarField>,
        rng: impl RngCore,
    ) -> Result<(), Error>;

    fn verify(
        vp: &Self::VerifierParam,
        running_instance: &mut Self::CommittedInstance,
        incomming_instances: &[Self::PublicInput],
        transcript: &mut impl Transcript<C::ScalarField>,
        rng: impl RngCore,
    ) -> Result<(), Error>;
}

pub trait Decider<C: CurveGroup>: Clone + Debug {
    type PreprocessorParam: Debug;
    type ProverParam: Debug;
    type VerifierParam: Debug;
    type FreshInstance: Debug;
    type PublicInput: Debug;
    type CommittedInstanceWithWitness: Debug;
    type CommittedInstance: Clone + Debug;

    fn prove(
        pp: &Self::ProverParam,
        running_instance: &Self::CommittedInstanceWithWitness,
        transcript: &mut impl Transcript<C::ScalarField>,
        rng: impl RngCore,
    ) -> Result<(), Error>;

    fn verify(
        vp: &Self::VerifierParam,
        running_instance: &Self::CommittedInstance,
        transcript: &mut impl Transcript<C::ScalarField>,
        rng: impl RngCore,
    ) -> Result<(), Error>;
}
