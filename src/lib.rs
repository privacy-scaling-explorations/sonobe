use ark_ec::CurveGroup;
use ark_std::{fmt::Debug, rand::RngCore};

#[derive(Debug)]
pub enum Error {}

pub trait Transcript<C: CurveGroup>: Debug {
    // todos
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
        transcript: &mut impl Transcript<C>,
        rng: impl RngCore,
    ) -> Result<(), Error>;

    fn verify(
        vp: &Self::VerifierParam,
        running_instance: &mut Self::CommittedInstance,
        incomming_instances: &[Self::PublicInput],
        transcript: &mut impl Transcript<C>,
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
        transcript: &mut impl Transcript<C>,
        rng: impl RngCore,
    ) -> Result<(), Error>;

    fn verify(
        vp: &Self::VerifierParam,
        running_instance: &Self::CommittedInstance,
        transcript: &mut impl Transcript<C>,
        rng: impl RngCore,
    ) -> Result<(), Error>;
}
