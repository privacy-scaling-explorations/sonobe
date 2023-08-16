#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]

use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use ark_std::{fmt::Debug, rand::RngCore};
use thiserror::Error;

pub mod transcript;

#[derive(Debug, Error)]
pub enum Error {
    #[error("Relation not satisfied")]
    NotSatisfied,
}

pub trait Transcript<F: PrimeField> {
    type TranscriptConfig: Debug;

    fn new(config: &Self::TranscriptConfig) -> Self;
    fn absorb(&mut self, v: &F);
    fn absorb_vec(&mut self, v: &[F]);
    fn get_challenge(&mut self) -> F;
    fn get_challenges(&mut self, n: usize) -> Vec<F>;
}

/// FoldingScheme defines trait that is implemented by the diverse folding schemes. It is defined
/// over a cycle of curves (C1, C2), where:
/// - C1 is the main curve, which ScalarField we use as our F for al the field operations
/// - C2 is the auxiliary curve, which we use for the commitments, whose BaseField (for point
/// coordinates) are in the C1::ScalarField
pub trait FoldingScheme<C1: CurveGroup, C2: CurveGroup>: Clone + Debug {
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
        transcript: &mut impl Transcript<C1::ScalarField>,
        rng: impl RngCore,
    ) -> Result<(), Error>;

    fn verify(
        vp: &Self::VerifierParam,
        running_instance: &mut Self::CommittedInstance,
        incomming_instances: &[Self::PublicInput],
        transcript: &mut impl Transcript<C1::ScalarField>,
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
