use ark_crypto_primitives::sponge::{
    poseidon::constraints::PoseidonSpongeVar, CryptographicSponge,
};
use ark_ff::PrimeField;
use ark_poly::Polynomial;
use ark_r1cs_std::{
    fields::{fp::FpVar, FieldVar},
    poly::{domain::Radix2DomainVar, evaluations::univariate::EvaluationsVar},
};
use ark_relations::r1cs::SynthesisError;
use ark_std::log2;

use crate::folding::traits::{CommittedInstanceOps, CommittedInstanceVarOps, Dummy, WitnessOps};
use crate::transcript::{Transcript, TranscriptVar};
use crate::utils::vec::poly_from_vec;
use crate::{arith::ArithRelation, folding::circuits::CF1};
use crate::{Curve, Error};

pub mod off_chain;
pub mod on_chain;

/// Gadget that computes the KZG challenges.
/// It also offers the rust native implementation compatible with the gadget.
pub struct KZGChallengesGadget {}

impl KZGChallengesGadget {
    pub fn get_challenges_native<C: Curve, T: Transcript<CF1<C>>, U: CommittedInstanceOps<C>>(
        transcript: &mut T,
        U_i: &U,
    ) -> Vec<CF1<C>> {
        let mut challenges = vec![];
        for cm in U_i.get_commitments() {
            transcript.absorb_nonnative(&cm);
            challenges.push(transcript.get_challenge());
        }
        challenges
    }

    pub fn get_challenges_gadget<
        C: Curve,
        S: CryptographicSponge,
        T: TranscriptVar<CF1<C>, S>,
        U: CommittedInstanceVarOps<C>,
    >(
        transcript: &mut T,
        U_i: &U,
    ) -> Result<Vec<FpVar<CF1<C>>>, SynthesisError> {
        let mut challenges = vec![];
        for cm in U_i.get_commitments() {
            transcript.absorb_nonnative(&cm)?;
            challenges.push(transcript.get_challenge()?);
        }
        Ok(challenges)
    }
}

/// Gadget that interpolates the polynomial from the given vector and returns
/// its evaluation at the given point.
/// It also offers the rust native implementation compatible with the gadget.
pub struct EvalGadget {}

impl EvalGadget {
    pub fn evaluate_native<F: PrimeField>(v: &[F], point: F) -> Result<F, Error> {
        let mut v = v.to_vec();
        v.resize(v.len().next_power_of_two(), F::zero());

        Ok(poly_from_vec(v)?.evaluate(&point))
    }

    pub fn evaluate_gadget<F: PrimeField>(
        v: &[FpVar<F>],
        point: &FpVar<F>,
    ) -> Result<FpVar<F>, SynthesisError> {
        let mut v = v.to_vec();
        v.resize(v.len().next_power_of_two(), FpVar::zero());
        let n = v.len() as u64;
        let gen = F::get_root_of_unity(n).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        // `unwrap` below is safe because `Radix2DomainVar::new` only fails if
        // `offset.enforce_not_equal(&FpVar::zero())` returns an error.
        // But in our case, `offset` is `FpVar::one()`, i.e., both operands of
        // `enforce_not_equal` are constants.
        // Consequently, `FpVar`'s implementation of `enforce_not_equal` will
        // always return `Ok(())`.
        let domain = Radix2DomainVar::new(gen, log2(v.len()) as u64, FpVar::one()).unwrap();

        let evaluations_var = EvaluationsVar::from_vec_and_domain(v, domain, true);
        evaluations_var.interpolate_and_evaluate(point)
    }
}

/// This is a temporary workaround for step 6 (running NIFS.V for group elements
/// in circuit) in an NIFS-agnostic way, because different folding schemes have
/// different interfaces of folding verification now.
///
/// In the future, we may introduce a better solution that uses a trait for all
/// folding schemes that specifies their native and in-circuit behaviors.
pub trait DeciderEnabledNIFS<
    C: Curve,
    RU: CommittedInstanceOps<C>, // Running instance
    IU: CommittedInstanceOps<C>, // Incoming instance
    W: WitnessOps<CF1<C>>,
    A: ArithRelation<W, RU>,
>
{
    type ProofDummyCfg;
    type Proof: Dummy<Self::ProofDummyCfg>;
    type RandomnessDummyCfg;
    type Randomness: Dummy<Self::RandomnessDummyCfg>;

    /// Fold the field elements in `U` and `u` inside the circuit.
    ///
    /// `U_vec` is `U` expressed as a vector of `FpVar`s, which can be reused
    /// before or after calling this function to save constraints.
    #[allow(clippy::too_many_arguments)]
    fn fold_field_elements_gadget(
        arith: &A,
        transcript: &mut PoseidonSpongeVar<CF1<C>>,
        U: RU::Var,
        U_vec: Vec<FpVar<CF1<C>>>,
        u: IU::Var,
        proof: Self::Proof,
        randomness: Self::Randomness,
    ) -> Result<RU::Var, SynthesisError>;

    /// Fold the group elements (i.e., commitments) in `U` and `u` outside the
    /// circuit.
    fn fold_group_elements_native(
        U_commitments: &[C],
        u_commitments: &[C],
        proof: Option<Self::Proof>,
        randomness: Self::Randomness,
    ) -> Result<Vec<C>, Error>;
}

#[cfg(test)]
pub mod tests {
    use ark_crypto_primitives::sponge::{
        constraints::CryptographicSpongeVar, poseidon::PoseidonSponge,
    };
    use ark_pallas::{Fr, Projective};
    use ark_r1cs_std::{alloc::AllocVar, R1CSVar};
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::UniformRand;

    use super::*;
    use crate::folding::nova::{nifs::nova_circuits::CommittedInstanceVar, CommittedInstance};
    use crate::transcript::poseidon::poseidon_canonical_config;

    // checks that the gadget and native implementations of the challenge computation match
    #[test]
    fn test_kzg_challenge_gadget() -> Result<(), Error> {
        let mut rng = ark_std::test_rng();
        let poseidon_config = poseidon_canonical_config::<Fr>();
        let mut transcript = PoseidonSponge::<Fr>::new(&poseidon_config);

        let U_i = CommittedInstance::<Projective> {
            cmE: Projective::rand(&mut rng),
            u: Fr::rand(&mut rng),
            cmW: Projective::rand(&mut rng),
            x: vec![Fr::rand(&mut rng); 1],
        };

        // compute the challenge natively
        let challenges = KZGChallengesGadget::get_challenges_native(&mut transcript, &U_i);

        let cs = ConstraintSystem::<Fr>::new_ref();
        let U_iVar =
            CommittedInstanceVar::<Projective>::new_witness(cs.clone(), || Ok(U_i.clone()))?;
        let mut transcript_var = PoseidonSpongeVar::<Fr>::new(cs.clone(), &poseidon_config);

        let challenges_var =
            KZGChallengesGadget::get_challenges_gadget(&mut transcript_var, &U_iVar)?;
        assert!(cs.is_satisfied()?);

        // check that the natively computed and in-circuit computed hashes match
        assert_eq!(challenges_var.value()?, challenges);
        Ok(())
    }

    #[test]
    fn test_polynomial_interpolation() -> Result<(), Error> {
        let mut rng = ark_std::test_rng();
        let n = 12;
        let l = 1 << n;

        let v: Vec<Fr> = std::iter::repeat_with(|| Fr::rand(&mut rng))
            .take(l)
            .collect();
        let challenge = Fr::rand(&mut rng);

        use ark_poly::Polynomial;
        let polynomial = poly_from_vec(v.to_vec())?;
        let eval = polynomial.evaluate(&challenge);

        let cs = ConstraintSystem::<Fr>::new_ref();
        let vVar = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(v))?;
        let challengeVar = FpVar::<Fr>::new_witness(cs.clone(), || Ok(challenge))?;

        let evalVar = EvalGadget::evaluate_gadget(&vVar, &challengeVar)?;

        assert_eq!(evalVar.value()?, eval);
        assert!(cs.is_satisfied()?);
        Ok(())
    }
}
