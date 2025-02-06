use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::SynthesisError;
use ark_std::{rand::RngCore, UniformRand};

use super::decider_eth_circuit::WitnessVar;
use super::nifs::nova_circuits::CommittedInstanceVar;
use super::{CommittedInstance, Witness};
use crate::arith::{
    r1cs::{circuits::R1CSMatricesVar, R1CS},
    Arith, ArithRelation, ArithRelationGadget, ArithSampler,
};
use crate::commitment::CommitmentScheme;
use crate::folding::circuits::CF1;
use crate::utils::gadgets::{EquivalenceGadget, VectorGadget};
use crate::{Curve, Error};

/// Implements [`ArithRelation`] for R1CS, where the witness is of type
/// [`Witness`], and the committed instance is of type [`CommittedInstance`].
///
/// Due to the error terms `Witness.E` and `CommittedInstance.u`, R1CS here is
/// considered as a relaxed R1CS.
///
/// One may wonder why we do not provide distinct structs for R1CS and relaxed
/// R1CS.
/// This is because both plain R1CS and relaxed R1CS have the same structure:
/// they are both represented by three matrices.
/// What makes them different is the error terms, which are not part of the R1CS
/// struct, but are part of the witness and committed instance.
///
/// As a follow-up, one may further ask why not providing a trait for relaxed
/// R1CS and implement it for the [`R1CS`] struct, where the relaxed R1CS trait
/// has methods for relaxed satisfiability check, while the [`ArithRelation`]
/// trait that [`R1CS`] implements has methods for plain satisfiability check.
/// However, it would be more ideal if we have a single method that can smartly
/// choose the type of satisfiability check, which would make the code more
/// generic and easier to maintain.
///
/// This is achieved thanks to the new design of the [`ArithRelation`] trait,
/// where we can implement the trait for the same constraint system with
/// different types of witnesses and committed instances.
/// For R1CS, whether it is relaxed or not is now determined by the types of `W`
/// and `U`: the satisfiability check is relaxed if `W` and `U` are defined by
/// folding schemes, and plain if they are vectors of field elements.
impl<C: Curve> ArithRelation<Witness<C>, CommittedInstance<C>> for R1CS<CF1<C>> {
    type Evaluation = Vec<CF1<C>>;

    fn eval_relation(
        &self,
        w: &Witness<C>,
        u: &CommittedInstance<C>,
    ) -> Result<Self::Evaluation, Error> {
        self.eval_at_z(&[&[u.u][..], &u.x, &w.W].concat())
    }

    fn check_evaluation(
        w: &Witness<C>,
        _u: &CommittedInstance<C>,
        e: Self::Evaluation,
    ) -> Result<(), Error> {
        (w.E == e).then_some(()).ok_or(Error::NotSatisfied)
    }
}

impl<C: Curve> ArithSampler<C, Witness<C>, CommittedInstance<C>> for R1CS<CF1<C>> {
    fn sample_witness_instance<CS: CommitmentScheme<C, true>>(
        &self,
        params: &CS::ProverParams,
        mut rng: impl RngCore,
    ) -> Result<(Witness<C>, CommittedInstance<C>), Error> {
        // Implements sampling a (committed) RelaxedR1CS
        // See construction 5 in https://eprint.iacr.org/2023/573.pdf
        let u = C::ScalarField::rand(&mut rng);
        let rE = C::ScalarField::rand(&mut rng);
        let rW = C::ScalarField::rand(&mut rng);

        let W = (0..self.n_witnesses())
            .map(|_| C::ScalarField::rand(&mut rng))
            .collect();
        let x = (0..self.n_public_inputs())
            .map(|_| C::ScalarField::rand(&mut rng))
            .collect::<Vec<C::ScalarField>>();
        let mut z = vec![u];
        z.extend(&x);
        z.extend(&W);

        let E = self.eval_at_z(&z)?;

        let witness = Witness { E, rE, W, rW };
        let mut cm_witness = witness.commit::<CS, true>(params, x)?;

        // witness.commit() sets u to 1, we set it to the sampled u value
        cm_witness.u = u;

        debug_assert!(
            self.check_relation(&witness, &cm_witness).is_ok(),
            "Sampled a non satisfiable relaxed R1CS, sampled u: {}, computed E: {:?}",
            u,
            witness.E
        );

        Ok((witness, cm_witness))
    }
}

impl<C: Curve> ArithRelationGadget<WitnessVar<C>, CommittedInstanceVar<C>>
    for R1CSMatricesVar<C::ScalarField, FpVar<C::ScalarField>>
{
    type Evaluation = (Vec<FpVar<C::ScalarField>>, Vec<FpVar<C::ScalarField>>);

    fn eval_relation(
        &self,
        w: &WitnessVar<C>,
        u: &CommittedInstanceVar<C>,
    ) -> Result<Self::Evaluation, SynthesisError> {
        self.eval_at_z(&[&[u.u.clone()][..], &u.x, &w.W].concat())
    }

    fn enforce_evaluation(
        w: &WitnessVar<C>,
        _u: &CommittedInstanceVar<C>,
        (AzBz, uCz): Self::Evaluation,
    ) -> Result<(), SynthesisError> {
        EquivalenceGadget::<C::ScalarField>::enforce_equivalent(&AzBz[..], &uCz.add(&w.E)?[..])
    }
}
