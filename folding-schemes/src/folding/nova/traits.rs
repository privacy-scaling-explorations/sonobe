use ark_crypto_primitives::sponge::Absorb;
use ark_ec::CurveGroup;
use ark_std::fmt::Debug;
use ark_std::{rand::RngCore, UniformRand};

use super::{CommittedInstance, Witness};
use crate::arith::ArithSampler;
use crate::arith::{r1cs::R1CS, Arith};
use crate::commitment::CommitmentScheme;
use crate::folding::circuits::CF1;
use crate::transcript::Transcript;
use crate::Error;

/// Defines the NIFS (Non-Interactive Folding Scheme) trait, initially defined in
/// [Nova](https://eprint.iacr.org/2021/370.pdf), and it's variants
/// [Ova](https://hackmd.io/V4838nnlRKal9ZiTHiGYzw) and
/// [Mova](https://eprint.iacr.org/2024/1220.pdf).
/// `H` specifies whether the NIFS will use a blinding factor.
pub trait NIFSTrait<C: CurveGroup, CS: CommitmentScheme<C, H>, const H: bool = false> {
    type CommittedInstance: Debug + Clone + Absorb;
    type Witness: Debug + Clone;
    type ProverAux: Debug + Clone; // Prover's aux params
    type VerifierAux: Debug + Clone; // Verifier's aux params

    fn new_witness(w: Vec<C::ScalarField>, e_len: usize, rng: impl RngCore) -> Self::Witness;
    fn new_instance(
        w: &Self::Witness,
        params: &CS::ProverParams,
        x: Vec<C::ScalarField>,
        aux: Vec<C::ScalarField>, // t_or_e in Ova, empty for Nova
    ) -> Result<Self::CommittedInstance, Error>;

    fn fold_witness(
        r: C::ScalarField,
        W: &Self::Witness, // running witness
        w: &Self::Witness, // incoming witness
        aux: &Self::ProverAux,
    ) -> Result<Self::Witness, Error>;

    /// computes the auxiliary parameters, eg. in Nova: (T, cmT), in Ova: T
    fn compute_aux(
        cs_prover_params: &CS::ProverParams,
        r1cs: &R1CS<C::ScalarField>,
        W_i: &Self::Witness,
        U_i: &Self::CommittedInstance,
        w_i: &Self::Witness,
        u_i: &Self::CommittedInstance,
    ) -> Result<(Self::ProverAux, Self::VerifierAux), Error>;

    fn get_challenge<T: Transcript<C::ScalarField>>(
        transcript: &mut T,
        pp_hash: C::ScalarField, // public params hash
        U_i: &Self::CommittedInstance,
        u_i: &Self::CommittedInstance,
        aux: &Self::VerifierAux, // ie. in Nova wouild be cmT, in Ova it's empty
    ) -> Vec<bool>;

    /// NIFS.P. Notice that this method is implemented at the trait level, and depends on the other
    /// two methods `fold_witness` and `verify`.
    fn prove(
        r: C::ScalarField,
        W_i: &Self::Witness,           // running witness
        U_i: &Self::CommittedInstance, // running committed instance
        w_i: &Self::Witness,           // incoming witness
        u_i: &Self::CommittedInstance, // incoming committed instance
        aux_p: &Self::ProverAux,
        aux_v: &Self::VerifierAux,
    ) -> Result<(Self::Witness, Self::CommittedInstance), Error> {
        let w = Self::fold_witness(r, W_i, w_i, aux_p)?;
        let ci = Self::verify(r, U_i, u_i, aux_v);
        Ok((w, ci))
    }

    /// NIFS.V
    fn verify(
        // r comes from the transcript, and is a n-bit (N_BITS_CHALLENGE) element
        r: C::ScalarField,
        U_i: &Self::CommittedInstance,
        u_i: &Self::CommittedInstance,
        aux: &Self::VerifierAux,
    ) -> Self::CommittedInstance;
}

/// Implements `Arith` for R1CS, where the witness is of type [`Witness`], and
/// the committed instance is of type [`CommittedInstance`].
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
/// R1CS and implement it for the `R1CS` struct, where the relaxed R1CS trait
/// has methods for relaxed satisfiability check, while the `Arith` trait that
/// `R1CS` implements has methods for plain satisfiability check.
/// However, it would be more ideal if we have a single method that can smartly
/// choose the type of satisfiability check, which would make the code more
/// generic and easier to maintain.
///
/// This is achieved thanks to the new design of the [`Arith`] trait, where we
/// can implement the trait for the same constraint system with different types
/// of witnesses and committed instances.
/// For R1CS, whether it is relaxed or not is now determined by the types of `W`
/// and `U`: the satisfiability check is relaxed if `W` and `U` are defined by
/// folding schemes, and plain if they are vectors of field elements.
impl<C: CurveGroup> Arith<Witness<C>, CommittedInstance<C>> for R1CS<CF1<C>> {
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

impl<C: CurveGroup> ArithSampler<C, Witness<C>, CommittedInstance<C>> for R1CS<CF1<C>> {
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

        let W = (0..self.A.n_cols - self.l - 1)
            .map(|_| C::ScalarField::rand(&mut rng))
            .collect();
        let x = (0..self.l)
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
