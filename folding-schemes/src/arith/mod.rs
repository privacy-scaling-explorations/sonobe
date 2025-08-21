use ark_ff::PrimeField;
use ark_relations::gr1cs::SynthesisError;
use ark_std::rand::RngCore;

use crate::{commitment::CommitmentScheme, folding::traits::Dummy, Curve, Error};

pub mod ccs;
pub mod r1cs;

/// [`Arith`] is a trait about constraint systems (R1CS, CCS, etc.), where we
/// define methods for getting information about the constraint system.
pub trait Arith: Clone {
    /// Returns the degree of the constraint system
    fn degree(&self) -> usize;

    /// Returns the number of constraints in the constraint system
    fn n_constraints(&self) -> usize;

    /// Returns the number of variables in the constraint system
    fn n_variables(&self) -> usize;

    /// Returns the number of public inputs / public IO / instances / statements
    /// in the constraint system
    fn n_public_inputs(&self) -> usize;

    /// Returns the number of witnesses / secret inputs in the constraint system
    fn n_witnesses(&self) -> usize;

    /// Returns a tuple containing (w, x) (witness and public inputs respectively)
    fn split_z<F: PrimeField>(&self, z: &[F]) -> (Vec<F>, Vec<F>);
}

/// `ArithRelation` *treats a constraint system as a relation* between a witness
/// of type `W` and a statement / public input / public IO / instance of type
/// `U`, and in this trait, we define the necessary operations on the relation.
///
/// Note that the same constraint system may support different types of `W` and
/// `U`, and the satisfiability check may vary.
///
/// For example, both plain R1CS and relaxed R1CS are represented by 3 matrices,
/// but the types of `W` and `U` are different:
/// - The plain R1CS has `W` and `U` as vectors of field elements.
///   
///   `W = w` and `U = x` satisfy R1CS if `Az ∘ Bz = Cz`, where `z = [1, x, w]`.
///
/// - In Nova, Relaxed R1CS has `W` as [`crate::folding::nova::Witness`],
///   and `U` as [`crate::folding::nova::CommittedInstance`].
///  
///   `W = (w, e, ...)` and `U = (u, x, ...)` satisfy Relaxed R1CS if
///   `Az ∘ Bz = uCz + e`, where `z = [u, x, w]`.
///   (commitments in `U` are not checked here)
///
///   Also, `W` and `U` have non-native field elements as their components when
///   used as CycleFold witness and instance.
///
/// - In ProtoGalaxy, Relaxed R1CS has `W` as [`crate::folding::protogalaxy::Witness`],
///   and `U` as [`crate::folding::protogalaxy::CommittedInstance`].
///    
///   `W = (w, ...)` and `U = (x, e, β, ...)` satisfy Relaxed R1CS if
///   `e = Σ pow_i(β) v_i`, where `v = Az ∘ Bz - Cz`, `z = [1, x, w]`.
///   (commitments in `U` are not checked here)
///
/// This is also the case of CCS, where `W` and `U` may be vectors of field
/// elements, [`crate::folding::hypernova::Witness`] and [`crate::folding::hypernova::lcccs::LCCCS`],
/// or [`crate::folding::hypernova::Witness`] and [`crate::folding::hypernova::cccs::CCCS`].
pub trait ArithRelation<W, U>: Arith {
    type Evaluation;

    /// Returns a dummy witness and instance
    fn dummy_witness_instance<'a>(&'a self) -> (W, U)
    where
        W: Dummy<&'a Self>,
        U: Dummy<&'a Self>,
    {
        (W::dummy(self), U::dummy(self))
    }

    /// Evaluates the constraint system `self` at witness `w` and instance `u`.
    /// Returns the evaluation result.
    ///
    /// The evaluation result is usually a vector of field elements.
    /// For instance:
    /// - Evaluating the plain R1CS at `W = w` and `U = x` returns
    ///   `Az ∘ Bz - Cz`, where `z = [1, x, w]`.
    ///
    /// - Evaluating the relaxed R1CS in Nova at `W = (w, e, ...)` and
    ///   `U = (u, x, ...)` returns `Az ∘ Bz - uCz`, where `z = [u, x, w]`.
    ///
    /// - Evaluating the relaxed R1CS in ProtoGalaxy at `W = (w, ...)` and
    ///   `U = (x, e, β, ...)` returns `Az ∘ Bz - Cz`, where `z = [1, x, w]`.
    ///
    /// However, we use `Self::Evaluation` to represent the evaluation result
    /// for future extensibility.
    fn eval_relation(&self, w: &W, u: &U) -> Result<Self::Evaluation, Error>;

    /// Checks if the evaluation result is valid. The witness `w` and instance
    /// `u` are also parameters, because the validity check may need information
    /// contained in `w` and/or `u`.
    ///
    /// For instance:
    /// - The evaluation `v` of plain R1CS at satisfying `W` and `U` should be
    ///   an all-zero vector.
    ///
    /// - The evaluation `v` of relaxed R1CS in Nova at satisfying `W` and `U`
    ///   should be equal to the error term `e` in the witness.
    ///
    /// - The evaluation `v` of relaxed R1CS in ProtoGalaxy at satisfying `W`
    ///   and `U` should satisfy `e = Σ pow_i(β) v_i`, where `e` is the error
    ///   term in the committed instance.
    fn check_evaluation(w: &W, u: &U, v: Self::Evaluation) -> Result<(), Error>;

    /// Checks if witness `w` and instance `u` satisfy the constraint system
    /// `self` by first computing the evaluation result and then checking the
    /// validity of the evaluation result.
    ///
    /// Used only for testing.
    fn check_relation(&self, w: &W, u: &U) -> Result<(), Error> {
        let e = self.eval_relation(w, u)?;
        Self::check_evaluation(w, u, e)
    }
}

/// `ArithSerializer` is for serializing constraint systems.
///
/// Currently we only support converting parameters to bytes, but in the future
/// we may consider implementing methods for serializing the actual data (e.g.,
/// R1CS matrices).
pub trait ArithSerializer {
    /// Returns the bytes that represent the parameters, that is, the matrices sizes, the amount of
    /// public inputs, etc, without the matrices/polynomials values.
    fn params_to_le_bytes(&self) -> Vec<u8>;
}

/// `ArithSampler` allows sampling random pairs of witness and instance that
/// satisfy the constraint system `self`.
///
/// This is useful for constructing a zero-knowledge layer for a folding-based
/// IVC.
/// An example of such a layer can be found in Appendix D of the [HyperNova]
/// paper.
///
/// Note that we use a separate trait for sampling, because this operation may
/// not be supported by all witness-instance pairs.
/// For instance, it is difficult (if not impossible) to do this for `w` and `x`
/// in a plain R1CS.
///
/// [HyperNova]: https://eprint.iacr.org/2023/573.pdf
pub trait ArithSampler<C: Curve, W, U>: ArithRelation<W, U> {
    /// Samples a random witness and instance that satisfy the constraint system.
    fn sample_witness_instance<CS: CommitmentScheme<C, true>>(
        &self,
        params: &CS::ProverParams,
        rng: impl RngCore,
    ) -> Result<(W, U), Error>;
}

/// `ArithRelationGadget` defines the in-circuit counterparts of operations
/// specified in `ArithRelation` on constraint systems.
pub trait ArithRelationGadget<WVar, UVar> {
    type Evaluation;

    /// Evaluates the constraint system `self` at witness `w` and instance `u`.
    /// Returns the evaluation result.
    fn eval_relation(&self, w: &WVar, u: &UVar) -> Result<Self::Evaluation, SynthesisError>;

    /// Generates constraints for enforcing that witness `w` and instance `u`
    /// satisfy the constraint system `self` by first computing the evaluation
    /// result and then checking the validity of the evaluation result.
    fn enforce_relation(&self, w: &WVar, u: &UVar) -> Result<(), SynthesisError> {
        let e = self.eval_relation(w, u)?;
        Self::enforce_evaluation(w, u, e)
    }

    /// Generates constraints for enforcing that the evaluation result is valid.
    /// The witness `w` and instance `u` are also parameters, because the
    /// validity check may need information contained in `w` and/or `u`.
    fn enforce_evaluation(w: &WVar, u: &UVar, e: Self::Evaluation) -> Result<(), SynthesisError>;
}
