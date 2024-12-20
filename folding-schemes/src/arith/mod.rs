//! Trait definitions and implementations for arithmetic constraint systems.
//!
//! This module provides core abstractions for working with different types of arithmetic
//! constraint systems like R1CS (Rank-1 Constraint Systems) and CCS (Customizable Constraint Systems).
//! The key trait [`Arith`] defines a generic interface that constraint systems must implement,
//! allowing the rest of the library to work with different constraint system implementations in a
//! uniform way.
//!
//! # Key Traits
//!
//! * [`Arith`] - Core trait defining operations that constraint systems must support
//! * [`ArithGadget`] - In-circuit counterpart operations for constraint systems
//! * [`ArithSampler`] - Optional trait for sampling random satisfying witness-instance pairs
//! * [`ArithSerializer`] - Serialization support for constraint systems
//!
//! # Modules
//!
//! * [`ccs`] - Implementation of Customizable Constraint Systems (CCS)
//! * [`r1cs`] - Implementation of Rank-1 Constraint Systems (R1CS)
//!
//! # Examples of Supported Systems
//!
//! The module supports various constraint system types including:
//!
//! * Plain R1CS - Traditional rank-1 constraint systems
//! * Nova's Relaxed R1CS - Modified R1CS with relaxation terms
//! * ProtoGalaxy's Relaxed R1CS - Alternative relaxation approach
//! * CCS - Customizable constraint systems with different witness/instance types
//!
//! Each system can define its own witness (`W`) and instance (`U`) types while implementing
//! the common [`Arith`] interface, allowing for flexible constraint system implementations
//! while maintaining a consistent API.
//!
//! # Evaluation Types
//!
//! Different constraint systems can have different evaluation semantics:
//!
//! * Plain R1CS evaluates to `Az ∘ Bz - Cz`
//! * Nova's Relaxed R1CS evaluates to `Az ∘ Bz - uCz`
//! * ProtoGalaxy's version evaluates to `Az ∘ Bz - Cz`
//! * CCS can have various evaluation forms
//!
//! The [`Arith`] trait's associated `Evaluation` type allows each system to define its own
//! evaluation result type while maintaining type safety.

use ark_ec::CurveGroup;
use ark_relations::r1cs::SynthesisError;
use ark_std::rand::RngCore;

use crate::{commitment::CommitmentScheme, folding::traits::Dummy, Error};

pub mod ccs;
pub mod r1cs;

/// `Arith` defines the operations that a constraint system (e.g., R1CS, CCS,
/// etc.) should support.
///
/// Here, `W` is the type of witness, and `U` is the type of statement / public
/// input / public IO / instance.
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
pub trait Arith<W, U>: Clone {
    /// The type for the output of the relation's evalation.
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
    /// - Evaluating the relaxed R1CS in [`crate::folding::protogalaxy`] at `W = (w, ...)` and
    ///   `U = (x, e, β, ...)` returns `Az ∘ Bz - Cz`, where `z = [1, x, w]`.
    ///
    /// However, we use `Self::Evaluation` to represent the evaluation result
    /// for future extensibility.
    ///     
    /// # Errors
    /// Returns an error if:
    /// - The dimensions of vectors don't match the expected sizes
    /// - The evaluation calculations fail
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
    /// - The evaluation `v` of relaxed R1CS in [`crate::folding::protogalaxy`] at satisfying `W`
    ///   and `U` should satisfy `e = Σ pow_i(β) v_i`, where `e` is the error
    ///   term in the committed instance.
    ///
    /// # Errors
    /// Returns an error if:
    /// - The evaluation result is not valid for the given witness and instance
    /// - The evaluation result fails to satisfy the constraint system requirements
    fn check_evaluation(w: &W, u: &U, v: Self::Evaluation) -> Result<(), Error>;

    /// Checks if witness `w` and instance `u` satisfy the constraint system
    /// `self` by first computing the evaluation result and then checking the
    /// validity of the evaluation result.
    ///
    /// Used only for testing.
    ///
    /// # Errors
    /// Returns an error if:
    /// - The evaluation fails (`eval_relation` errors)
    /// - The evaluation check fails (`check_evaluation` errors)
    /// - The witness and instance do not satisfy the constraint system
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
pub trait ArithSampler<C: CurveGroup, W, U>: Arith<W, U> {
    /// Samples a random witness and instance that satisfy the constraint system.
    ///
    /// # Errors
    /// Returns an error if:
    /// - Sampling of random values fails
    /// - The commitment scheme operations fail
    /// - The sampled values do not satisfy the constraint system
    fn sample_witness_instance<CS: CommitmentScheme<C, true>>(
        &self,
        params: &CS::ProverParams,
        rng: impl RngCore,
    ) -> Result<(W, U), Error>;
}

/// `ArithGadget` defines the in-circuit counterparts of operations specified in
/// `Arith` on constraint systems.
pub trait ArithGadget<WVar, UVar> {
    /// The type for the output of the relation's evalation.
    type Evaluation;

    /// Evaluates the constraint system `self` at witness `w` and instance `u`.
    /// Returns the evaluation result.
    ///
    /// # Errors
    /// Returns a `SynthesisError` if:
    /// - Circuit constraint generation fails
    /// - Variable allocation fails
    /// - Required witness values are missing
    fn eval_relation(&self, w: &WVar, u: &UVar) -> Result<Self::Evaluation, SynthesisError>;

    /// Generates constraints for enforcing that witness `w` and instance `u`
    /// satisfy the constraint system `self` by first computing the evaluation
    /// result and then checking the validity of the evaluation result.
    ///
    /// # Errors
    /// Returns a `SynthesisError` if:
    /// - The evaluation fails (`eval_relation` errors)
    /// - The enforcement of evaluation constraints fails
    /// - Circuit constraint generation fails
    fn enforce_relation(&self, w: &WVar, u: &UVar) -> Result<(), SynthesisError> {
        let e = self.eval_relation(w, u)?;
        Self::enforce_evaluation(w, u, e)
    }

    /// Generates constraints for enforcing that the evaluation result is valid.
    /// The witness `w` and instance `u` are also parameters, because the
    /// validity check may need information contained in `w` and/or `u`.
    ///
    /// # Errors
    /// Returns a `SynthesisError` if:
    /// - Circuit constraint generation fails for the evaluation check
    /// - The enforcement of evaluation constraints fails
    fn enforce_evaluation(w: &WVar, u: &UVar, e: Self::Evaluation) -> Result<(), SynthesisError>;
}
