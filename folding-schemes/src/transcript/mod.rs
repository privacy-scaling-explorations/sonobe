use ark_crypto_primitives::sponge::{constraints::CryptographicSpongeVar, CryptographicSponge};
use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use ark_r1cs_std::{boolean::Boolean, fields::fp::FpVar, groups::CurveVar};
use ark_relations::r1cs::SynthesisError;

pub mod poseidon;

/// An interface for objects that can be absorbed by a `Transcript`.
///
/// Matches `Absorb` in `ark-crypto-primitives`.
pub trait AbsorbNonNative {
    /// Converts the object into field elements that can be absorbed by a `Transcript`.
    /// Append the list to `dest`
    fn to_native_sponge_field_elements<F: PrimeField>(&self, dest: &mut Vec<F>);

    /// Converts the object into field elements that can be absorbed by a `Transcript`.
    /// Return the list as `Vec`
    fn to_native_sponge_field_elements_as_vec<F: PrimeField>(&self) -> Vec<F> {
        let mut result = Vec::new();
        self.to_native_sponge_field_elements(&mut result);
        result
    }
}

/// An interface for objects that can be absorbed by a `TranscriptVar` whose constraint field
/// is `F`.
///
/// Matches `AbsorbGadget` in `ark-crypto-primitives`.
pub trait AbsorbNonNativeGadget<F: PrimeField> {
    /// Converts the object into field elements that can be absorbed by a `TranscriptVar`.
    fn to_native_sponge_field_elements(&self) -> Result<Vec<FpVar<F>>, SynthesisError>;
}

impl<T: AbsorbNonNative> AbsorbNonNative for [T] {
    fn to_native_sponge_field_elements<F: PrimeField>(&self, dest: &mut Vec<F>) {
        for t in self.iter() {
            t.to_native_sponge_field_elements(dest);
        }
    }
}

impl<F: PrimeField, T: AbsorbNonNativeGadget<F>> AbsorbNonNativeGadget<F> for &T {
    fn to_native_sponge_field_elements(&self) -> Result<Vec<FpVar<F>>, SynthesisError> {
        T::to_native_sponge_field_elements(self)
    }
}

impl<F: PrimeField, T: AbsorbNonNativeGadget<F>> AbsorbNonNativeGadget<F> for [T] {
    fn to_native_sponge_field_elements(&self) -> Result<Vec<FpVar<F>>, SynthesisError> {
        let mut result = Vec::new();
        for t in self.iter() {
            result.extend(t.to_native_sponge_field_elements()?);
        }
        Ok(result)
    }
}

pub trait Transcript<F: PrimeField>: CryptographicSponge {
    /// `new_with_pp_hash` creates a new transcript / sponge with the given
    /// hash of the public parameters.
    fn new_with_pp_hash(config: &Self::Config, pp_hash: F) -> Self;

    /// `absorb_point` is for absorbing points whose `BaseField` is the field of
    /// the sponge, i.e., the type `C` of these points should satisfy
    /// `C::BaseField = F`.
    ///
    /// If the sponge field `F` is `C::ScalarField`, call `absorb_nonnative`
    /// instead.
    fn absorb_point<C: CurveGroup<BaseField = F>>(&mut self, v: &C);
    /// `absorb_nonnative` is for structs that contain non-native (field or
    /// group) elements, including:
    ///
    /// - A field element of type `T: PrimeField` that will be absorbed into a
    ///   sponge that operates in another field `F != T`.
    /// - A group element of type `C: CurveGroup` that will be absorbed into a
    ///   sponge that operates in another field `F != C::BaseField`, e.g.,
    ///   `F = C::ScalarField`.
    /// - A `CommittedInstance` on the secondary curve (used for CycleFold) that
    ///   will be absorbed into a sponge that operates in the (scalar field of
    ///   the) primary curve.
    ///
    ///   Note that although a `CommittedInstance` for `AugmentedFCircuit` on
    ///   the primary curve also contains non-native elements, we still regard
    ///   it as native, because the sponge is on the same curve.
    fn absorb_nonnative<V: AbsorbNonNative>(&mut self, v: &V);

    fn get_challenge(&mut self) -> F;
    /// get_challenge_nbits returns a field element of size nbits
    fn get_challenge_nbits(&mut self, nbits: usize) -> Vec<bool>;
    fn get_challenges(&mut self, n: usize) -> Vec<F>;
}

pub trait TranscriptVar<F: PrimeField, S: CryptographicSponge>:
    CryptographicSpongeVar<F, S>
{
    /// `new_with_pp_hash` creates a new transcript / sponge with the given
    /// hash of the public parameters.
    fn new_with_pp_hash(
        config: &Self::Parameters,
        pp_hash: &FpVar<F>,
    ) -> Result<Self, SynthesisError>;

    /// `absorb_point` is for absorbing points whose `BaseField` is the field of
    /// the sponge, i.e., the type `C` of these points should satisfy
    /// `C::BaseField = F`.
    ///
    /// If the sponge field `F` is `C::ScalarField`, call `absorb_nonnative`
    /// instead.
    fn absorb_point<C: CurveGroup<BaseField = F>, GC: CurveVar<C, F>>(
        &mut self,
        v: &GC,
    ) -> Result<(), SynthesisError>;
    /// `absorb_nonnative` is for structs that contain non-native (field or
    /// group) elements, including:
    ///
    /// - A field element of type `T: PrimeField` that will be absorbed into a
    ///   sponge that operates in another field `F != T`.
    /// - A group element of type `C: CurveGroup` that will be absorbed into a
    ///   sponge that operates in another field `F != C::BaseField`, e.g.,
    ///   `F = C::ScalarField`.
    /// - A `CommittedInstance` on the secondary curve (used for CycleFold) that
    ///   will be absorbed into a sponge that operates in the (scalar field of
    ///   the) primary curve.
    ///
    ///   Note that although a `CommittedInstance` for `AugmentedFCircuit` on
    ///   the primary curve also contains non-native elements, we still regard
    ///   it as native, because the sponge is on the same curve.
    fn absorb_nonnative<V: AbsorbNonNativeGadget<F>>(
        &mut self,
        v: &V,
    ) -> Result<(), SynthesisError>;

    fn get_challenge(&mut self) -> Result<FpVar<F>, SynthesisError>;
    /// returns the bit representation of the challenge, we use its output in-circuit for the
    /// `GC.scalar_mul_le` method.
    fn get_challenge_nbits(&mut self, nbits: usize) -> Result<Vec<Boolean<F>>, SynthesisError>;
    fn get_challenges(&mut self, n: usize) -> Result<Vec<FpVar<F>>, SynthesisError>;
}
