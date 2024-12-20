use ark_ec::{
    short_weierstrass::{Projective, SWCurveConfig, SWFlags},
    AffineRepr, CurveGroup,
};
use ark_ff::{Field, PrimeField};
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    eq::EqGadget,
    fields::fp::FpVar,
    prelude::Boolean,
    R1CSVar,
};
use ark_relations::r1cs::{ConstraintSystemRef, Namespace, SynthesisError};
use ark_serialize::{CanonicalSerialize, CanonicalSerializeWithFlags};
use ark_std::{borrow::Borrow, Zero};

use crate::{
    folding::traits::Inputize,
    transcript::{AbsorbNonNative, AbsorbNonNativeGadget},
    SonobeCurve, SonobeField,
};

use super::uint::NonNativeUintVar;

/// NonNativeAffineVar represents an elliptic curve point in Affine representation in the non-native
/// field, over the constraint field. It is not intended to perform operations, but just to contain
/// the affine coordinates in order to perform hash operations of the point.
#[derive(Debug, Clone)]
pub struct NonNativeAffineVar<C: SonobeCurve> {
    pub x: NonNativeUintVar<C::ScalarField>,
    pub y: NonNativeUintVar<C::ScalarField>,
}

impl<C: SonobeCurve> AllocVar<C, C::ScalarField> for NonNativeAffineVar<C> {
    fn new_variable<T: Borrow<C>>(
        cs: impl Into<Namespace<C::ScalarField>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|val| {
            let cs = cs.into();

            let affine = val.borrow().into_affine();
            let (x, y) = affine.xy().unwrap_or_default();

            let x = NonNativeUintVar::new_variable(cs.clone(), || Ok(x), mode)?;
            let y = NonNativeUintVar::new_variable(cs.clone(), || Ok(y), mode)?;

            Ok(Self { x, y })
        })
    }
}

impl<C: SonobeCurve> R1CSVar<C::ScalarField> for NonNativeAffineVar<C> {
    type Value = C;

    fn cs(&self) -> ConstraintSystemRef<C::ScalarField> {
        self.x.cs().or(self.y.cs())
    }

    fn value(&self) -> Result<Self::Value, SynthesisError> {
        debug_assert_eq!(C::BaseField::extension_degree(), 1);

        let x = <C::BaseField as Field>::BasePrimeField::from_le_bytes_mod_order(
            &self.x.value()?.to_bytes_le(),
        );
        let y = <C::BaseField as Field>::BasePrimeField::from_le_bytes_mod_order(
            &self.y.value()?.to_bytes_le(),
        );
        // Below is a workaround to convert the `x` and `y` coordinates to a
        // point. This is because the `SonobeCurve` trait does not provide a
        // method to construct a point from `BaseField` elements.
        let mut bytes = vec![];
        // `unwrap` below is safe because serialization of a `PrimeField` value
        // only fails if the serialization flag has more than 8 bits, but here
        // we call `serialize_uncompressed` which uses an empty flag.
        x.serialize_uncompressed(&mut bytes).unwrap();
        // `unwrap` below is also safe, because the bit size of `SWFlags` is 2.
        y.serialize_with_flags(
            &mut bytes,
            if x.is_zero() && y.is_zero() {
                SWFlags::PointAtInfinity
            } else if y <= -y {
                SWFlags::YIsPositive
            } else {
                SWFlags::YIsNegative
            },
        )
        .unwrap();
        // `unwrap` below is safe because `bytes` is constructed from the `x`
        // and `y` coordinates of a valid point, and these coordinates are
        // serialized in the same way as the `SonobeCurve` implementation.
        Ok(C::deserialize_uncompressed_unchecked(&bytes[..]).unwrap())
    }
}

impl<C: SonobeCurve> EqGadget<C::ScalarField> for NonNativeAffineVar<C> {
    fn is_eq(&self, other: &Self) -> Result<Boolean<C::ScalarField>, SynthesisError> {
        let mut result = Boolean::TRUE;
        if self.x.0.len() != other.x.0.len() {
            return Err(SynthesisError::Unsatisfiable);
        }
        if self.y.0.len() != other.y.0.len() {
            return Err(SynthesisError::Unsatisfiable);
        }
        for (l, r) in self
            .x
            .0
            .iter()
            .chain(&self.y.0)
            .zip(other.x.0.iter().chain(&other.y.0))
        {
            if l.ub != r.ub {
                return Err(SynthesisError::Unsatisfiable);
            }
            result &= l.v.is_eq(&r.v)?;
        }
        Ok(result)
    }

    fn enforce_equal(&self, other: &Self) -> Result<(), SynthesisError> {
        if self.x.0.len() != other.x.0.len() {
            return Err(SynthesisError::Unsatisfiable);
        }
        if self.y.0.len() != other.y.0.len() {
            return Err(SynthesisError::Unsatisfiable);
        }
        for (l, r) in self
            .x
            .0
            .iter()
            .chain(&self.y.0)
            .zip(other.x.0.iter().chain(&other.y.0))
        {
            if l.ub != r.ub {
                return Err(SynthesisError::Unsatisfiable);
            }
            l.v.enforce_equal(&r.v)?;
        }
        Ok(())
    }
}

impl<C: SonobeCurve> Inputize<C::ScalarField, NonNativeAffineVar<C>> for C {
    fn inputize(&self) -> Vec<C::ScalarField> {
        let affine = self.into_affine();
        let (x, y) = affine.xy().unwrap_or_default();

        let x = x.inputize();
        let y = y.inputize();
        [x, y].concat()
    }
}

impl<C: SonobeCurve> NonNativeAffineVar<C> {
    pub fn zero() -> Self {
        // `unwrap` below is safe because we are allocating a constant value,
        // which is guaranteed to succeed.
        Self::new_constant(ConstraintSystemRef::None, C::zero()).unwrap()
    }
}

impl<P: SWCurveConfig<ScalarField: SonobeField, BaseField: SonobeField>> AbsorbNonNative
    for Projective<P>
{
    fn to_native_sponge_field_elements<F: PrimeField>(&self, dest: &mut Vec<F>) {
        let affine = self.into_affine();
        let (x, y) = affine.xy().unwrap_or_default();

        x.to_native_sponge_field_elements(dest);
        y.to_native_sponge_field_elements(dest);
    }
}

impl<C: SonobeCurve> AbsorbNonNativeGadget<C::ScalarField> for NonNativeAffineVar<C> {
    fn to_native_sponge_field_elements(
        &self,
    ) -> Result<Vec<FpVar<C::ScalarField>>, SynthesisError> {
        let x = self.x.to_native_sponge_field_elements()?;
        let y = self.y.to_native_sponge_field_elements()?;
        Ok([x, y].concat())
    }
}

#[cfg(test)]
mod tests {
    use ark_pallas::{Fr, Projective};
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::UniformRand;

    use super::*;
    use crate::Error;

    #[test]
    fn test_alloc_zero() {
        let cs = ConstraintSystem::<Fr>::new_ref();

        // dealing with the 'zero' point should not panic when doing the unwrap
        let p = Projective::zero();
        assert!(NonNativeAffineVar::<Projective>::new_witness(cs.clone(), || Ok(p)).is_ok());
    }

    #[test]
    fn test_improved_to_hash_preimage() -> Result<(), Error> {
        let cs = ConstraintSystem::<Fr>::new_ref();

        // check that point_to_nonnative_limbs returns the expected values
        let mut rng = ark_std::test_rng();
        let p = Projective::rand(&mut rng);
        let pVar = NonNativeAffineVar::<Projective>::new_witness(cs.clone(), || Ok(p))?;
        assert_eq!(
            pVar.to_native_sponge_field_elements()?.value()?,
            p.to_native_sponge_field_elements_as_vec()
        );
        Ok(())
    }

    #[test]
    fn test_inputize() -> Result<(), Error> {
        let cs = ConstraintSystem::<Fr>::new_ref();

        // check that point_to_nonnative_limbs returns the expected values
        let mut rng = ark_std::test_rng();
        let p = Projective::rand(&mut rng);
        let pVar = NonNativeAffineVar::<Projective>::new_witness(cs.clone(), || Ok(p))?;
        let xy = p.inputize();

        assert_eq!([pVar.x.0.value()?, pVar.y.0.value()?].concat(), xy);
        Ok(())
    }
}
