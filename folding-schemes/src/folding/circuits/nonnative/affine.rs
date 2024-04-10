use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::PrimeField;
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    fields::fp::FpVar,
    ToConstraintFieldGadget,
};
use ark_relations::r1cs::{Namespace, SynthesisError};
use ark_std::Zero;
use core::borrow::Borrow;

use super::uint::{nonnative_field_to_field_elements, NonNativeUintVar};

/// NonNativeAffineVar represents an elliptic curve point in Affine representation in the non-native
/// field, over the constraint field. It is not intended to perform operations, but just to contain
/// the affine coordinates in order to perform hash operations of the point.
#[derive(Debug, Clone)]
pub struct NonNativeAffineVar<C: CurveGroup>
where
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
{
    pub x: NonNativeUintVar<C::ScalarField>,
    pub y: NonNativeUintVar<C::ScalarField>,
}

impl<C> AllocVar<C, C::ScalarField> for NonNativeAffineVar<C>
where
    C: CurveGroup,
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
{
    fn new_variable<T: Borrow<C>>(
        cs: impl Into<Namespace<C::ScalarField>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|val| {
            let cs = cs.into();

            let affine = val.borrow().into_affine();
            let zero_point = (&C::BaseField::zero(), &C::BaseField::zero());
            let xy = affine.xy().unwrap_or(zero_point);

            let x = NonNativeUintVar::new_variable(cs.clone(), || Ok(*xy.0), mode)?;
            let y = NonNativeUintVar::new_variable(cs.clone(), || Ok(*xy.1), mode)?;

            Ok(Self { x, y })
        })
    }
}

impl<C: CurveGroup> ToConstraintFieldGadget<C::ScalarField> for NonNativeAffineVar<C>
where
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
{
    // Used for converting `NonNativeAffineVar` to a vector of `FpVar` with minimum length in
    // the circuit.
    fn to_constraint_field(&self) -> Result<Vec<FpVar<C::ScalarField>>, SynthesisError> {
        let x = self.x.to_constraint_field()?;
        let y = self.y.to_constraint_field()?;
        Ok([x, y].concat())
    }
}

/// The out-circuit counterpart of `NonNativeAffineVar::to_constraint_field`
#[allow(clippy::type_complexity)]
pub fn nonnative_affine_to_field_elements<C: CurveGroup>(
    p: C,
) -> Result<(Vec<C::ScalarField>, Vec<C::ScalarField>), SynthesisError>
where
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
{
    let affine = p.into_affine();
    if affine.is_zero() {
        let x = nonnative_field_to_field_elements(&C::BaseField::zero());
        let y = nonnative_field_to_field_elements(&C::BaseField::zero());
        return Ok((x, y));
    }

    let (x, y) = affine.xy().unwrap();
    let x = nonnative_field_to_field_elements(x);
    let y = nonnative_field_to_field_elements(y);
    Ok((x, y))
}

impl<C: CurveGroup> NonNativeAffineVar<C>
where
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
{
    // A wrapper of `point_to_nonnative_limbs_custom_opt` with constraints-focused optimization
    // type (which is the default optimization type for arkworks' Groth16).
    // Used for extracting a list of field elements of type `C::ScalarField` from the public input
    // `p`, in exactly the same way as how `NonNativeAffineVar` is represented as limbs of type
    // `FpVar` in-circuit.
    pub fn inputize(p: C) -> Result<(Vec<C::ScalarField>, Vec<C::ScalarField>), SynthesisError> {
        let affine = p.into_affine();
        if affine.is_zero() {
            let x = NonNativeUintVar::inputize(
                &(C::ScalarField::zero()).into(),
                C::ScalarField::MODULUS_BIT_SIZE as usize,
            );
            let y = NonNativeUintVar::inputize(
                &(C::ScalarField::zero()).into(),
                C::ScalarField::MODULUS_BIT_SIZE as usize,
            );
            return Ok((x, y));
        }

        let (x, y) = affine.xy().unwrap();
        let x = NonNativeUintVar::inputize(&(*x).into(), C::ScalarField::MODULUS_BIT_SIZE as usize);
        let y = NonNativeUintVar::inputize(&(*y).into(), C::ScalarField::MODULUS_BIT_SIZE as usize);
        Ok((x, y))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_pallas::{Fr, Projective};
    use ark_r1cs_std::{alloc::AllocVar, R1CSVar, ToConstraintFieldGadget};
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::{UniformRand, Zero};

    #[test]
    fn test_alloc_zero() {
        let cs = ConstraintSystem::<Fr>::new_ref();

        // dealing with the 'zero' point should not panic when doing the unwrap
        let p = Projective::zero();
        assert!(NonNativeAffineVar::<Projective>::new_witness(cs.clone(), || Ok(p)).is_ok());
    }

    #[test]
    fn test_improved_to_constraint_field() {
        let cs = ConstraintSystem::<Fr>::new_ref();

        // check that point_to_nonnative_limbs returns the expected values
        let mut rng = ark_std::test_rng();
        let p = Projective::rand(&mut rng);
        let pVar = NonNativeAffineVar::<Projective>::new_witness(cs.clone(), || Ok(p)).unwrap();
        let (x, y) = nonnative_affine_to_field_elements(p).unwrap();
        assert_eq!(
            pVar.to_constraint_field().unwrap().value().unwrap(),
            [x, y].concat()
        );
    }

    #[test]
    fn test_inputize() {
        let cs = ConstraintSystem::<Fr>::new_ref();

        // check that point_to_nonnative_limbs returns the expected values
        let mut rng = ark_std::test_rng();
        let p = Projective::rand(&mut rng);
        let pVar = NonNativeAffineVar::<Projective>::new_witness(cs.clone(), || Ok(p)).unwrap();
        let (x, y) = NonNativeAffineVar::inputize(p).unwrap();

        assert_eq!(pVar.x.0.value().unwrap(), x);
        assert_eq!(pVar.y.0.value().unwrap(), y);
    }
}
