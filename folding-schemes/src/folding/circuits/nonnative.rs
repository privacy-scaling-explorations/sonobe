use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{BigInteger, PrimeField};
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    boolean::Boolean,
    fields::{
        fp::FpVar,
        nonnative::{
            params::{get_params, OptimizationType},
            AllocatedNonNativeFieldVar, NonNativeFieldVar,
        },
        FieldVar,
    },
    ToBitsGadget, ToConstraintFieldGadget,
};
use ark_relations::r1cs::{ConstraintSystemRef, Namespace, OptimizationGoal, SynthesisError};
use ark_std::Zero;
use core::borrow::Borrow;
use std::marker::PhantomData;

/// Compose a vector boolean into a `NonNativeFieldVar`
pub fn nonnative_field_var_from_le_bits<TargetField: PrimeField, BaseField: PrimeField>(
    cs: ConstraintSystemRef<BaseField>,
    bits: &[Boolean<BaseField>],
) -> Result<NonNativeFieldVar<TargetField, BaseField>, SynthesisError> {
    let params = get_params(
        TargetField::MODULUS_BIT_SIZE as usize,
        BaseField::MODULUS_BIT_SIZE as usize,
        match cs.optimization_goal() {
            OptimizationGoal::None => OptimizationType::Constraints,
            OptimizationGoal::Constraints => OptimizationType::Constraints,
            OptimizationGoal::Weight => OptimizationType::Weight,
        },
    );

    // push the lower limbs first
    let mut limbs = bits
        .chunks(params.bits_per_limb)
        .map(Boolean::le_bits_to_fp_var)
        .collect::<Result<Vec<_>, _>>()?;
    limbs.resize(params.num_limbs, FpVar::zero());
    limbs.reverse();

    Ok(AllocatedNonNativeFieldVar {
        cs,
        limbs,
        num_of_additions_over_normal_form: BaseField::one(),
        is_in_the_normal_form: false,
        target_phantom: PhantomData,
    }
    .into())
}

/// A more efficient version of `NonNativeFieldVar::to_constraint_field`
pub fn nonnative_field_var_to_constraint_field<TargetField: PrimeField, BaseField: PrimeField>(
    f: &NonNativeFieldVar<TargetField, BaseField>,
) -> Result<Vec<FpVar<BaseField>>, SynthesisError> {
    let bits = f.to_bits_le()?;

    let bits_per_limb = BaseField::MODULUS_BIT_SIZE as usize - 1;
    let num_limbs = (TargetField::MODULUS_BIT_SIZE as usize).div_ceil(bits_per_limb);

    let mut limbs = bits
        .chunks(bits_per_limb)
        .map(|chunk| {
            let mut limb = FpVar::<BaseField>::zero();
            let mut w = BaseField::one();
            for b in chunk.iter() {
                limb += FpVar::from(b.clone()) * w;
                w.double_in_place();
            }
            limb
        })
        .collect::<Vec<FpVar<BaseField>>>();
    limbs.resize(num_limbs, FpVar::zero());
    limbs.reverse();

    Ok(limbs)
}

/// The out-circuit counterpart of `nonnative_field_var_to_constraint_field`
pub fn nonnative_field_to_field_elements<TargetField: PrimeField, BaseField: PrimeField>(
    f: &TargetField,
) -> Vec<BaseField> {
    let bits = f.into_bigint().to_bits_le();

    let bits_per_limb = BaseField::MODULUS_BIT_SIZE as usize - 1;
    let num_limbs = (TargetField::MODULUS_BIT_SIZE as usize).div_ceil(bits_per_limb);

    let mut limbs = bits
        .chunks(bits_per_limb)
        .map(|chunk| {
            let mut limb = BaseField::zero();
            let mut w = BaseField::one();
            for &b in chunk.iter() {
                limb += BaseField::from(b) * w;
                w.double_in_place();
            }
            limb
        })
        .collect::<Vec<BaseField>>();
    limbs.resize(num_limbs, BaseField::zero());
    limbs.reverse();

    limbs
}

/// NonNativeAffineVar represents an elliptic curve point in Affine representation in the non-native
/// field, over the constraint field. It is not intended to perform operations, but just to contain
/// the affine coordinates in order to perform hash operations of the point.
#[derive(Debug, Clone)]
pub struct NonNativeAffineVar<C: CurveGroup>
where
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
{
    pub x: NonNativeFieldVar<C::BaseField, C::ScalarField>,
    pub y: NonNativeFieldVar<C::BaseField, C::ScalarField>,
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

            let x = NonNativeFieldVar::<C::BaseField, C::ScalarField>::new_variable(
                cs.clone(),
                || Ok(xy.0),
                mode,
            )?;
            let y = NonNativeFieldVar::<C::BaseField, C::ScalarField>::new_variable(
                cs.clone(),
                || Ok(xy.1),
                mode,
            )?;

            Ok(Self { x, y })
        })
    }
}

impl<C: CurveGroup> ToConstraintFieldGadget<C::ScalarField> for NonNativeAffineVar<C>
where
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
{
    // A more efficient version of `point_to_nonnative_limbs_custom_opt`.
    // Used for converting `NonNativeAffineVar` to a vector of `FpVar` with minimum length in
    // the circuit.
    fn to_constraint_field(&self) -> Result<Vec<FpVar<C::ScalarField>>, SynthesisError> {
        let x = nonnative_field_var_to_constraint_field(&self.x)?;
        let y = nonnative_field_var_to_constraint_field(&self.y)?;
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
        point_to_nonnative_limbs_custom_opt(p, OptimizationType::Constraints)
    }
}

// Used to compute (outside the circuit) the limbs representation of a point.
// For `OptimizationType::Constraints`, the result matches the one used in-circuit.
// For `OptimizationType::Weight`, the result vector is more dense and is suitable for hashing.
// It is possible to further optimize the length of the result vector (see
// `nonnative_affine_to_field_elements`)
#[allow(clippy::type_complexity)]
fn point_to_nonnative_limbs_custom_opt<C: CurveGroup>(
    p: C,
    optimization_type: OptimizationType,
) -> Result<(Vec<C::ScalarField>, Vec<C::ScalarField>), SynthesisError>
where
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
{
    let affine = p.into_affine();
    if affine.is_zero() {
        let x =
            AllocatedNonNativeFieldVar::<C::BaseField, C::ScalarField>::get_limbs_representations(
                &C::BaseField::zero(),
                optimization_type,
            )?;
        let y =
            AllocatedNonNativeFieldVar::<C::BaseField, C::ScalarField>::get_limbs_representations(
                &C::BaseField::zero(),
                optimization_type,
            )?;
        return Ok((x, y));
    }

    let (x, y) = affine.xy().unwrap();
    let x = AllocatedNonNativeFieldVar::<C::BaseField, C::ScalarField>::get_limbs_representations(
        x,
        optimization_type,
    )?;
    let y = AllocatedNonNativeFieldVar::<C::BaseField, C::ScalarField>::get_limbs_representations(
        y,
        optimization_type,
    )?;
    Ok((x, y))
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
    fn test_arkworks_to_constraint_field() {
        let cs = ConstraintSystem::<Fr>::new_ref();

        // check that point_to_nonnative_limbs returns the expected values
        let mut rng = ark_std::test_rng();
        let p = Projective::rand(&mut rng);
        let pVar = NonNativeAffineVar::<Projective>::new_witness(cs.clone(), || Ok(p)).unwrap();
        let (x, y) = point_to_nonnative_limbs_custom_opt(p, OptimizationType::Weight).unwrap();
        assert_eq!(pVar.x.to_constraint_field().unwrap().value().unwrap(), x);
        assert_eq!(pVar.y.to_constraint_field().unwrap().value().unwrap(), y);
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

        match (pVar.x, pVar.y) {
            (NonNativeFieldVar::Var(p_x), NonNativeFieldVar::Var(p_y)) => {
                assert_eq!(p_x.limbs.value().unwrap(), x);
                assert_eq!(p_y.limbs.value().unwrap(), y);
            }
            _ => unreachable!(),
        }
    }
}
