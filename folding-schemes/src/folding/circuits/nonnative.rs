use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{BigInteger, PrimeField};
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    fields::{
        fp::FpVar,
        nonnative::{params::OptimizationType, AllocatedNonNativeFieldVar, NonNativeFieldVar},
        FieldVar,
    },
    ToBitsGadget,
};
use ark_relations::r1cs::{Namespace, SynthesisError};
use ark_std::Zero;
use core::borrow::Borrow;

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

/// Wrapper on top of [`point_to_nonnative_limbs_custom_opt`] which always uses
/// [`OptimizationType::Weight`].
#[allow(clippy::type_complexity)]
pub fn point_to_nonnative_limbs<C: CurveGroup>(
    p: C,
) -> Result<(Vec<C::ScalarField>, Vec<C::ScalarField>), SynthesisError>
where
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
{
    point_to_nonnative_limbs_custom_opt(p, OptimizationType::Weight)
}

/// Used to compute (outside the circuit) the limbs representation of a point that matches the one
/// used in-circuit, and in particular this method allows to specify which [`OptimizationType`] to
/// use.
#[allow(clippy::type_complexity)]
pub fn point_to_nonnative_limbs_custom_opt<C: CurveGroup>(
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
    fn test_alloc_nonnativeaffinevar() {
        let cs = ConstraintSystem::<Fr>::new_ref();

        // dealing with the 'zero' point should not panic when doing the unwrap
        let p = Projective::zero();
        NonNativeAffineVar::<Projective>::new_witness(cs.clone(), || Ok(p)).unwrap();

        // check that point_to_nonnative_limbs returns the expected values
        let mut rng = ark_std::test_rng();
        let p = Projective::rand(&mut rng);
        let pVar = NonNativeAffineVar::<Projective>::new_witness(cs.clone(), || Ok(p)).unwrap();
        let (x, y) = point_to_nonnative_limbs(p).unwrap();
        assert_eq!(pVar.x.to_constraint_field().unwrap().value().unwrap(), x);
        assert_eq!(pVar.y.to_constraint_field().unwrap().value().unwrap(), y);
    }
}
