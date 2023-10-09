use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{BigInteger, PrimeField};
use ark_r1cs_std::fields::nonnative::{params::OptimizationType, AllocatedNonNativeFieldVar};
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    fields::fp::FpVar,
    fields::nonnative::{NonNativeFieldConfig, NonNativeFieldVar},
};
use ark_relations::{
    ns,
    r1cs::{Namespace, Result as R1CSResult, SynthesisError},
};
use core::{borrow::Borrow, marker::PhantomData};

/// NonNativeAffineVar represents an elliptic curve point in Affine represenation in the non-native
/// field. It is not intended to perform operations, but just to contain the affine coordinates in
/// order to perform hash operations of the point.
#[derive(Debug, Clone)]
pub struct NonNativeAffineVar<F: PrimeField, CF: PrimeField> {
    pub x: NonNativeFieldVar<F, CF>,
    pub y: NonNativeFieldVar<F, CF>,
}

impl<C> AllocVar<C, C::ScalarField> for NonNativeAffineVar<C::BaseField, C::ScalarField>
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
            let xy = affine.xy().unwrap();
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

/// point_to_nonnative_limbs is used to return (outside the circuit) the limbs representation that
/// matches the one used in-circuit.
#[allow(clippy::type_complexity)]
pub fn point_to_nonnative_limbs<C: CurveGroup>(
    p: C,
) -> Result<(Vec<C::ScalarField>, Vec<C::ScalarField>), SynthesisError>
where
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
{
    let affine = p.into_affine();
    let (x, y) = affine.xy().unwrap();
    let x = AllocatedNonNativeFieldVar::<C::BaseField, C::ScalarField>::get_limbs_representations(
        x,
        OptimizationType::Weight,
    )?;
    let y = AllocatedNonNativeFieldVar::<C::BaseField, C::ScalarField>::get_limbs_representations(
        y,
        OptimizationType::Weight,
    )?;
    Ok((x, y))
}

/// NonNativeFieldReprVar represents an elliptic curve point in Affine represenation in the non-native
/// field. It is not intended to perform operations, but just to contain the affine coordinates in
/// order to perform hash operations of the point.
pub struct NonNativeFieldReprVar<TargetField: PrimeField, BaseField: PrimeField> {
    _t: PhantomData<TargetField>,
    _b: PhantomData<BaseField>,
    pub allocated: AllocatedNonNativeFieldVar<TargetField, BaseField>,
}

impl<TargetField: PrimeField, BaseField: PrimeField> AllocVar<TargetField, BaseField>
    for NonNativeFieldReprVar<TargetField, BaseField>
{
    fn new_variable<T: Borrow<TargetField>>(
        cs: impl Into<Namespace<BaseField>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> R1CSResult<Self> {
        let ns = cs.into();
        let cs = ns.cs();
        let this = Self::new_variable_unchecked(ns!(cs, "alloc"), f, mode)?;
        // if mode == AllocationMode::Witness {
        //     this.enforce_in_range(ns!(cs, "bits"))?;
        // }
        Ok(Self {
            _t: PhantomData,
            _b: PhantomData,
            allocated: this,
        })
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField> NonNativeFieldReprVar<TargetField, BaseField> {
    fn new_variable_unchecked<T: Borrow<TargetField>>(
        cs: impl Into<Namespace<BaseField>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> R1CSResult<AllocatedNonNativeFieldVar<TargetField, BaseField>> {
        let ns = cs.into();
        let cs = ns.cs();

        let zero = TargetField::zero();

        let elem = match f() {
            Ok(t) => *(t.borrow()),
            Err(_) => zero,
        };
        let elem_representations = Self::get_limbs_representations(&elem)?;
        let mut limbs = Vec::new();

        for limb in elem_representations.iter() {
            limbs.push(FpVar::<BaseField>::new_variable(
                ark_relations::ns!(cs, "alloc"),
                || Ok(limb),
                mode,
            )?);
        }

        let num_of_additions_over_normal_form = if mode != AllocationMode::Witness {
            BaseField::zero()
        } else {
            BaseField::one()
        };

        Ok(AllocatedNonNativeFieldVar {
            cs,
            limbs,
            num_of_additions_over_normal_form,
            is_in_the_normal_form: mode != AllocationMode::Witness,
            target_phantom: PhantomData,
        })
    }

    pub fn get_limbs_representations(elem: &TargetField) -> R1CSResult<Vec<BaseField>> {
        Self::get_limbs_representations_from_big_integer(&elem.into_bigint())
    }

    pub fn get_limbs_representations_from_big_integer(
        elem: &<TargetField as PrimeField>::BigInt,
    ) -> R1CSResult<Vec<BaseField>> {
        let params = NonNativeFieldConfig {
            num_limbs: 2,
            bits_per_limb: BaseField::MODULUS_BIT_SIZE as usize - 1,
        };

        // push the lower limbs first
        let mut limbs: Vec<BaseField> = Vec::new();
        let mut cur = *elem;
        for _ in 0..params.num_limbs {
            let cur_bits = cur.to_bits_be(); // `to_bits` is big endian
            let cur_mod_r = <BaseField as PrimeField>::BigInt::from_bits_be(
                &cur_bits[cur_bits.len() - params.bits_per_limb..],
            ); // therefore, the lowest `bits_per_non_top_limb` bits is what we want.
            limbs.push(BaseField::from_bigint(cur_mod_r).unwrap());
            cur.divn(params.bits_per_limb as u32);
        }

        // then we reserve, so that the limbs are ``big limb first''
        limbs.reverse();

        Ok(limbs)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_r1cs_std::{alloc::AllocVar, R1CSVar};
    use ark_relations::r1cs::ConstraintSystem;
    use ark_vesta::{Fq, Fr};

    #[test]
    fn test_nonnative_repr() {
        let cs = ConstraintSystem::<Fr>::new_ref();

        let vBI = Fr::MODULUS;
        dbg!(&vBI);
        let v = Fq::from_bigint(vBI).unwrap();
        // let v = Fq::rand(&mut rng);
        dbg!(&v);

        let vReprVar =
            NonNativeFieldReprVar::<Fq, Fr>::new_witness(cs.clone(), || Ok(v.clone())).unwrap();
        let vVar = vReprVar.allocated;
        dbg!(v);
        dbg!(vVar.limbs.value().unwrap());
        dbg!(vVar.value().unwrap()); // TODO this fails to recover the original value
        assert_eq!(vVar.value().unwrap(), v);
    }
}
