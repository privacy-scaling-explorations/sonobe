use std::{
    borrow::Borrow,
    cmp::{max, min},
};

use ark_ff::{BigInteger, One, PrimeField, Zero};
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    boolean::Boolean,
    fields::{fp::FpVar, FieldVar},
    prelude::EqGadget,
    select::CondSelectGadget,
    R1CSVar, ToBitsGadget, ToConstraintFieldGadget,
};
use ark_relations::r1cs::{ConstraintSystemRef, Namespace, SynthesisError};
use num_bigint::BigUint;
use num_integer::Integer;

// TODO: Add comments & unit tests

#[derive(Debug, Clone)]
pub struct LimbVar<F: PrimeField> {
    pub v: FpVar<F>,
    pub ub: BigUint,
}

impl<F: PrimeField, B: AsRef<[Boolean<F>]>> From<B> for LimbVar<F> {
    fn from(bits: B) -> Self {
        Self {
            v: Boolean::le_bits_to_fp_var(bits.as_ref()).unwrap(),
            ub: (BigUint::one() << bits.as_ref().len()) - BigUint::one(),
        }
    }
}

impl<F: PrimeField> Default for LimbVar<F> {
    fn default() -> Self {
        Self {
            v: FpVar::zero(),
            ub: BigUint::zero(),
        }
    }
}

impl<F: PrimeField> R1CSVar<F> for LimbVar<F> {
    type Value = F;

    fn cs(&self) -> ConstraintSystemRef<F> {
        self.v.cs()
    }

    fn value(&self) -> Result<Self::Value, SynthesisError> {
        self.v.value()
    }
}

impl<F: PrimeField> CondSelectGadget<F> for LimbVar<F> {
    fn conditionally_select(
        cond: &Boolean<F>,
        true_value: &Self,
        false_value: &Self,
    ) -> Result<Self, SynthesisError> {
        assert_eq!(true_value.ub, false_value.ub);
        Ok(Self {
            v: cond.select(&true_value.v, &false_value.v)?,
            ub: true_value.ub.clone(),
        })
    }
}

impl<F: PrimeField> LimbVar<F> {
    fn add(&self, other: &Self) -> Option<Self> {
        let ubound = &self.ub + &other.ub;
        if ubound < F::MODULUS_MINUS_ONE_DIV_TWO.into() {
            Some(Self {
                v: &self.v + &other.v,
                ub: ubound,
            })
        } else {
            None
        }
    }

    fn mul(&self, other: &Self) -> Option<Self> {
        let ubound = &self.ub * &other.ub;
        if ubound < F::MODULUS_MINUS_ONE_DIV_TWO.into() {
            Some(Self {
                v: &self.v * &other.v,
                ub: ubound,
            })
        } else {
            None
        }
    }

    fn zero() -> Self {
        Self::default()
    }

    fn constant(v: F) -> Self {
        Self {
            v: FpVar::constant(v),
            ub: v.into(),
        }
    }
}

impl<F: PrimeField> ToBitsGadget<F> for LimbVar<F> {
    fn to_bits_le(&self) -> Result<Vec<Boolean<F>>, SynthesisError> {
        let cs = self.cs();

        let bits = &self
            .v
            .value()
            .unwrap_or_default()
            .into_bigint()
            .to_bits_le()[..self.ub.bits() as usize];
        let bits = if cs.is_none() {
            Vec::new_constant(cs, bits)?
        } else {
            Vec::new_witness(cs, || Ok(bits))?
        };

        Boolean::le_bits_to_fp_var(&bits)?.enforce_equal(&self.v)?;

        Ok(bits)
    }
}

#[derive(Debug, Clone)]
pub struct NonNativeUintVar<F: PrimeField>(pub Vec<LimbVar<F>>);

impl<F: PrimeField> NonNativeUintVar<F> {
    const fn bits_per_limb() -> usize {
        assert!(F::MODULUS_BIT_SIZE >= 250);
        // TODO: explain why 56
        // TODO: either make it a global const, or compute an optimal value based on the modulus size
        56
    }
}

struct BoundedBigUint(BigUint, usize);

impl<F: PrimeField> AllocVar<BoundedBigUint, F> for NonNativeUintVar<F> {
    fn new_variable<T: Borrow<BoundedBigUint>>(
        cs: impl Into<Namespace<F>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let cs = cs.into().cs();
        let v = f()?;
        let BoundedBigUint(x, l) = v.borrow();

        let mut limbs = vec![];
        for chunk in (0..*l)
            .map(|i| x.bit(i as u64))
            .collect::<Vec<_>>()
            .chunks(Self::bits_per_limb())
        {
            let limb = F::from_bigint(F::BigInt::from_bits_le(chunk)).unwrap();
            let limb = FpVar::new_variable(cs.clone(), || Ok(limb), mode)?;
            Self::enforce_bit_length(&limb, chunk.len())?;
            limbs.push(LimbVar {
                v: limb,
                ub: (BigUint::one() << chunk.len()) - BigUint::one(),
            });
        }

        Ok(Self(limbs))
    }
}

impl<F: PrimeField, G: PrimeField> AllocVar<G, F> for NonNativeUintVar<F> {
    fn new_variable<T: Borrow<G>>(
        cs: impl Into<Namespace<F>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let cs = cs.into().cs();
        let v = f()?;
        let v = v.borrow();

        let mut limbs = vec![];

        for chunk in v.into_bigint().to_bits_le().chunks(Self::bits_per_limb()) {
            let limb = F::from_bigint(F::BigInt::from_bits_le(chunk)).unwrap();
            let limb = FpVar::new_variable(cs.clone(), || Ok(limb), mode)?;
            Self::enforce_bit_length(&limb, chunk.len())?;
            limbs.push(LimbVar {
                v: limb,
                ub: (BigUint::one() << chunk.len()) - BigUint::one(),
            });
        }

        Ok(Self(limbs))
    }
}

impl<F: PrimeField> NonNativeUintVar<F> {
    pub fn inputize(x: &BigUint, l: usize) -> Vec<F> {
        (0..l)
            .map(|i| x.bit(i as u64))
            .collect::<Vec<_>>()
            .chunks(Self::bits_per_limb())
            .map(|chunk| F::from_bigint(F::BigInt::from_bits_le(chunk)).unwrap())
            .collect()
    }
}

impl<F: PrimeField> R1CSVar<F> for NonNativeUintVar<F> {
    type Value = BigUint;

    fn cs(&self) -> ConstraintSystemRef<F> {
        self.0.cs()
    }

    fn value(&self) -> Result<Self::Value, SynthesisError> {
        let mut r = BigUint::zero();

        for limb in self.0.value()?.into_iter().rev() {
            r <<= Self::bits_per_limb();
            r += Into::<BigUint>::into(limb);
        }

        Ok(r)
    }
}

impl<F: PrimeField> NonNativeUintVar<F> {
    pub fn enforce_equal_unaligned(&self, other: &Self) -> Result<(), SynthesisError> {
        let cs = self.cs().or(other.cs());
        let len = min(self.0.len(), other.0.len());

        let (steps, xxs, yys, rest) = {
            let mut steps = vec![];
            let mut x_grouped = vec![];
            let mut y_grouped = vec![];
            let mut i = 0;
            while i < len {
                let mut j = i;
                let mut xx = LimbVar::zero();
                let mut yy = LimbVar::zero();
                while j < len {
                    let delta = BigUint::one() << (Self::bits_per_limb() * (j - i));
                    assert!(delta < F::MODULUS_MINUS_ONE_DIV_TWO.into());
                    let delta = LimbVar::constant(delta.into());
                    match (
                        self.0[j].mul(&delta).and_then(|x| xx.add(&x)),
                        other.0[j].mul(&delta).and_then(|y| yy.add(&y)),
                    ) {
                        (Some(x), Some(y)) => (xx, yy) = (x, y),
                        _ => break,
                    }
                    j += 1;
                }
                steps.push((j - i) * Self::bits_per_limb());
                x_grouped.push(xx);
                y_grouped.push(yy);
                i = j;
            }
            let mut rest = LimbVar::zero();
            for v in &(if i < self.0.len() { self } else { other }).0[i..] {
                rest = rest.add(v).unwrap();
            }
            (steps, x_grouped, y_grouped, rest.v)
        };
        let n = steps.len();
        let mut acc = BigUint::zero();
        let mut c = FpVar::<F>::zero();
        for i in 0..n {
            let step = steps[i];
            let max_ubound = max(xxs[i].ub.clone(), yys[i].ub.clone());
            acc += &max_ubound;
            let carry_width = (max_ubound.bits() as usize + 1)
                .checked_sub(step)
                .unwrap_or_default();
            let z = &xxs[i].v + F::from(max_ubound) - &yys[i].v;
            let c_prev = c.clone();
            c = {
                let c: BigUint = (&z + c).value().unwrap_or_default().into();
                if cs.is_none() {
                    FpVar::constant(F::from(c >> step))
                } else {
                    FpVar::new_witness(cs.clone(), || Ok(F::from(c >> step)))?
                }
            };
            let (q, r) = acc.div_rem(&(BigUint::one() << step));
            if i == n - 1 {
                (&c + &rest).enforce_equal(&FpVar::constant(F::from(q.clone())))?;
            } else {
                Self::enforce_bit_length(&c, carry_width)?;
            }

            (z + c_prev).enforce_equal(&(&c * F::from(BigUint::one() << step) + F::from(r)))?;
            acc = q;
        }

        Ok(())
    }
}

impl<F: PrimeField> ToBitsGadget<F> for NonNativeUintVar<F> {
    fn to_bits_le(&self) -> Result<Vec<Boolean<F>>, SynthesisError> {
        Ok(self
            .0
            .iter()
            .map(|limb| limb.to_bits_le())
            .collect::<Result<Vec<_>, _>>()?
            .concat())
    }
}

impl<F: PrimeField> ToConstraintFieldGadget<F> for NonNativeUintVar<F> {
    fn to_constraint_field(&self) -> Result<Vec<FpVar<F>>, SynthesisError> {
        let bits_per_limb = F::MODULUS_BIT_SIZE as usize - 1;

        let limbs = self
            .to_bits_le()?
            .chunks(bits_per_limb)
            .map(Boolean::le_bits_to_fp_var)
            .collect::<Result<Vec<_>, _>>()?;

        Ok(limbs)
    }
}

impl<F: PrimeField> CondSelectGadget<F> for NonNativeUintVar<F> {
    fn conditionally_select(
        cond: &Boolean<F>,
        true_value: &Self,
        false_value: &Self,
    ) -> Result<Self, SynthesisError> {
        assert_eq!(true_value.0.len(), false_value.0.len());
        let mut v = vec![];
        for i in 0..true_value.0.len() {
            v.push(cond.select(&true_value.0[i], &false_value.0[i])?);
        }
        Ok(Self(v))
    }
}

impl<F: PrimeField> NonNativeUintVar<F> {
    pub fn ubound(&self) -> BigUint {
        let mut r = BigUint::zero();

        for i in self.0.iter().rev() {
            r <<= Self::bits_per_limb();
            r += &i.ub;
        }

        r
    }

    fn enforce_bit_length(x: &FpVar<F>, length: usize) -> Result<Vec<Boolean<F>>, SynthesisError> {
        let cs = x.cs();

        let bits = &x.value().unwrap_or_default().into_bigint().to_bits_le()[..length];
        let bits = if cs.is_none() {
            Vec::new_constant(cs, bits)?
        } else {
            Vec::new_witness(cs, || Ok(bits))?
        };

        Boolean::le_bits_to_fp_var(&bits)?.enforce_equal(x)?;

        Ok(bits)
    }

    pub fn add_no_reduce(&self, other: &Self) -> Self {
        let mut z = vec![LimbVar::zero(); max(self.0.len(), other.0.len())];
        for i in 0..self.0.len() {
            z[i] = z[i].add(&self.0[i]).unwrap();
        }
        for i in 0..other.0.len() {
            z[i] = z[i].add(&other.0[i]).unwrap();
        }
        Self(z)
    }

    pub fn mul_no_reduce(&self, other: &Self) -> Result<Self, SynthesisError> {
        let len = self.0.len() + other.0.len() - 1;
        if self.is_constant() || other.is_constant() {
            let mut z = vec![LimbVar::zero(); len];
            for i in 0..self.0.len() {
                for j in 0..other.0.len() {
                    z[i + j] = z[i + j].add(&self.0[i].mul(&other.0[j]).unwrap()).unwrap();
                }
            }
            return Ok(Self(z));
        }
        let cs = self.cs().or(other.cs());
        let mode = if cs.is_none() {
            AllocationMode::Constant
        } else {
            AllocationMode::Witness
        };

        let z = {
            let mut z = vec![(F::zero(), BigUint::zero()); len];
            for i in 0..self.0.len() {
                for j in 0..other.0.len() {
                    z[i + j].0 += self.0[i].value().unwrap_or_default()
                        * other.0[j].value().unwrap_or_default();
                    z[i + j].1 += &self.0[i].ub * &other.0[j].ub;
                }
            }
            z.into_iter()
                .map(|(v, ub)| {
                    Ok(LimbVar {
                        v: FpVar::new_variable(cs.clone(), || Ok(v), mode)?,
                        ub,
                    })
                })
                .collect::<Result<Vec<_>, _>>()?
        };
        for c in 1..=len {
            let mut l = FpVar::<F>::zero();
            let mut r = FpVar::<F>::zero();
            let mut o = FpVar::<F>::zero();
            let mut t = F::one();
            for i in 0..len {
                if i < self.0.len() {
                    l += &self.0[i].v * t;
                }
                if i < other.0.len() {
                    r += &other.0[i].v * t;
                }
                o += &z[i].v * t;
                t *= F::from(c as u64);
            }
            l.mul_equals(&r, &o)?;
        }

        Ok(Self(z))
    }

    pub fn reduce<M: PrimeField>(&self) -> Result<Self, SynthesisError> {
        let cs = self.cs();
        let mode = if cs.is_none() {
            AllocationMode::Constant
        } else {
            AllocationMode::Witness
        };
        let m: BigUint = M::MODULUS.into();
        let (q, r) = {
            let v = self.value().unwrap_or_default();
            let (q, r) = v.div_rem(&m);
            let q_ubound = self.ubound().div_ceil(&m);
            let r_ubound = &m;
            (
                Self::new_variable(
                    cs.clone(),
                    || Ok(BoundedBigUint(q, q_ubound.bits() as usize)),
                    mode,
                )?,
                Self::new_variable(
                    cs.clone(),
                    || Ok(BoundedBigUint(r, r_ubound.bits() as usize)),
                    mode,
                )?,
            )
        };

        q.mul_no_reduce(&Self::new_constant(
            cs.clone(),
            BoundedBigUint(m, M::MODULUS_BIT_SIZE as usize),
        )?)?
        .add_no_reduce(&r)
        .enforce_equal_unaligned(&self)?;

        Ok(r)
    }

    pub fn enforce_congruent<M: PrimeField>(&self, other: &Self) -> Result<(), SynthesisError> {
        let cs = self.cs();
        let mode = if cs.is_none() {
            AllocationMode::Constant
        } else {
            AllocationMode::Witness
        };
        let m: BigUint = M::MODULUS.into();
        let bits = (max(self.ubound(), other.ubound()) / &m).bits() as usize;
        let (d, b) = {
            let x = self.value().unwrap_or_default();
            let y = other.value().unwrap_or_default();
            let (d, b) = if x > y {
                ((x - y) / &m, true)
            } else {
                ((y - x) / &m, false)
            };
            (
                Self::new_variable(cs.clone(), || Ok(BoundedBigUint(d, bits)), mode)?,
                Boolean::new_variable(cs.clone(), || Ok(b), mode)?,
            )
        };

        let zero = Self::new_constant(cs.clone(), BoundedBigUint(BigUint::zero(), bits))?;
        let m = Self::new_constant(cs.clone(), BoundedBigUint(m, M::MODULUS_BIT_SIZE as usize))?;
        let l = self.add_no_reduce(&b.select(&zero, &d)?.mul_no_reduce(&m)?);
        let r = other.add_no_reduce(&b.select(&d, &zero)?.mul_no_reduce(&m)?);
        l.enforce_equal_unaligned(&r)
    }
}

impl<F: PrimeField, B: AsRef<[Boolean<F>]>> From<B> for NonNativeUintVar<F> {
    fn from(bits: B) -> Self {
        Self(
            bits.as_ref()
                .chunks(Self::bits_per_limb())
                .map(LimbVar::from)
                .collect::<Vec<_>>(),
        )
    }
}

/// The out-circuit counterpart of `NonNativeUintVar::to_constraint_field`
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

    limbs
}
