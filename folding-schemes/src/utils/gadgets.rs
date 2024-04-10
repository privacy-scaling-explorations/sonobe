use ark_ff::PrimeField;
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    fields::{
        nonnative::{NonNativeFieldMulResultVar, NonNativeFieldVar},
        FieldVar,
    },
};
use ark_relations::r1cs::{Namespace, SynthesisError};
use core::{borrow::Borrow, marker::PhantomData};

use crate::utils::vec::SparseMatrix;

pub fn mat_vec_mul_sparse<F: PrimeField, CF: PrimeField, FV: FieldVar<F, CF>>(
    m: SparseMatrixVar<F, CF, FV>,
    v: Vec<FV>,
) -> Vec<FV> {
    let mut res = vec![FV::zero(); m.n_rows];
    for (row_i, row) in m.coeffs.iter().enumerate() {
        for (value, col_i) in row.iter() {
            if value.value().unwrap() == F::one() {
                // no need to multiply by 1
                res[row_i] += v[*col_i].clone();
                continue;
            }
            res[row_i] += value.clone().mul(&v[*col_i].clone());
        }
    }
    res
}
/// An optimized variant of `mat_vec_mul_sparse` for `NonNativeFieldVar`.
/// Use this with caution, as this function assumes that no "overflow" will happen when summing
/// up `NonNativeFieldMulResultVar`s.
/// 
/// The above condition holds for checking `cf_r1cs`, because it has only 1.4k columns, and the
/// upper bound of each limb in the final sum is approx. `1.4k * 2^bits_per_limb * num_limbs`,
/// where `bits_per_limb` and `num_limbs` are reasonably small.
/// For a 254-bit `Fq` and 254-bit `Fr`, `bits_per_limb = 15`, `num_limbs = 17`, and the upper
/// bound is `2^33`, which is by far less than `2^254`.
pub fn nonnative_mat_vec_mul_sparse<F: PrimeField, CF: PrimeField>(
    m: SparseMatrixVar<F, CF, NonNativeFieldVar<F, CF>>,
    v: &[NonNativeFieldVar<F, CF>],
) -> Result<Vec<NonNativeFieldVar<F, CF>>, SynthesisError> {
    let mut res = vec![NonNativeFieldVar::zero(); m.n_rows];
    for (row_i, row) in m.coeffs.iter().enumerate() {
        let mut r = NonNativeFieldMulResultVar::<F, CF>::zero();
        for (value, col_i) in row.iter() {
            r += value.clone().mul_without_reduce(&v[*col_i].clone())?;
        }
        res[row_i] = r.reduce()?;
    }
    Ok(res)
}
pub fn vec_add<F: PrimeField, CF: PrimeField, FV: FieldVar<F, CF>>(
    a: &Vec<FV>,
    b: &Vec<FV>,
) -> Result<Vec<FV>, SynthesisError> {
    if a.len() != b.len() {
        return Err(SynthesisError::Unsatisfiable);
    }
    let mut r: Vec<FV> = vec![FV::zero(); a.len()];
    for i in 0..a.len() {
        r[i] = a[i].clone() + b[i].clone();
    }
    Ok(r)
}
pub fn vec_scalar_mul<F: PrimeField, CF: PrimeField, FV: FieldVar<F, CF>>(
    vec: &Vec<FV>,
    c: &FV,
) -> Vec<FV> {
    let mut result = vec![FV::zero(); vec.len()];
    for (i, a) in vec.iter().enumerate() {
        result[i] = a.clone() * c;
    }
    result
}
pub fn hadamard<F: PrimeField, CF: PrimeField, FV: FieldVar<F, CF>>(
    a: &Vec<FV>,
    b: &Vec<FV>,
) -> Result<Vec<FV>, SynthesisError> {
    if a.len() != b.len() {
        return Err(SynthesisError::Unsatisfiable);
    }
    let mut r: Vec<FV> = vec![FV::zero(); a.len()];
    for i in 0..a.len() {
        r[i] = a[i].clone() * b[i].clone();
    }
    Ok(r)
}

#[derive(Debug, Clone)]
pub struct SparseMatrixVar<F: PrimeField, CF: PrimeField, FV: FieldVar<F, CF>> {
    _f: PhantomData<F>,
    _cf: PhantomData<CF>,
    _fv: PhantomData<FV>,
    pub n_rows: usize,
    pub n_cols: usize,
    // same format as the native SparseMatrix (which follows ark_relations::r1cs::Matrix format
    pub coeffs: Vec<Vec<(FV, usize)>>,
}

impl<F, CF, FV> AllocVar<SparseMatrix<F>, CF> for SparseMatrixVar<F, CF, FV>
where
    F: PrimeField,
    CF: PrimeField,
    FV: FieldVar<F, CF>,
{
    fn new_variable<T: Borrow<SparseMatrix<F>>>(
        cs: impl Into<Namespace<CF>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|val| {
            let cs = cs.into();

            let mut coeffs: Vec<Vec<(FV, usize)>> = Vec::new();
            for row in val.borrow().coeffs.iter() {
                let mut rowVar: Vec<(FV, usize)> = Vec::new();
                for &(value, col_i) in row.iter() {
                    let coeffVar = FV::new_variable(cs.clone(), || Ok(value), mode)?;
                    rowVar.push((coeffVar, col_i));
                }
                coeffs.push(rowVar);
            }

            Ok(Self {
                _f: PhantomData,
                _cf: PhantomData,
                _fv: PhantomData,
                n_rows: val.borrow().n_rows,
                n_cols: val.borrow().n_cols,
                coeffs,
            })
        })
    }
}
