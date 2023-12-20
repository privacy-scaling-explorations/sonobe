use ark_ff::PrimeField;
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    fields::FieldVar,
};
use ark_relations::r1cs::{Namespace, SynthesisError};
use core::{borrow::Borrow, marker::PhantomData};

use crate::ccs::r1cs::R1CS;
use crate::utils::vec::SparseMatrix;

#[derive(Debug, Clone)]
pub struct RelaxedR1CSGadget<F: PrimeField, CF: PrimeField, FV: FieldVar<F, CF>> {
    _f: PhantomData<F>,
    _cf: PhantomData<CF>,
    _fv: PhantomData<FV>,
}
impl<F: PrimeField, CF: PrimeField, FV: FieldVar<F, CF>> RelaxedR1CSGadget<F, CF, FV> {
    /// performs the RelaxedR1CS check (Az∘Bz==uCz+E)
    pub fn check(
        r1cs: R1CSVar<F, CF, FV>,
        E: Vec<FV>,
        u: FV,
        z: Vec<FV>,
    ) -> Result<(), SynthesisError> {
        let Az = mat_vec_mul_sparse(r1cs.A, z.clone());
        let Bz = mat_vec_mul_sparse(r1cs.B, z.clone());
        let Cz = mat_vec_mul_sparse(r1cs.C, z.clone());
        let uCz = vec_scalar_mul(&Cz, &u);
        let uCzE = vec_add(&uCz, &E)?;
        let AzBz = hadamard(&Az, &Bz)?;
        for i in 0..AzBz.len() {
            AzBz[i].enforce_equal(&uCzE[i].clone())?;
        }
        Ok(())
    }
}

fn mat_vec_mul_sparse<F: PrimeField, CF: PrimeField, FV: FieldVar<F, CF>>(
    m: SparseMatrixVar<F, CF, FV>,
    v: Vec<FV>,
) -> Vec<FV> {
    let mut res = vec![FV::zero(); m.n_rows];
    for (row_i, row) in m.coeffs.iter().enumerate() {
        for (value, col_i) in row.iter() {
            res[row_i] += value.clone().mul(&v[*col_i].clone());
        }
    }
    res
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

#[derive(Debug, Clone)]
pub struct R1CSVar<F: PrimeField, CF: PrimeField, FV: FieldVar<F, CF>> {
    _f: PhantomData<F>,
    _cf: PhantomData<CF>,
    _fv: PhantomData<FV>,
    pub A: SparseMatrixVar<F, CF, FV>,
    pub B: SparseMatrixVar<F, CF, FV>,
    pub C: SparseMatrixVar<F, CF, FV>,
}

impl<F, CF, FV> AllocVar<R1CS<F>, CF> for R1CSVar<F, CF, FV>
where
    F: PrimeField,
    CF: PrimeField,
    FV: FieldVar<F, CF>,
{
    fn new_variable<T: Borrow<R1CS<F>>>(
        cs: impl Into<Namespace<CF>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        _mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|val| {
            let cs = cs.into();

            let A = SparseMatrixVar::<F, CF, FV>::new_constant(cs.clone(), &val.borrow().A)?;
            let B = SparseMatrixVar::<F, CF, FV>::new_constant(cs.clone(), &val.borrow().B)?;
            let C = SparseMatrixVar::<F, CF, FV>::new_constant(cs.clone(), &val.borrow().C)?;

            Ok(Self {
                _f: PhantomData,
                _cf: PhantomData,
                _fv: PhantomData,
                A,
                B,
                C,
            })
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_crypto_primitives::crh::{
        sha256::{
            constraints::{Sha256Gadget, UnitVar},
            Sha256,
        },
        CRHScheme, CRHSchemeGadget,
    };
    use ark_ff::BigInteger;
    use ark_pallas::{Fq, Fr};
    use ark_r1cs_std::{
        alloc::AllocVar,
        bits::uint8::UInt8,
        eq::EqGadget,
        fields::{fp::FpVar, nonnative::NonNativeFieldVar},
    };
    use ark_relations::r1cs::{
        ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, SynthesisError,
    };
    use ark_std::One;

    use crate::ccs::r1cs::{
        tests::{get_test_r1cs, get_test_z},
        R1CS,
    };
    use crate::frontend::arkworks::{extract_r1cs_and_z, tests::TestCircuit};

    #[test]
    fn test_relaxed_r1cs_small_gadget_handcrafted() {
        let r1cs: R1CS<Fr> = get_test_r1cs();
        let rel_r1cs = r1cs.clone().relax();
        let z = get_test_z(3);

        let cs = ConstraintSystem::<Fr>::new_ref();

        let zVar = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(z)).unwrap();
        let EVar = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(rel_r1cs.E)).unwrap();
        let uVar = FpVar::<Fr>::new_witness(cs.clone(), || Ok(rel_r1cs.u)).unwrap();
        let r1csVar = R1CSVar::<Fr, Fr, FpVar<Fr>>::new_witness(cs.clone(), || Ok(r1cs)).unwrap();

        RelaxedR1CSGadget::<Fr, Fr, FpVar<Fr>>::check(r1csVar, EVar, uVar, zVar).unwrap();
        assert!(cs.is_satisfied().unwrap());
    }

    // gets as input a circuit that implements the ConstraintSynthesizer trait, and that has been
    // initialized.
    fn test_relaxed_r1cs_gadget<CS: ConstraintSynthesizer<Fr>>(circuit: CS) {
        let cs = ConstraintSystem::<Fr>::new_ref();

        circuit.generate_constraints(cs.clone()).unwrap();
        cs.finalize();
        assert!(cs.is_satisfied().unwrap());

        let cs = cs.into_inner().unwrap();

        let (r1cs, z) = extract_r1cs_and_z::<Fr>(&cs);
        r1cs.check_relation(&z).unwrap();

        let relaxed_r1cs = r1cs.clone().relax();
        relaxed_r1cs.check_relation(&z).unwrap();

        // set new CS for the circuit that checks the RelaxedR1CS of our original circuit
        let cs = ConstraintSystem::<Fr>::new_ref();
        // prepare the inputs for our circuit
        let zVar = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(z)).unwrap();
        let EVar = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(relaxed_r1cs.E)).unwrap();
        let uVar = FpVar::<Fr>::new_witness(cs.clone(), || Ok(relaxed_r1cs.u)).unwrap();
        let r1csVar = R1CSVar::<Fr, Fr, FpVar<Fr>>::new_witness(cs.clone(), || Ok(r1cs)).unwrap();

        RelaxedR1CSGadget::<Fr, Fr, FpVar<Fr>>::check(r1csVar, EVar, uVar, zVar).unwrap();
        assert!(cs.is_satisfied().unwrap());
    }

    #[test]
    fn test_relaxed_r1cs_small_gadget_arkworks() {
        let x = Fr::from(5_u32);
        let y = x * x * x + x + Fr::from(5_u32);
        let circuit = TestCircuit::<Fr> { x, y };
        test_relaxed_r1cs_gadget(circuit);
    }

    struct Sha256TestCircuit<F: PrimeField> {
        _f: PhantomData<F>,
        pub x: Vec<u8>,
        pub y: Vec<u8>,
    }
    impl<F: PrimeField> ConstraintSynthesizer<F> for Sha256TestCircuit<F> {
        fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
            let x = Vec::<UInt8<F>>::new_witness(cs.clone(), || Ok(self.x))?;
            let y = Vec::<UInt8<F>>::new_input(cs.clone(), || Ok(self.y))?;

            let unitVar = UnitVar::default();
            let comp_y = <Sha256Gadget<F> as CRHSchemeGadget<Sha256, F>>::evaluate(&unitVar, &x)?;
            comp_y.0.enforce_equal(&y)?;
            Ok(())
        }
    }
    #[test]
    fn test_relaxed_r1cs_medium_gadget_arkworks() {
        let x = Fr::from(5_u32).into_bigint().to_bytes_le();
        let y = <Sha256 as CRHScheme>::evaluate(&(), x.clone()).unwrap();

        let circuit = Sha256TestCircuit::<Fr> {
            _f: PhantomData,
            x,
            y,
        };
        test_relaxed_r1cs_gadget(circuit);
    }

    // circuit that has the number of constraints specified in the `n_constraints` parameter. Note
    // that the generated circuit will have very sparse matrices, so the resulting constraints
    // number of the RelaxedR1CS gadget must take that into account.
    struct CustomTestCircuit<F: PrimeField> {
        _f: PhantomData<F>,
        pub n_constraints: usize,
        pub x: F,
        pub y: F,
    }
    impl<F: PrimeField> CustomTestCircuit<F> {
        fn new(n_constraints: usize) -> Self {
            let x = F::from(5_u32);
            let mut y = F::one();
            for _ in 0..n_constraints - 1 {
                y *= x;
            }
            Self {
                _f: PhantomData,
                n_constraints,
                x,
                y,
            }
        }
    }
    impl<F: PrimeField> ConstraintSynthesizer<F> for CustomTestCircuit<F> {
        fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
            let x = FpVar::<F>::new_witness(cs.clone(), || Ok(self.x))?;
            let y = FpVar::<F>::new_input(cs.clone(), || Ok(self.y))?;

            let mut comp_y = FpVar::<F>::new_witness(cs.clone(), || Ok(F::one()))?;
            for _ in 0..self.n_constraints - 1 {
                comp_y *= x.clone();
            }

            comp_y.enforce_equal(&y)?;
            Ok(())
        }
    }

    #[test]
    fn test_relaxed_r1cs_custom_circuit() {
        let n_constraints = 10_000;
        let x = Fr::from(5_u32);
        let mut y = Fr::one();
        for _ in 0..n_constraints - 1 {
            y *= x;
        }

        let circuit = CustomTestCircuit::<Fr> {
            _f: PhantomData,
            n_constraints,
            x,
            y,
        };
        test_relaxed_r1cs_gadget(circuit);
    }

    #[test]
    fn test_relaxed_r1cs_nonnative_circuit() {
        let cs = ConstraintSystem::<Fq>::new_ref();
        // in practice we would use CycleFoldCircuit, but is a very big circuit (when computed
        // non-natively inside the RelaxedR1CS circuit), so in order to have a short test we use a
        // custom circuit.
        let circuit = CustomTestCircuit::<Fq>::new(10);
        circuit.generate_constraints(cs.clone()).unwrap();
        cs.finalize();
        let cs = cs.into_inner().unwrap();
        let (r1cs, z) = extract_r1cs_and_z::<Fq>(&cs);

        let relaxed_r1cs = r1cs.clone().relax();

        // natively
        let cs = ConstraintSystem::<Fq>::new_ref();
        let zVar = Vec::<FpVar<Fq>>::new_witness(cs.clone(), || Ok(z.clone())).unwrap();
        let EVar =
            Vec::<FpVar<Fq>>::new_witness(cs.clone(), || Ok(relaxed_r1cs.clone().E)).unwrap();
        let uVar = FpVar::<Fq>::new_witness(cs.clone(), || Ok(relaxed_r1cs.u)).unwrap();
        let r1csVar =
            R1CSVar::<Fq, Fq, FpVar<Fq>>::new_witness(cs.clone(), || Ok(r1cs.clone())).unwrap();
        RelaxedR1CSGadget::<Fq, Fq, FpVar<Fq>>::check(r1csVar, EVar, uVar, zVar).unwrap();

        // non-natively
        let cs = ConstraintSystem::<Fr>::new_ref();
        let zVar = Vec::<NonNativeFieldVar<Fq, Fr>>::new_witness(cs.clone(), || Ok(z)).unwrap();
        let EVar = Vec::<NonNativeFieldVar<Fq, Fr>>::new_witness(cs.clone(), || Ok(relaxed_r1cs.E))
            .unwrap();
        let uVar =
            NonNativeFieldVar::<Fq, Fr>::new_witness(cs.clone(), || Ok(relaxed_r1cs.u)).unwrap();
        let r1csVar =
            R1CSVar::<Fq, Fr, NonNativeFieldVar<Fq, Fr>>::new_witness(cs.clone(), || Ok(r1cs))
                .unwrap();
        RelaxedR1CSGadget::<Fq, Fr, NonNativeFieldVar<Fq, Fr>>::check(r1csVar, EVar, uVar, zVar)
            .unwrap();
    }
}
