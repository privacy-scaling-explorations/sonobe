use ark_ff::PrimeField;
use ark_r1cs_std::fields::fp::{AllocatedFp, FpVar};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError, Variable};
use ark_std::{any::Any, any::TypeId, collections::BTreeMap};

pub trait ArkCacheCast {
    fn get_as<T: 'static, R: 'static>(&self) -> Option<&R>;

    fn get_mut_as<T: 'static, R: 'static>(&mut self) -> Option<&mut R>;
}

impl ArkCacheCast for BTreeMap<TypeId, Box<dyn Any>> {
    fn get_as<T: 'static, R: 'static>(&self) -> Option<&R> {
        self.get(&TypeId::of::<T>())?.downcast_ref::<R>()
    }

    fn get_mut_as<T: 'static, R: 'static>(&mut self) -> Option<&mut R> {
        self.get_mut(&TypeId::of::<T>())?.downcast_mut::<R>()
    }
}

pub struct Query;
pub struct LookupTable;
pub struct Committed;
pub struct Multiplicity;

pub trait LookupConstraintSystem<F: PrimeField> {
    fn init_lookup(&self, table: Vec<F>) -> Result<(), SynthesisError>;

    fn new_query_variable<Func>(&self, f: Func) -> Result<Variable, SynthesisError>
    where
        Func: FnOnce() -> Result<F, SynthesisError>;

    fn new_query_fp<Func>(&self, f: Func) -> Result<FpVar<F>, SynthesisError>
    where
        Func: FnOnce() -> Result<F, SynthesisError>;
}

impl<F: PrimeField> LookupConstraintSystem<F> for ConstraintSystemRef<F> {
    fn init_lookup(&self, table: Vec<F>) -> Result<(), SynthesisError> {
        let cs = self.borrow_mut().ok_or(SynthesisError::MissingCS)?;

        let mut cache = cs.cache_map.borrow_mut();
        cache.insert(TypeId::of::<LookupTable>(), Box::new(table));
        cache.insert(TypeId::of::<Query>(), Box::new(Vec::<Variable>::new()));

        Ok(())
    }

    fn new_query_variable<Func>(&self, f: Func) -> Result<Variable, SynthesisError>
    where
        Func: FnOnce() -> Result<F, SynthesisError>,
    {
        let mut cs = self.borrow_mut().ok_or(SynthesisError::MissingCS)?;

        let variable = cs.new_witness_variable(f)?;

        let mut cache = cs.cache_map.borrow_mut();
        let queries = cache
            .get_mut_as::<Query, Vec<Variable>>()
            .ok_or(SynthesisError::AssignmentMissing)?;
        queries.push(variable);

        Ok(variable)
    }

    fn new_query_fp<Func>(&self, f: Func) -> Result<FpVar<F>, SynthesisError>
    where
        Func: FnOnce() -> Result<F, SynthesisError>,
    {
        let mut value = None;
        let value_generator = || {
            use ark_std::borrow::Borrow;
            value = Some(*f()?.borrow());
            value.ok_or(SynthesisError::AssignmentMissing)
        };
        let variable = self.new_query_variable(value_generator)?;
        Ok(FpVar::Var(AllocatedFp::new(value, variable, self.clone())))
    }
}

pub trait CommitAndProveConstraintSystem<F: PrimeField> {
    fn init_commit_and_prove(&mut self) -> Result<(), SynthesisError>;

    fn new_committed_variable<Func>(&mut self, f: Func) -> Result<Variable, SynthesisError>
    where
        Func: FnOnce() -> Result<F, SynthesisError>;

    fn num_committed_variables(&self) -> usize;
}

impl<F: PrimeField> CommitAndProveConstraintSystem<F> for ConstraintSystemRef<F> {
    fn init_commit_and_prove(&mut self) -> Result<(), SynthesisError> {
        let cs = self.borrow_mut().ok_or(SynthesisError::MissingCS)?;

        let mut cache = cs.cache_map.borrow_mut();
        cache.insert(TypeId::of::<Committed>(), Box::new(Vec::<Variable>::new()));

        Ok(())
    }

    fn new_committed_variable<Func>(&mut self, f: Func) -> Result<Variable, SynthesisError>
    where
        Func: FnOnce() -> Result<F, SynthesisError>,
    {
        let mut cs = self.borrow_mut().ok_or(SynthesisError::MissingCS)?;

        let variable = cs.new_input_variable(f)?;

        let mut cache = cs.cache_map.borrow_mut();
        let committed = cache
            .get_mut(&TypeId::of::<Committed>())
            .ok_or(SynthesisError::AssignmentMissing)?
            .downcast_mut::<Vec<Variable>>()
            .ok_or(SynthesisError::AssignmentMissing)?;
        committed.push(variable);

        Ok(variable)
    }

    fn num_committed_variables(&self) -> usize {
        let cs = self.borrow().unwrap();

        let cache = cs.cache_map.borrow();
        let committed = cache
            .get(&TypeId::of::<Committed>())
            .unwrap()
            .downcast_ref::<Vec<Variable>>()
            .unwrap();
        committed.len()
    }
}
