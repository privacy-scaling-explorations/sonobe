use ark_ff::PrimeField;
use ark_r1cs_std::fields::fp::{AllocatedFp, FpVar};
use ark_relations::r1cs::{ConstraintSystem, ConstraintSystemRef, SynthesisError, Variable};
use ark_std::{
    any::{Any, TypeId},
    collections::{BTreeMap, HashMap},
};

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

    /// Gadget for computing the vector of multiplicities $(m_1, ..., m_M)$,
    /// where $m_j$ is the number of times $t_j$ appears in the queries
    /// $(q_1, ..., q_N)$.
    ///
    /// The multiplicities are allocated as witness variables and stored in the
    /// cache map of arkworks' constraint system.
    fn finalize_lookup(&self) -> Result<(), SynthesisError>;
}

impl<F: PrimeField> LookupConstraintSystem<F> for ConstraintSystemRef<F> {
    fn init_lookup(&self, table: Vec<F>) -> Result<(), SynthesisError> {
        let cs = self.borrow_mut().ok_or(SynthesisError::MissingCS)?;

        let mut cache = cs.cache_map.borrow_mut();
        cache.insert(TypeId::of::<LookupTable>(), Box::new(table));
        cache.insert(TypeId::of::<Query>(), Box::new(Vec::<usize>::new()));

        Ok(())
    }

    fn new_query_variable<Func>(&self, f: Func) -> Result<Variable, SynthesisError>
    where
        Func: FnOnce() -> Result<F, SynthesisError>,
    {
        let mut cs = self.borrow_mut().ok_or(SynthesisError::MissingCS)?;
        let index = cs.num_witness_variables;

        let query = cs.new_witness_variable(f)?;

        let mut cache = cs.cache_map.borrow_mut();
        let queries = cache
            .get_mut_as::<Query, Vec<usize>>()
            .ok_or(SynthesisError::AssignmentMissing)?;
        // `index` is the inner value of the query variable, i.e.,
        // `query = Variable::Witness(index)`
        queries.push(index);

        Ok(query)
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

    fn finalize_lookup(&self) -> Result<(), SynthesisError> {
        let mut cs = self.borrow_mut().ok_or(SynthesisError::MissingCS)?;

        // Wrapped in a block to make the borrow checker happy.
        let multiplicity_values = {
            let cache = cs.cache_map.borrow();
            let table = match cache.get_as::<LookupTable, Vec<F>>() {
                Some(table) => table,
                None => return Ok(()),
            };
            let mut histo = table
                .iter()
                .map(|&entry| (entry, 0u64))
                .collect::<HashMap<_, _>>();
            let queries = cache
                .get_as::<Query, Vec<usize>>()
                .ok_or(SynthesisError::AssignmentMissing)?;

            if !cs.is_in_setup_mode() {
                for &query in queries {
                    histo
                        .get_mut(&cs.witness_assignment[query])
                        .map(|c| *c += 1)
                        .ok_or(SynthesisError::AssignmentMissing)?;
                }
            };

            table
                .iter()
                .map(|entry| F::from(histo[entry]))
                .collect::<Vec<_>>()
        };
        let multiplicity_variables = (0..multiplicity_values.len())
            .map(|i| cs.num_witness_variables + i)
            .collect::<Vec<_>>();
        cs.num_witness_variables += multiplicity_values.len();

        if !cs.is_in_setup_mode() {
            cs.witness_assignment.extend(multiplicity_values);
        }

        let mut cache = cs.cache_map.borrow_mut();
        cache.insert(
            TypeId::of::<Multiplicity>(),
            Box::new(multiplicity_variables),
        );

        Ok(())
    }
}

pub trait CommitAndProveConstraintSystem<F: PrimeField> {
    fn init_commit_and_prove(&mut self) -> Result<(), SynthesisError>;

    fn new_committed_variable<Func>(&mut self, f: Func) -> Result<Variable, SynthesisError>
    where
        Func: FnOnce() -> Result<F, SynthesisError>;
}

impl<F: PrimeField> CommitAndProveConstraintSystem<F> for ConstraintSystemRef<F> {
    fn init_commit_and_prove(&mut self) -> Result<(), SynthesisError> {
        let cs = self.borrow_mut().ok_or(SynthesisError::MissingCS)?;

        let mut cache = cs.cache_map.borrow_mut();
        cache.insert(TypeId::of::<Committed>(), Box::new(Vec::<usize>::new()));

        Ok(())
    }

    fn new_committed_variable<Func>(&mut self, f: Func) -> Result<Variable, SynthesisError>
    where
        Func: FnOnce() -> Result<F, SynthesisError>,
    {
        let mut cs = self.borrow_mut().ok_or(SynthesisError::MissingCS)?;
        let index = cs.num_instance_variables;

        let committed = cs.new_input_variable(f)?;

        let mut cache = cs.cache_map.borrow_mut();
        let committed_variables = cache
            .get_mut_as::<Committed, Vec<usize>>()
            .ok_or(SynthesisError::AssignmentMissing)?;
        // `index` is the inner value of the committed variable, i.e.,
        // `committed = Variable::Instance(index)`
        committed_variables.push(index);

        Ok(committed)
    }
}

pub trait ConstraintSystemStatistics {
    fn num_variables_of_type<T: 'static>(&self) -> usize;

    fn has_variables_of_type<T: 'static>(&self) -> bool {
        self.num_variables_of_type::<T>() > 0
    }
}

impl<F: PrimeField> ConstraintSystemStatistics for ConstraintSystem<F> {
    fn num_variables_of_type<T: 'static>(&self) -> usize {
        let cache = self.cache_map.borrow();
        if let Some(vec) = cache.get_as::<T, Vec<usize>>() {
            vec.len()
        } else {
            0
        }
    }
}

impl<F: PrimeField> ConstraintSystemStatistics for ConstraintSystemRef<F> {
    fn num_variables_of_type<T: 'static>(&self) -> usize {
        let cs = self.borrow().unwrap();
        cs.num_variables_of_type::<T>()
    }
}
