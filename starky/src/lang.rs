//! STARK Language

/// Constraint
pub trait Constraint<T> {
    /// Asserts that `value == 0`.
    fn assert_zero(&mut self, value: T) -> &mut Self;

    /// Asserts that `lhs == rhs` by subtracting them and calling [`Self::assert_zero`].
    #[inline]
    fn assert_eq(&mut self, lhs: T, rhs: T) -> &mut Self
    where
        Self: Sub<T>,
    {
        let diff = self.sub(lhs, rhs);
        self.assert_zero(diff)
    }

    /// Asserts that `value == 1`.
    #[inline]
    fn assert_one(&mut self, value: T) -> &mut Self
    where
        Self: Sub<T> + One<T>,
    {
        let one = self.one();
        self.assert_eq(value, one)
    }
}

impl<T, C> Constraint<T> for &mut C
where
    C: Constraint<T>,
{
    #[inline]
    fn assert_zero(&mut self, value: T) -> &mut Self {
        (**self).assert_zero(value);
        self
    }
}

/// Constraint Filtered
pub trait ConstraintFiltered<T, Filter> {
    /// Asserts that `value == 0` whenever the `filter` is true.
    fn assert_zero_when(&mut self, filter: Filter, value: T) -> &mut Self;

    /// Asserts that `lhs == rhs` whenever the `filter` is true by subtracting them and calling
    /// [`Self::assert_zero_when`].
    #[inline]
    fn assert_eq_when(&mut self, filter: Filter, lhs: T, rhs: T) -> &mut Self
    where
        Self: Sub<T>,
    {
        let diff = self.sub(lhs, rhs);
        self.assert_zero_when(filter, diff)
    }

    /// Asserts that `value == 1` whenever the `filter` is true.
    #[inline]
    fn assert_one_when(&mut self, filter: Filter, value: T) -> &mut Self
    where
        Self: Sub<T> + One<T>,
    {
        let one = self.one();
        self.assert_eq_when(filter, value, one)
    }
}

/// All Rows Filter
pub struct All;

/// Transition Filter
pub struct Transition;

/// First Row Filter
pub struct FirstRow;

/// Last Row Filter
pub struct LastRow;

/// Zero
pub trait Zero<T> {
    /// Returns the additive identity over `T`.
    fn zero(&mut self) -> T;
}

impl<T, C> Zero<T> for &mut C
where
    C: Zero<T>,
{
    #[inline]
    fn zero(&mut self) -> T {
        (**self).zero()
    }
}

/// Addition
pub trait Add<T> {
    /// Adds `lhs` and `rhs` returning their sum.
    fn add(&mut self, lhs: T, rhs: T) -> T;

    ///
    #[inline]
    fn double(&mut self, value: T) -> T
    where
        T: Clone,
    {
        self.add(value.clone(), value)
    }

    /// Computes the sum over `iter`, returning [`Zero::zero`] if `iter` is empty.
    #[inline]
    fn sum<I>(&mut self, iter: I) -> T
    where
        Self: Zero<T>,
        I: IntoIterator<Item = T>,
    {
        iter.into_iter()
            .fold(self.zero(), |lhs, rhs| self.add(lhs, rhs))
    }
}

impl<T, C> Add<T> for &mut C
where
    C: Add<T>,
{
    #[inline]
    fn add(&mut self, lhs: T, rhs: T) -> T {
        (**self).add(lhs, rhs)
    }
}

/// Subtraction
pub trait Sub<T> {
    /// Subtracts `lhs` and `rhs` returning their difference.
    fn sub(&mut self, lhs: T, rhs: T) -> T;
}

impl<T, C> Sub<T> for &mut C
where
    C: Sub<T>,
{
    #[inline]
    fn sub(&mut self, lhs: T, rhs: T) -> T {
        (**self).sub(lhs, rhs)
    }
}

/// One
pub trait One<T> {
    /// Returns the multiplicative identity over `T`.
    fn one(&mut self) -> T;
}

impl<T, C> One<T> for &mut C
where
    C: One<T>,
{
    #[inline]
    fn one(&mut self) -> T {
        (**self).one()
    }
}

/// Multiplication
pub trait Mul<T> {
    /// Multiplies `lhs` and `rhs` returning their product.
    fn mul(&mut self, lhs: T, rhs: T) -> T;

    /// Computes the product over `iter`, returning [`One::one`] if `iter` is empty.
    #[inline]
    fn product<I>(&mut self, iter: I) -> T
    where
        Self: One<T>,
        I: IntoIterator<Item = T>,
    {
        iter.into_iter()
            .fold(self.one(), |lhs, rhs| self.mul(lhs, rhs))
    }
}

impl<T, C> Mul<T> for &mut C
where
    C: Mul<T>,
{
    #[inline]
    fn mul(&mut self, lhs: T, rhs: T) -> T {
        (**self).mul(lhs, rhs)
    }
}

/// Arithmetic over a Field
pub trait Arithmetic<T>: Add<T> + Mul<T> + One<T> + Sub<T> + Zero<T> {
    ///
    #[inline]
    fn two(&mut self) -> T {
        let lhs_one = self.one();
        let rhs_one = self.one();
        self.add(lhs_one, rhs_one)
    }

    ///
    #[inline]
    fn xor(&mut self, lhs: T, rhs: T) -> T
    where
        T: Clone,
    {
        let sum = self.add(lhs.clone(), rhs.clone());
        let product = self.mul(lhs, rhs);
        let double_product = self.double(product);
        self.sub(sum, double_product)
    }
}

impl<T, C> Arithmetic<T> for C where C: Add<T> + Mul<T> + One<T> + Sub<T> + Zero<T> {}

/// IR Assertions
pub trait Assertions<T>: Sized {
    ///
    #[inline]
    fn assert_zero_product(&mut self, lhs: T, rhs: T) -> &mut Self
    where
        Self: Constraint<T> + Mul<T>,
    {
        let product = self.mul(lhs, rhs);
        self.assert_zero(product)
    }

    ///
    #[inline]
    fn assert_boolean(&mut self, value: T) -> &mut Self
    where
        Self: Constraint<T> + Mul<T> + One<T> + Sub<T>,
        T: Clone,
    {
        let one = self.one();
        let one_minus_value = self.sub(one, value.clone());
        self.assert_zero_product(value, one_minus_value)
    }

    ///
    #[inline]
    fn assert_bit_decomposition<B>(&mut self, value: T, bits: B) -> &mut Self
    where
        Self: Add<T> + Constraint<T> + Mul<T> + One<T> + Sub<T> + Zero<T>,
        T: Clone,
        B: IntoIterator<Item = T>,
    {
        let two = self.two();
        let mut addends = vec![];
        let mut shift = self.one();
        for bit in bits {
            self.assert_boolean(bit.clone());
            addends.push(self.mul(shift.clone(), bit));
            shift = self.mul(two.clone(), shift);
        }
        let sum = self.sum(addends);
        self.assert_eq(value, sum)
    }

    ///
    #[inline]
    fn assert_bit_decomposition_with_unchecked_bits<B>(&mut self, value: T, bits: B) -> &mut Self
    where
        Self: Add<T> + Constraint<T> + Mul<T> + One<T> + Sub<T> + Zero<T>,
        T: Clone,
        B: IntoIterator<Item = T>,
    {
        let two = self.two();
        let mut addends = vec![];
        let mut shift = self.one();
        for bit in bits {
            addends.push(self.mul(shift.clone(), bit));
            shift = self.mul(two.clone(), shift);
        }
        let sum = self.sum(addends);
        self.assert_eq(value, sum)
    }

    ///
    #[inline]
    fn assert_zero_transition(&mut self, value: T) -> &mut Self
    where
        Self: ConstraintFiltered<T, Transition>,
    {
        self.assert_zero_when(Transition, value)
    }

    ///
    #[inline]
    fn assert_eq_transition(&mut self, lhs: T, rhs: T) -> &mut Self
    where
        Self: ConstraintFiltered<T, Transition> + Sub<T>,
    {
        self.assert_eq_when(Transition, lhs, rhs)
    }

    ///
    #[inline]
    fn assert_one_transition(&mut self, value: T) -> &mut Self
    where
        Self: ConstraintFiltered<T, Transition> + Sub<T> + One<T>,
    {
        self.assert_one_when(Transition, value)
    }

    ///
    #[inline]
    fn assert_zero_product_transition(&mut self, lhs: T, rhs: T) -> &mut Self
    where
        Self: ConstraintFiltered<T, Transition> + Mul<T>,
    {
        let product = self.mul(lhs, rhs);
        self.assert_zero_transition(product)
    }

    ///
    #[inline]
    fn assert_increments_by(&mut self, curr: T, next: T, step: T) -> &mut Self
    where
        Self: ConstraintFiltered<T, Transition> + Sub<T>,
    {
        let diff = self.sub(next, curr);
        self.assert_eq_transition(diff, step)
    }

    ///
    #[inline]
    fn assert_zero_first_row(&mut self, value: T) -> &mut Self
    where
        Self: ConstraintFiltered<T, FirstRow>,
    {
        self.assert_zero_when(FirstRow, value)
    }

    ///
    #[inline]
    fn assert_eq_first_row(&mut self, lhs: T, rhs: T) -> &mut Self
    where
        Self: ConstraintFiltered<T, FirstRow> + Sub<T>,
    {
        self.assert_eq_when(FirstRow, lhs, rhs)
    }

    ///
    #[inline]
    fn assert_one_first_row(&mut self, value: T) -> &mut Self
    where
        Self: ConstraintFiltered<T, FirstRow> + Sub<T> + One<T>,
    {
        self.assert_one_when(FirstRow, value)
    }

    ///
    #[inline]
    fn assert_zero_last_row(&mut self, value: T) -> &mut Self
    where
        Self: ConstraintFiltered<T, LastRow>,
    {
        self.assert_zero_when(LastRow, value)
    }

    ///
    #[inline]
    fn assert_eq_last_row(&mut self, lhs: T, rhs: T) -> &mut Self
    where
        Self: ConstraintFiltered<T, LastRow> + Sub<T>,
    {
        self.assert_eq_when(LastRow, lhs, rhs)
    }

    ///
    #[inline]
    fn assert_one_last_row(&mut self, value: T) -> &mut Self
    where
        Self: ConstraintFiltered<T, LastRow> + Sub<T> + One<T>,
    {
        self.assert_one_when(LastRow, value)
    }

    ///
    #[inline]
    fn assert_all_zero<I>(&mut self, iter: I) -> &mut Self
    where
        Self: Constraint<T>,
        I: IntoIterator<Item = T>,
    {
        for item in iter {
            self.assert_zero(item);
        }
        self
    }

    ///
    #[inline]
    fn assert_valid_zero_check(&mut self, is_zero: T, value: T, inverse: T) -> &mut Self
    where
        Self: Constraint<T> + Mul<T> + One<T> + Sub<T>,
        T: Clone,
    {
        let prod = self.mul(value.clone(), inverse.clone());
        self.when(is_zero)
            .assert_zero(value)
            .assert_zero(inverse)
            .otherwise()
            .assert_one(prod);
        self
    }

    ///
    #[inline]
    fn when(&mut self, condition: T) -> Branch<T, Self> {
        Branch {
            condition,
            compiler: self,
        }
    }

    ///
    #[inline]
    fn when_all<I>(&mut self, conditions: I) -> Branch<T, Self>
    where
        Self: Mul<T> + One<T>,
        I: IntoIterator<Item = T>,
    {
        let condition = self.product(conditions);
        self.when(condition)
    }
}

impl<T, COM> Assertions<T> for COM {}

/// Branching Compiler
pub struct Branch<'c, T, COM> {
    /// Condition
    condition: T,

    /// Base Compiler
    compiler: &'c mut COM,
}

impl<'c, T, COM> Branch<'c, T, COM> {
    ///
    #[inline]
    pub fn otherwise(&mut self) -> &mut Self
    where
        T: Clone,
        COM: Sub<T> + One<T>,
    {
        let one = self.compiler.one();
        self.condition = self.compiler.sub(one, self.condition.clone());
        self
    }
}

impl<'c, T, COM> Add<T> for Branch<'c, T, COM>
where
    COM: Add<T>,
{
    #[inline]
    fn add(&mut self, lhs: T, rhs: T) -> T {
        self.compiler.add(lhs, rhs)
    }
}

impl<'c, T, COM> Sub<T> for Branch<'c, T, COM>
where
    COM: Sub<T>,
{
    #[inline]
    fn sub(&mut self, lhs: T, rhs: T) -> T {
        self.compiler.sub(lhs, rhs)
    }
}

impl<'c, T, COM> Zero<T> for Branch<'c, T, COM>
where
    COM: Zero<T>,
{
    #[inline]
    fn zero(&mut self) -> T {
        self.compiler.zero()
    }
}

impl<'c, T, COM> Mul<T> for Branch<'c, T, COM>
where
    COM: Mul<T>,
{
    #[inline]
    fn mul(&mut self, lhs: T, rhs: T) -> T {
        self.compiler.mul(lhs, rhs)
    }
}

impl<'c, T, COM> One<T> for Branch<'c, T, COM>
where
    COM: One<T>,
{
    #[inline]
    fn one(&mut self) -> T {
        self.compiler.one()
    }
}

impl<'c, T, COM> Constraint<T> for Branch<'c, T, COM>
where
    T: Clone,
    COM: Constraint<T> + Mul<T>,
{
    #[inline]
    fn assert_zero(&mut self, value: T) -> &mut Self {
        let filtered_value = self.compiler.mul(self.condition.clone(), value);
        self.compiler.assert_zero(filtered_value);
        self
    }
}

impl<'c, T, Filter, COM> ConstraintFiltered<T, Filter> for Branch<'c, T, COM>
where
    T: Clone,
    COM: ConstraintFiltered<T, Filter> + Mul<T>,
{
    #[inline]
    fn assert_zero_when(&mut self, filter: Filter, value: T) -> &mut Self {
        let filtered_value = self.compiler.mul(self.condition.clone(), value);
        self.compiler.assert_zero_when(filter, filtered_value);
        self
    }
}

///
pub trait Variable<COM = ()>
where
    COM: ?Sized,
{
    ///
    fn create(compiler: &mut COM) -> Self;
}

///
pub trait Allocator {
    ///
    #[inline]
    fn allocate<V>(&mut self) -> V
    where
        V: Variable<Self>,
    {
        V::create(self)
    }

    ///
    #[inline]
    fn allocate_vec<V>(&mut self, len: usize) -> Vec<V>
    where
        V: Variable<Self>,
    {
        (0..len).map(|_| V::create(self)).collect()
    }
}

impl<COM> Allocator for COM where COM: ?Sized {}

/// Executor
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Executor<T> {
    /// Flattened Column Data
    ///
    /// Each section of the vector is formatted as
    /// ```
    /// [ ... x1.curr x1.next x2.curr x2.next ... ]
    /// ```
    /// and the location of the sections is given by the `column_starting_indices` vector, storing
    /// the machines contiguously.
    flattened_columns: Vec<T>,

    /// Machine Column Data Starting Indices
    column_starting_indices: Vec<usize>,

    /// Flattened Public Inputs
    ///
    /// Each section of the vector is a flat extension of the public inputs for a given machine.
    /// The locations of the sections is given by the `public_input_starting_indices` vector,
    /// storing the machines contiguously.
    flattened_public_inputs: Vec<T>,

    /// Machine Public Input Starting Indices
    public_input_starting_indices: Vec<usize>,

    /// Intermediate Values
    ///
    /// This is a flat map from indices to values which can represent any intermediate values
    /// coming from any machine.
    intermediate_values: Vec<T>,
}

impl<T> Executor<T> {
    /// Builds an [`Executor`] over the machine `data` where each item in the iterator is the
    /// vector of current-row columns, the vector of next-row columns, and the vector of public
    /// inputs respectively.
    #[inline]
    pub fn new<I>(data: I) -> Self
    where
        I: IntoIterator<Item = (Vec<T>, Vec<T>, Vec<T>)>,
    {
        let mut flattened_columns = vec![];
        let mut column_starting_indices = vec![];
        let mut flattened_public_inputs = vec![];
        let mut public_input_starting_indices = vec![];
        for (curr, next, mut public_inputs) in data {
            assert_eq!(
                curr.len(),
                next.len(),
                "Current row and next row must have the same number of columns."
            );
            column_starting_indices.push(flattened_columns.len());
            public_input_starting_indices.push(flattened_public_inputs.len());
            for (curr, next) in curr.into_iter().zip(next) {
                flattened_columns.push(curr);
                flattened_columns.push(next);
            }
            flattened_public_inputs.append(&mut public_inputs);
        }
        Self {
            flattened_columns,
            column_starting_indices,
            flattened_public_inputs,
            public_input_starting_indices,
            intermediate_values: vec![],
        }
    }

    /// Returns the columns slice (interleaving current and next rows) for the given `index`.
    #[inline]
    fn columns(&self, index: MachineIndex) -> Option<&[T]> {
        let start = *self.column_starting_indices.get(index.0)?;
        Some(match self.column_starting_indices.get(index.0 + 1) {
            Some(last) => &self.flattened_columns[start..*last],
            _ => &self.flattened_columns[start..],
        })
    }

    /// Returns the public inputs slice for the given `index`.
    #[inline]
    fn public_inputs(&self, index: MachineIndex) -> Option<&[T]> {
        let start = *self.public_input_starting_indices.get(index.0)?;
        Some(match self.public_input_starting_indices.get(index.0 + 1) {
            Some(last) => &self.flattened_public_inputs[start..*last],
            _ => &self.flattened_public_inputs[start..],
        })
    }

    /// Returns the value of `variable` if it exists in the executor.
    #[inline]
    pub fn value_of(&self, variable: Var) -> Option<&T> {
        match variable.0 {
            VarData::ColumnVariable { column, row_shift } => {
                // NOTE: We only support a stride of 2 right now.
                assert!(row_shift < 2, "Only current and next rows are supported!");
                self.columns(column.machine)?
                    .get(2 * column.index.0 + row_shift)
            }
            VarData::PublicInput(index) => self.public_inputs(index.machine)?.get(index.index.0),
            VarData::IntermediateVariable(index) => self.intermediate_values.get(index),
        }
    }

    /// Executes the function `f` over the values of the incoming `variables`. If any of the
    /// variables has no assigned value, an `Err` is returned with the unknown variable.
    #[inline]
    pub fn execute<F, const N: usize, Output>(
        &mut self,
        variables: &[Var; N],
        f: F,
    ) -> Result<Output, Var>
    where
        F: FnOnce([&T; N]) -> Output,
    {
        let mut values = vec![];
        for var in variables {
            if let Some(value) = self.value_of(*var) {
                values.push(value);
            } else {
                return Err(*var);
            }
        }
        Ok(f(values.try_into().ok().expect(
            "The value slice and variable slice are guaranteed to have the same size",
        )))
    }

    /// Executes the binary operation `f` over the `lhs` and `rhs` values.
    ///
    /// See the [`execute`](Self::execute) method for more details.
    #[inline]
    pub fn execute_binary_op<F, Output>(&mut self, lhs: Var, rhs: Var, f: F) -> Result<Output, Var>
    where
        F: FnOnce(&T, &T) -> Output,
    {
        self.execute(&[lhs, rhs], move |[x, y]| f(x, y))
    }

    /// Executes the function `f` over the values of the incoming `variables` assigning its output
    /// to a new intermediate variable which is returned. If any of the variables has no assigned value,
    /// an `Err` is returned with the unknown variable.
    #[inline]
    pub fn execute_assign<F, const N: usize>(
        &mut self,
        variables: &[Var; N],
        f: F,
    ) -> Result<Var, Var>
    where
        F: FnOnce([&T; N]) -> T,
    {
        let output_variable = Var(VarData::IntermediateVariable(
            self.intermediate_values.len(),
        ));
        let output_value = self.execute(variables, f)?;
        self.intermediate_values.push(output_value);
        Ok(output_variable)
    }

    /// Executes the binary operation `f` over the `lhs` and `rhs` values.
    ///
    /// See the [`execute_assign`](Self::execute_assign) method for more details.
    #[inline]
    pub fn execute_assign_binary_op<F>(&mut self, lhs: Var, rhs: Var, f: F) -> Result<Var, Var>
    where
        F: FnOnce(&T, &T) -> T,
    {
        self.execute_assign(&[lhs, rhs], move |[x, y]| f(x, y))
    }
}

/// Machine
pub trait Machine<COM = ()> {
    /// Metadata Type
    type Metadata;

    /// Creates a new instance of the machine over the given `metadata`,
    /// including generating the row-by-row constraints.
    ///
    /// `metadata` should contain
    ///     - imported columns (set of `OracleRegister` types)
    ///
    /// This `compiler` only needs to be able to do:
    ///     - allocation
    ///     - lookup linking (lookup tables, permutations, CTLs)
    ///     - arithmetic
    ///     - constraints
    ///
    /// The return type should only include the columns that are exported by this machine, no
    /// intermediate columns. Columns inside this machine should also be wired to describe the
    /// permutation information.
    ///
    /// Permutation linkages:
    ///     - compiler.link_permutation(input, table)
    ///
    /// Lookup linkages:
    ///     - compiler.link_lookup(input, table, input_permuted, table_permuted)
    fn create(metadata: Self::Metadata, compiler: &mut COM) -> Self;
}

///
pub trait PermutationLinker<T> {
    /// In the shape compiler this builds permutation shape tables.
    ///     In the trace it adds the sorting.
    /// In an execution compiler it does nothing (eventually move this part out of the vanishing
    /// polynomial section and into here).
    fn link_permutation(&mut self, input: T, table: T);
}

///
pub trait LookupLinker<T> {
    /// In the shape compiler this builds the lookup shape table.
    ///     In the trace it adds lookup columns (`gen_luts`).
    /// In an execution compiler it adds the lookup constraints over input_permuted and
    /// table_permuted.
    fn link_lookup(&mut self, input: T, table: T, input_permuted: T, table_permuted: T);
}

/// Machine Index
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct MachineIndex(usize);

/// Column Index
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ColumnIndex(usize);

/// Public Input Index
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PublicInputIndex(usize);

/// Column
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Column {
    /// Machine Index
    machine: MachineIndex,

    /// Column Index
    index: ColumnIndex,
}

/// Public Input
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct PublicInput {
    /// Machine Index
    machine: MachineIndex,

    /// Public Input Index
    index: PublicInputIndex,
}

/// Variable Data
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum VarData {
    /// Column Variable
    ColumnVariable {
        /// Column
        column: Column,

        /// Row Shift
        ///
        /// Counts how many rows away this target is relative to the current row.
        /// For the current row, `row_shift = 0` and for the next row
        /// `row_shift = 1`.
        row_shift: usize,
    },

    /// Public Input Variable
    PublicInput(PublicInput),

    /// Intermediate Variable
    ///
    /// Any computations over columns produce intermediate values that will be constrained
    /// internally.
    IntermediateVariable(usize),
}

/// Variable
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Var(VarData);

/// Oracle Wiring
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct OracleWiring {
    /// Source Machine Index
    pub source_machine: MachineIndex,

    /// Source Column Index
    pub source_column: ColumnIndex,

    /// Target Column Index
    pub target_column: ColumnIndex,
}

/// Multi-Machine Shape
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Shape {
    /// Oracle Dependencies
    pub oracle_dependencies: Vec<Vec<OracleWiring>>,

    /// Channel Counts
    pub channel_counts: Vec<(ColumnIndex, usize)>,
}

/// Register
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Register<T = Var> {
    /// Current Row Variable
    pub curr: T,

    /// Next Row Variable
    pub next: T,
}

impl<T, COM> Variable<COM> for Register<T> {
    #[inline]
    fn create(compiler: &mut COM) -> Self {
        let _ = compiler;
        todo!()
    }
}

/// Oracle Source Register
///
/// This kind of register can only be created whenever we have a column that we create an oracle
/// from using `compiler.create_oracle(column) -> OracleSourceRegister`.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct OracleSourceRegister {
    ///
    source: Register,

    ///
    filter: Bool,
}

/// Oracle Target Register
///
/// This kind of register can only be created whenever we have an `OracleSourceRegister` to bind to it using
/// `compiler.create_oracle(column) -> OracleTargetRegister` which should error if the `compiler`
/// current machine index is the same. No internal oracle columns?
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct OracleTargetRegister {
    ///
    target: Register,

    ///
    filter: Bool,
}

/// Boolean Register
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Bool<T = Var>(Register<T>);

impl<T> Bool<T> {
    ///
    #[inline]
    pub fn register(self) -> Register<T> {
        self.0
    }

    ///
    #[inline]
    pub fn curr(self) -> T {
        self.0.curr
    }

    ///
    #[inline]
    pub fn next(self) -> T {
        self.0.next
    }

    ///
    #[inline]
    pub fn create_unchecked<COM>(compiler: &mut COM) -> Self
    where
        Register<T>: Variable<COM>,
    {
        Self(compiler.allocate())
    }

    ///
    #[inline]
    pub fn create_unchecked_vec<COM>(len: usize, compiler: &mut COM) -> Vec<Self>
    where
        Register<T>: Variable<COM>,
    {
        (0..len).map(|_| Self::create_unchecked(compiler)).collect()
    }

    ///
    #[inline]
    pub fn create_vec<COM>(len: usize, compiler: &mut COM) -> Vec<Self>
    where
        COM: Constraint<T> + Mul<T> + One<T> + Sub<T>,
        T: Clone,
        Register<T>: Variable<COM>,
    {
        compiler.allocate_vec(len)
    }

    ///
    #[inline]
    pub fn from_register<COM>(register: Register<T>, compiler: &mut COM) -> Self
    where
        COM: Constraint<T> + Mul<T> + One<T> + Sub<T>,
        T: Clone,
    {
        compiler.assert_boolean(register.curr.clone());
        Self(register)
    }

    /// Returns the negation of `self`.
    #[inline]
    pub fn not<COM>(self, compiler: &mut COM) -> Self
    where
        COM: One<T> + Sub<T>,
        T: Clone,
    {
        let one = compiler.one();
        Self(Register {
            curr: compiler.sub(one.clone(), self.clone().curr()),
            next: compiler.sub(one, self.next()),
        })
    }
}

impl<T, COM> Variable<COM> for Bool<T>
where
    COM: Constraint<T> + Mul<T> + One<T> + Sub<T>,
    T: Clone,
    Register<T>: Variable<COM>,
{
    #[inline]
    fn create(compiler: &mut COM) -> Self {
        Self::from_register(compiler.allocate(), compiler)
    }
}

/// Defines an opcode structure.
#[macro_export]
macro_rules! define_opcode {
    ($(#[$meta:meta])* $vis:vis $name:ident { $head:ident, $($tail:ident),+ $(,)? }) => {
        $(#[$meta])*
        #[derive(Clone, Copy, Debug)]
        $vis struct $name<T = Var> {
            #[doc = "Opcode `"]
            #[doc = stringify!($head)]
            #[doc = "`"]
            pub $head: Bool<T>,

            $(
                #[doc = "Opcode `"]
                #[doc = stringify!($tail)]
                #[doc = "`"]
                pub $tail: Bool<T>
            ),+,

            /// Opcode Bit Sum
            pub bit_sum: Bool<T>,
        }

        impl<T> core::ops::Index<usize> for $name<T> {
            type Output = Bool<T>;

            #[inline]
            fn index(&self, index: usize) -> &Self::Output {
                [&self.$head, $(&self.$tail),+][index]
            }
        }

        impl<T, COM> Variable<COM> for $name<T>
        where
            COM: Add<T> + Constraint<T> + Mul<T> + One<T> + Sub<T> + Zero<T>,
            T: Clone,
        {
            #[inline]
            fn create(compiler: &mut COM) -> Self {
                struct TailOpcodes<S> {
                    $($tail: Bool<S>),+
                }
                let tail_opcodes = TailOpcodes { $($tail: compiler.allocate()),+ };
                let bit_sum =  Bool::from_register(
                    Register {
                        curr: compiler.sum([$(tail_opcodes.$tail.clone().curr()),+]),
                        next: compiler.sum([$(tail_opcodes.$tail.clone().next()),+]),
                    },
                    compiler
                );
                Self {
                    $head: bit_sum.clone().not(compiler),
                    $($tail: tail_opcodes.$tail),+,
                    bit_sum
                }
            }
        }
    };
}

define_opcode!(
    pub RlpOpcode {
        new_entry, list, recurse, return_, str_push, str_prefix, list_prefix, end_entry, halt
    }
);

/*

///
pub struct Oracle<T> {
    ///
    column: Column,

    ///
    filter_column: Column,

    ///
    __: PhantomData<T>,
}

pub struct RlpInputMemoryColumns {
    pub addr: Oracle<Register>,
    pub value: Oracle<Register>,
}

pub struct RlpCallStackColumns {
    pub is_pop: Oracle<Bool>,
    pub value: Oracle<Register>,
    pub timestamp: Oracle<Timestamp>,
}

pub struct RlpOutputStackColumns {
    pub addr: Oracle<Addr>,
    pub value: Oracle<Addr>,
}

pub struct RlpImportColumns {
    ///
    pub input_memory: [RlpInputMemoryColumns; 5],

    ///
    pub call_stack: [RlpCallStackColumns; 3],

    ///
    pub output_stack: [RlpOutputStackColumns; 5],
}

*/

/// Asserts a valid lookup over `curr_input`, `next_input`, and `next_table` in the `compiler`.
#[inline]
pub fn assert_lookup<T, COM>(curr_input: T, next_input: T, next_table: T, compiler: &mut COM)
where
    T: Clone,
    COM: Constraint<T> + ConstraintFiltered<T, LastRow> + Mul<T> + Sub<T>,
{
    // A "vertical" diff between the local and next permuted inputs.
    let diff_input_prev = compiler.sub(next_input.clone(), curr_input);

    // A "horizontal" diff between the next permuted input and permuted table value.
    let diff_input_table = compiler.sub(next_input, next_table);

    compiler.assert_zero_product(diff_input_prev, diff_input_table.clone());

    // This is actually constraining the first row, as per the spec, since `diff_input_table`
    // is a diff of the next row's values. In the context of `constraint_last_row`, the next
    // row is the first row.
    compiler.assert_zero_last_row(diff_input_table);
}

///
pub struct Lookup {
    ///
    pub input: Register,

    ///
    pub table: Register,

    ///
    pub permuted_input: Register,

    ///
    pub permuted_table: Register,
}

impl Lookup {
    ///
    #[inline]
    pub fn assert<COM>(self, compiler: &mut COM)
    where
        COM: Constraint<Var> + ConstraintFiltered<Var, LastRow> + Mul<Var> + Sub<Var>,
    {
        assert_lookup(
            self.permuted_input.curr,
            self.permuted_input.next,
            self.permuted_table.next,
            compiler,
        )
    }
}

///
#[derive(Clone, Debug)]
pub struct FilterColumns(Vec<Bool>);

///
#[derive(Clone, Copy, Debug)]
pub struct Timestamp(Register);

impl Timestamp {
    ///
    #[inline]
    pub fn register(self) -> Register {
        self.0
    }
}

impl<COM> Variable<COM> for Timestamp
where
    COM: Constraint<Var>
        + ConstraintFiltered<Var, FirstRow>
        + ConstraintFiltered<Var, Transition>
        + One<Var>
        + Sub<Var>,
{
    #[inline]
    fn create(compiler: &mut COM) -> Self {
        let one = compiler.one();
        let timestamp = compiler.allocate::<Register>();
        compiler.assert_eq_first_row(timestamp.curr, one);
        compiler.assert_increments_by(timestamp.curr, timestamp.next, one);
        Self(timestamp)
    }
}

define_opcode!(pub RwMemoryOpcode { read, write });

/// Read-Write Memory
pub struct RwMemory {
    /// Address
    pub addr: Register,

    /// Sorted Address
    pub addr_sorted: Register,

    /// Value
    pub value: Register,

    /// Sorted Values
    pub value_sorted: Register,

    /// Opcode
    pub opcode: RwMemoryOpcode,

    /// Sorted Read/Write Flag
    pub is_write_sorted: Bool,

    /// Sorted Timestamp
    pub timestamp_sorted: Register,

    /// Timestamp
    pub timestamp: Timestamp,

    /// Used to range check addresses and timestamp differenes
    pub timestamp_permuted: Register,

    /// Used for checking timestamp ordering via range check
    pub timestamp_sorted_diff: Register,

    /// Used for checking timestamp ordering via range check
    pub timestamp_sorted_diff_permuted: Register,
}

impl RwMemory {
    ///
    #[inline]
    pub fn permutations(&self) -> Vec<(Register, Register)> {
        vec![
            (self.addr, self.addr_sorted),
            (self.value, self.value_sorted),
            (
                self.opcode.write.register(),
                self.is_write_sorted.register(),
            ),
            (self.timestamp.register(), self.timestamp_sorted),
        ]
    }

    ///
    #[inline]
    pub fn lookups(&self) -> Vec<Lookup> {
        vec![Lookup {
            input: self.timestamp_sorted_diff,
            table: self.timestamp.register(),
            permuted_input: self.timestamp_sorted_diff_permuted,
            permuted_table: self.timestamp_permuted,
        }]
    }

    ///
    #[inline]
    fn assert<COM>(self, compiler: &mut COM) -> Self
    where
        COM: Constraint<Var>
            + ConstraintFiltered<Var, FirstRow>
            + ConstraintFiltered<Var, Transition>
            + ConstraintFiltered<Var, LastRow>
            + Add<Var>
            + Mul<Var>
            + One<Var>
            + Sub<Var>
            + Zero<Var>,
    {
        let one = compiler.one();

        let address_changed = compiler.sub(self.addr_sorted.next, self.addr_sorted.curr);
        let timestamp_changed =
            compiler.sub(self.timestamp_sorted.next, self.timestamp_sorted.curr);

        let address_unchanged = compiler.sub(one, address_changed);

        // ADDRESSES =====================================================================

        // Check that sorted addresses are monotonic, continuous, and start at 0.
        //
        // We do this by ensuring either the sorted address increases by 0 or 1 at each curr_row and at
        // the first curr_row, the sorted addr is 0.

        compiler.assert_zero_first_row(self.addr_sorted.curr);
        compiler.assert_zero_product_transition(address_changed, address_unchanged);

        // TIMESTAMPS ====================================================================

        // Check timestamps are increasing using a range check.
        //
        // This works as follows:
        // 1. Range check every timestamp to be in [1..num_rows].
        // 2. Range check the *difference* between the current and next timestamp to be in
        //    [1..num_rows] if address hasn't changed (i.e. we only care about timestamps for
        //    a particular address)
        // 3. This is enough. Let x, y be subsequent timestamps for a given address. x, y, and
        //    y - x are all in [1..num_rows]. Suppose "x > y" in the field. Then y - x > num_rows -><-
        //
        // This argument works as long as the number of rows is less than half of the field order, which
        // is very true for this library because we can only use up to 2^TWO_ADICITY rows and this is
        // usually far below the field size.
        //
        // We do this by enforcing the "unsorted" timestamps start at 1 and increment by 1 each row.
        // Then we apply a lookup against that col to check that the timestamp diffs are in [1..num_rows]
        // since timestamp_sorted is a permutation of timestamp, timestamp_sorted is guaranteed to be in
        // that range lookups are applied at the end of this function.

        compiler
            .when(address_unchanged)
            .assert_eq_transition(self.timestamp_sorted_diff.next, timestamp_changed);

        // Set the timestamp difference to 1 if the address changed as a dummy to indicate we don't care
        // (our range check doesn't include 0 because timestamps have to be unique).

        compiler
            .when(address_changed)
            .assert_eq_transition(self.timestamp_sorted_diff.next, one);

        // MEMORY TRACE ==================================================================

        // Check that the sorted memory trace is valid.
        //
        // To do this, we check the following at each step:
        // 1. If the address has changed, the memory trace is valid at this step
        // 2. If the address has not changed and the current operation is a write, the memory trace is
        //    valid at this step
        // 3. If the address has not changed and the current operation is a read, the memory trace is
        //    valid at this step iff the value is the same

        let next_is_not_write = compiler.sub(one, self.is_write_sorted.next());
        compiler
            .when_all([address_unchanged, next_is_not_write])
            .assert_eq_transition(self.value_sorted.next, self.value_sorted.curr);

        // LOOKUPS =======================================================================

        for lookup in self.lookups() {
            lookup.assert(compiler);
        }

        self
    }

    /* TODO:
    ///
    #[inline]
    pub fn read(&self, addr: T) -> T {
        // TRACE:
        value = memory.read(addr);

        // STARK:
        curr.value = value;
        curr.addr = addr;
        curr.is_write = false;
        next.timestamp = curr.timestamp + 1; // shared among all parts

        todo!()
    }

    ///
    #[inline]
    pub fn write(&self, addr: T, value: T) {
        // TRACE:
        memory.write(addr, value);

        // STARK:
        curr.addr = addr;
        curr.value = value;
        curr.is_write = true;
        next.timestamp = curr.timestamp + 1; // shared among all parts

        todo!()
    }
    */
}

impl<COM> Variable<COM> for RwMemory
where
    COM: Constraint<Var>
        + ConstraintFiltered<Var, FirstRow>
        + ConstraintFiltered<Var, Transition>
        + ConstraintFiltered<Var, LastRow>
        + Add<Var>
        + Mul<Var>
        + One<Var>
        + Sub<Var>
        + Zero<Var>,
{
    #[inline]
    fn create(compiler: &mut COM) -> Self {
        Self {
            addr: compiler.allocate(),
            addr_sorted: compiler.allocate(),
            value: compiler.allocate(),
            value_sorted: compiler.allocate(),
            opcode: compiler.allocate(),
            is_write_sorted: compiler.allocate(),
            timestamp_sorted: compiler.allocate(),
            timestamp: compiler.allocate(),
            timestamp_permuted: compiler.allocate(),
            timestamp_sorted_diff: compiler.allocate(),
            timestamp_sorted_diff_permuted: compiler.allocate(),
        }
        .assert(compiler)
    }
}

///
pub struct Stack {
    /// Stack Pointer
    pub sp: Register,

    /// Push/Pop Flag
    pub is_pop: Register,

    /// Read/Write Memory Gate
    pub rw_memory: RwMemory,
}

impl Stack {
    ///
    #[inline]
    pub fn permutations(&self) -> Vec<(Register, Register)> {
        self.rw_memory.permutations()
    }

    ///
    #[inline]
    pub fn lookups(&self) -> Vec<Lookup> {
        self.rw_memory.lookups()
    }

    ///
    #[inline]
    fn assert<COM>(self, compiler: &mut COM) -> Self
    where
        COM: Constraint<Var>
            + ConstraintFiltered<Var, FirstRow>
            + ConstraintFiltered<Var, Transition>
            + ConstraintFiltered<Var, LastRow>
            + Add<Var>
            + Mul<Var>
            + One<Var>
            + Sub<Var>
            + Zero<Var>,
    {
        let one = compiler.one();
        let is_push = compiler.sub(one, self.is_pop.curr);
        let sp_add_one = compiler.add(self.sp.curr, one);
        let sp_sub_one = compiler.sub(self.sp.curr, one);

        // Stack Semantics ===============================================================

        // Check that is_pop is binary (only operations are pop and push)
        compiler.assert_boolean(self.is_pop.curr);

        // Check SP starts at 0.
        compiler.assert_zero_first_row(self.sp.curr);

        // If the current operation is a push, the following should be true:
        // 1. addr should be sp
        // 2. next sp should be sp + 1
        // 3. is_write should be 1

        compiler
            .when(is_push)
            .assert_eq(self.rw_memory.addr.curr, self.sp.curr)
            .assert_eq_transition(self.sp.next, sp_add_one)
            .assert_one(self.rw_memory.opcode.write.curr());

        // If the current operation is a pop, the following should be true:
        //
        // 1. addr should be sp - 1
        // 2. next sp should be sp - 1
        // 3. is_write should be 0
        //
        // A corrolary of this is stack underflows (pop when sp is 0) can't happen since
        // then the addresses wouldn't satisfy the continuity requirement.

        compiler
            .when(self.is_pop.curr)
            .assert_eq(self.rw_memory.addr.curr, sp_sub_one)
            .assert_eq_transition(self.sp.next, sp_sub_one)
            .assert_zero(self.rw_memory.opcode.write.curr());

        self
    }

    /* TODO:
    ///
    #[inline]
    pub fn push(&self, value: T) {
        // TRACE:
        stack.push(value);
        curr.rw_memory.value = value;

        // STARK:
        curr.is_pop = false;
        curr.rw_memory.addr = curr.sp + 1;
        curr.rw_memory.is_write = true;
        next.timestamp = curr.timestamp + 1;
        next.sp = curr.sp + 1;

        todo!()
    }

    ///
    #[inline]
    pub fn pop(&self) -> T {
        // TRACE:
        value = stack.pop();
        curr.rw_memory.value = value;

        // STARK:
        curr.is_pop = true;
        curr.rw_memory.addr = curr.sp - 1;
        curr.rw_memory.is_write = false;
        next.timestamp = curr.timestamp + 1;
        next.sp = curr.sp - 1;

        todo!()
    }
    */
}

impl<COM> Variable<COM> for Stack
where
    COM: Constraint<Var>
        + ConstraintFiltered<Var, FirstRow>
        + ConstraintFiltered<Var, Transition>
        + ConstraintFiltered<Var, LastRow>
        + Add<Var>
        + Mul<Var>
        + One<Var>
        + Sub<Var>
        + Zero<Var>,
{
    #[inline]
    fn create(compiler: &mut COM) -> Self {
        Self {
            sp: compiler.allocate(),
            is_pop: compiler.allocate(),
            rw_memory: compiler.allocate(),
        }
        .assert(compiler)
    }
}
