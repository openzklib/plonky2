//! STARK IR

// TODO: Use `AssertZero` and `AssertEq` traits

use core::borrow::Borrow;

use plonky2::field::extension::Extendable;
use plonky2::field::packed::PackedField;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::ext_target::ExtensionTarget;
use plonky2::plonk::circuit_builder::CircuitBuilder;

/// Constraint
pub trait Constraint<F> {
    /// Asserts that `value == 0`.
    fn assert_zero(&mut self, value: &F) -> &mut Self;

    /// Asserts that `lhs == rhs` by subtracting them and calling [`Self::assert_zero`].
    #[inline]
    fn assert_eq(&mut self, lhs: &F, rhs: &F) -> &mut Self
    where
        Self: Sub<F>,
    {
        let diff = self.sub(lhs, rhs);
        self.assert_zero(&diff)
    }

    /// Asserts that `value == 1`.
    #[inline]
    fn assert_one(&mut self, value: &F) -> &mut Self
    where
        Self: Sub<F> + One<F>,
    {
        let one = self.one();
        self.assert_eq(value, &one)
    }
}

impl<F, C> Constraint<F> for &mut C
where
    C: Constraint<F>,
{
    #[inline]
    fn assert_zero(&mut self, value: &F) -> &mut Self {
        (**self).assert_zero(value);
        self
    }
}

/// Constraint Filtered
pub trait ConstraintFiltered<F, Filter> {
    /// Asserts that `value == 0` whenever the `filter` is true.
    fn assert_zero_when(&mut self, filter: Filter, value: &F) -> &mut Self;

    /// Asserts that `lhs == rhs` whenever the `filter` is true by subtracting them and calling
    /// [`Self::assert_zero_when`].
    #[inline]
    fn assert_eq_when(&mut self, filter: Filter, lhs: &F, rhs: &F) -> &mut Self
    where
        Self: Sub<F>,
    {
        let diff = self.sub(lhs, rhs);
        self.assert_zero_when(filter, &diff)
    }

    /// Asserts that `value == 1` whenever the `filter` is true.
    #[inline]
    fn assert_one_when(&mut self, filter: Filter, value: &F) -> &mut Self
    where
        Self: Sub<F> + One<F>,
    {
        let one = self.one();
        self.assert_eq_when(filter, value, &one)
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
pub trait Zero<F> {
    /// Returns the additive identity over `F`.
    fn zero(&mut self) -> F;
}

impl<F, C> Zero<F> for &mut C
where
    C: Zero<F>,
{
    #[inline]
    fn zero(&mut self) -> F {
        (**self).zero()
    }
}

impl<F> Zero<F> for ()
where
    F: PackedField,
{
    #[inline]
    fn zero(&mut self) -> F {
        F::ZEROS
    }
}

impl<F, const D: usize> Zero<ExtensionTarget<D>> for CircuitBuilder<F, D>
where
    F: RichField + Extendable<D>,
{
    #[inline]
    fn zero(&mut self) -> ExtensionTarget<D> {
        self.zero_extension()
    }
}

/// Addition
pub trait Add<F> {
    /// Adds `lhs` and `rhs` returning their sum.
    fn add(&mut self, lhs: &F, rhs: &F) -> F;

    ///
    #[inline]
    fn double(&mut self, value: &F) -> F {
        self.add(value, value)
    }

    /// Computes the sum over `iter`, returning [`Zero::zero`] if `iter` is empty.
    #[inline]
    fn sum<I>(&mut self, iter: I) -> F
    where
        Self: Zero<F>,
        I: IntoIterator,
        I::Item: Borrow<F>,
    {
        iter.into_iter()
            .fold(self.zero(), |lhs, rhs| self.add(lhs.borrow(), rhs.borrow()))
    }
}

impl<F, C> Add<F> for &mut C
where
    C: Add<F>,
{
    #[inline]
    fn add(&mut self, lhs: &F, rhs: &F) -> F {
        (**self).add(lhs, rhs)
    }
}

impl<P> Add<P> for ()
where
    P: PackedField,
{
    #[inline]
    fn add(&mut self, lhs: &P, rhs: &P) -> P {
        *lhs + *rhs
    }
}

impl<F, const D: usize> Add<ExtensionTarget<D>> for CircuitBuilder<F, D>
where
    F: RichField + Extendable<D>,
{
    #[inline]
    fn add(&mut self, lhs: &ExtensionTarget<D>, rhs: &ExtensionTarget<D>) -> ExtensionTarget<D> {
        self.add_extension(*lhs, *rhs)
    }
}

/// Subtraction
pub trait Sub<F> {
    /// Subtracts `lhs` and `rhs` returning their difference.
    fn sub(&mut self, lhs: &F, rhs: &F) -> F;
}

impl<F, C> Sub<F> for &mut C
where
    C: Sub<F>,
{
    #[inline]
    fn sub(&mut self, lhs: &F, rhs: &F) -> F {
        (**self).sub(lhs, rhs)
    }
}

impl<P> Sub<P> for ()
where
    P: PackedField,
{
    #[inline]
    fn sub(&mut self, lhs: &P, rhs: &P) -> P {
        *lhs - *rhs
    }
}

impl<F, const D: usize> Sub<ExtensionTarget<D>> for CircuitBuilder<F, D>
where
    F: RichField + Extendable<D>,
{
    #[inline]
    fn sub(&mut self, lhs: &ExtensionTarget<D>, rhs: &ExtensionTarget<D>) -> ExtensionTarget<D> {
        self.sub_extension(*lhs, *rhs)
    }
}

/// One
pub trait One<F> {
    /// Returns the multiplicative identity over `F`.
    fn one(&mut self) -> F;
}

impl<F, C> One<F> for &mut C
where
    C: One<F>,
{
    #[inline]
    fn one(&mut self) -> F {
        (**self).one()
    }
}

impl<F> One<F> for ()
where
    F: PackedField,
{
    #[inline]
    fn one(&mut self) -> F {
        F::ONES
    }
}

impl<F, const D: usize> One<ExtensionTarget<D>> for CircuitBuilder<F, D>
where
    F: RichField + Extendable<D>,
{
    #[inline]
    fn one(&mut self) -> ExtensionTarget<D> {
        self.one_extension()
    }
}

/// Multiplication
pub trait Mul<F> {
    /// Multiplies `lhs` and `rhs` returning their product.
    fn mul(&mut self, lhs: &F, rhs: &F) -> F;

    /// Computes the product over `iter`, returning [`One::one`] if `iter` is empty.
    #[inline]
    fn product<I>(&mut self, iter: I) -> F
    where
        Self: One<F>,
        I: IntoIterator,
        I::Item: Borrow<F>,
    {
        iter.into_iter()
            .fold(self.one(), |lhs, rhs| self.mul(lhs.borrow(), rhs.borrow()))
    }
}

impl<F, C> Mul<F> for &mut C
where
    C: Mul<F>,
{
    #[inline]
    fn mul(&mut self, lhs: &F, rhs: &F) -> F {
        (**self).mul(lhs, rhs)
    }
}

impl<P> Mul<P> for ()
where
    P: PackedField,
{
    #[inline]
    fn mul(&mut self, lhs: &P, rhs: &P) -> P {
        *lhs * *rhs
    }
}

impl<F, const D: usize> Mul<ExtensionTarget<D>> for CircuitBuilder<F, D>
where
    F: RichField + Extendable<D>,
{
    #[inline]
    fn mul(&mut self, lhs: &ExtensionTarget<D>, rhs: &ExtensionTarget<D>) -> ExtensionTarget<D> {
        self.mul_extension(*lhs, *rhs)
    }
}

/* TODO:
///
pub trait ArithmeticExtension<T, F> {
    ///
    fn arithmetic_extension(&mut self, const_0: T, const_1: T, multiplicand_0: F, multiplicand_1: F, addend: F) -> F;
}
*/

/// Arithmetic over a Field
pub trait Arithmetic<F>: Add<F> + Mul<F> + One<F> + Sub<F> + Zero<F> {
    #[inline]
    fn xor(&mut self, lhs: &F, rhs: &F) -> F {
        let sum = self.add(lhs, rhs);
        let product = self.mul(lhs, rhs);
        let double_product = self.double(&product);
        self.sub(&sum, &double_product)
    }
}

impl<F, C> Arithmetic<F> for C where C: Add<F> + Mul<F> + One<F> + Sub<F> + Zero<F> {}

/// IR Assertions
pub trait Assertions<F>: Sized {
    ///
    #[inline]
    fn assert_zero_product(&mut self, lhs: &F, rhs: &F) -> &mut Self
    where
        Self: Constraint<F> + Mul<F>,
    {
        let product = self.mul(lhs, rhs);
        self.assert_zero(&product)
    }

    ///
    #[inline]
    fn assert_boolean(&mut self, value: &F) -> &mut Self
    where
        Self: Constraint<F> + Mul<F> + One<F> + Sub<F>,
    {
        let one = self.one();
        let one_minus_value = self.sub(&one, value);
        self.assert_zero_product(value, &one_minus_value)
    }

    ///
    #[inline]
    fn assert_bit_decomposition<B>(&mut self, value: &F, bits: B) -> &mut Self
    where
        Self: Add<F> + Constraint<F> + Mul<F> + One<F> + Sub<F> + Zero<F>,
        B: IntoIterator,
        B::Item: Borrow<F>,
    {
        let one = self.one();
        let two = self.add(&one, &one);
        let mut addends = vec![];
        let mut shift = one;
        for bit in bits {
            let bit = bit.borrow();
            self.assert_boolean(bit);
            addends.push(self.mul(&shift, bit));
            shift = self.mul(&two, &shift);
        }
        let sum = self.sum(addends);
        self.assert_eq(value, &sum)
    }

    ///
    #[inline]
    fn assert_bit_decomposition_with_unchecked_bits<B>(&mut self, value: &F, bits: B) -> &mut Self
    where
        Self: Add<F> + Constraint<F> + Mul<F> + One<F> + Sub<F> + Zero<F>,
        B: IntoIterator,
        B::Item: Borrow<F>,
    {
        let one = self.one();
        let two = self.add(&one, &one);
        let mut addends = vec![];
        let mut shift = one;
        for bit in bits {
            let bit = bit.borrow();
            addends.push(self.mul(&shift, bit));
            shift = self.mul(&two, &shift);
        }
        let sum = self.sum(addends);
        self.assert_eq(value, &sum)
    }

    ///
    #[inline]
    fn assert_zero_transition(&mut self, value: &F) -> &mut Self
    where
        Self: ConstraintFiltered<F, Transition>,
    {
        self.assert_zero_when(Transition, value)
    }

    ///
    #[inline]
    fn assert_eq_transition(&mut self, lhs: &F, rhs: &F) -> &mut Self
    where
        Self: ConstraintFiltered<F, Transition> + Sub<F>,
    {
        self.assert_eq_when(Transition, lhs, rhs)
    }

    ///
    #[inline]
    fn assert_zero_product_transition(&mut self, lhs: &F, rhs: &F) -> &mut Self
    where
        Self: ConstraintFiltered<F, Transition> + Mul<F>,
    {
        let product = self.mul(lhs, rhs);
        self.assert_zero_transition(&product)
    }

    ///
    #[inline]
    fn assert_increments_by(&mut self, curr: &F, next: &F, step: &F) -> &mut Self
    where
        Self: ConstraintFiltered<F, Transition> + Sub<F>,
    {
        let diff = self.sub(curr, next);
        self.assert_eq_transition(&diff, step)
    }

    ///
    #[inline]
    fn assert_zero_first_row(&mut self, value: &F) -> &mut Self
    where
        Self: ConstraintFiltered<F, FirstRow>,
    {
        self.assert_zero_when(FirstRow, value)
    }

    ///
    #[inline]
    fn assert_eq_first_row(&mut self, lhs: &F, rhs: &F) -> &mut Self
    where
        Self: ConstraintFiltered<F, FirstRow> + Sub<F>,
    {
        self.assert_eq_when(FirstRow, lhs, rhs)
    }

    ///
    #[inline]
    fn assert_zero_last_row(&mut self, value: &F) -> &mut Self
    where
        Self: ConstraintFiltered<F, LastRow>,
    {
        self.assert_zero_when(LastRow, value)
    }

    ///
    #[inline]
    fn assert_eq_last_row(&mut self, lhs: &F, rhs: &F) -> &mut Self
    where
        Self: ConstraintFiltered<F, LastRow> + Sub<F>,
    {
        self.assert_eq_when(LastRow, lhs, rhs)
    }

    ///
    #[inline]
    fn assert_lookup(&mut self, curr_input: &F, next_input: &F, next_table: &F) -> &mut Self
    where
        F: Clone,
        Self: Constraint<F> + ConstraintFiltered<F, LastRow> + Mul<F> + Sub<F>,
    {
        // A "vertical" diff between the local and next permuted inputs.
        let diff_input_prev = self.sub(next_input, curr_input);

        // A "horizontal" diff between the next permuted input and permuted table value.
        let diff_input_table = self.sub(next_input, next_table);

        self.assert_zero_product(&diff_input_prev, &diff_input_table);

        // This is actually constraining the first row, as per the spec, since `diff_input_table`
        // is a diff of the next row's values. In the context of `constraint_last_row`, the next
        // row is the first row.
        self.assert_zero_last_row(&diff_input_table)
    }

    ///
    #[inline]
    fn when(&mut self, condition: F) -> Branch<F, Self> {
        Branch {
            condition,
            compiler: self,
        }
    }

    ///
    #[inline]
    fn when_all<I>(&mut self, conditions: I) -> Branch<F, Self>
    where
        Self: Mul<F> + One<F>,
        I: IntoIterator,
        I::Item: Borrow<F>,
    {
        let condition = self.product(conditions);
        self.when(condition)
    }
}

impl<F, COM> Assertions<F> for COM {}

/// Constant Allocation
pub trait Constant<T, F> {
    /// Allocates a constant `value` into the field type `F`.
    fn constant(&mut self, value: &T) -> F;
}

/// STARK Registers
#[derive(Clone, Copy, Debug)]
pub struct Registers<'t, T> {
    /// Current Values
    pub local_values: &'t [T],

    /// Next Values
    pub next_values: &'t [T],

    /// Public Inputs
    pub public_inputs: &'t [T],
}

/// Branching Compiler
pub struct Branch<'t, F, COM> {
    /// Condition
    condition: F,

    /// Base Compiler
    compiler: &'t mut COM,
}

impl<'t, F, COM> Add<F> for Branch<'t, F, COM>
where
    COM: Add<F>,
{
    #[inline]
    fn add(&mut self, lhs: &F, rhs: &F) -> F {
        self.compiler.add(lhs, rhs)
    }
}

impl<'t, F, COM> Sub<F> for Branch<'t, F, COM>
where
    COM: Sub<F>,
{
    #[inline]
    fn sub(&mut self, lhs: &F, rhs: &F) -> F {
        self.compiler.sub(lhs, rhs)
    }
}

impl<'t, F, COM> Zero<F> for Branch<'t, F, COM>
where
    COM: Zero<F>,
{
    #[inline]
    fn zero(&mut self) -> F {
        self.compiler.zero()
    }
}

impl<'t, F, COM> Mul<F> for Branch<'t, F, COM>
where
    COM: Mul<F>,
{
    #[inline]
    fn mul(&mut self, lhs: &F, rhs: &F) -> F {
        self.compiler.mul(lhs, rhs)
    }
}

impl<'t, F, COM> One<F> for Branch<'t, F, COM>
where
    COM: One<F>,
{
    #[inline]
    fn one(&mut self) -> F {
        self.compiler.one()
    }
}

impl<'t, F, COM> Constraint<F> for Branch<'t, F, COM>
where
    F: Clone,
    COM: Constraint<F> + Mul<F>,
{
    #[inline]
    fn assert_zero(&mut self, value: &F) -> &mut Self {
        let filtered_value = self.compiler.mul(&self.condition, value);
        self.compiler.assert_zero(&filtered_value);
        self
    }
}

impl<'t, F, Filter, COM> ConstraintFiltered<F, Filter> for Branch<'t, F, COM>
where
    F: Clone,
    COM: ConstraintFiltered<F, Filter> + Mul<F>,
{
    #[inline]
    fn assert_zero_when(&mut self, filter: Filter, value: &F) -> &mut Self {
        let filtered_value = self.compiler.mul(&self.condition, value);
        self.compiler.assert_zero_when(filter, &filtered_value);
        self
    }
}

/* TODO:
/// STARK Evaluation
pub trait Eval<F, COM = ()>
where
    COM: Compiler<F>,
{
    /// Evaluates a STARK over `curr`, `next`, `public_inputs` using `compiler`.
    fn eval(&self, curr: &[F], next: &[F], public_inputs: &[F], compiler: &mut COM);

    /// Evaluates a STARK over `registers` using `compiler`.
    #[inline]
    fn eval_registers(&self, registers: Registers<F>, compiler: &mut COM) {
        self.eval(
            registers.local_values,
            registers.next_values,
            registers.public_inputs,
            compiler,
        );
    }
}

///
pub trait Eval<F, C, COM = ()> {
    ///
    type Registers<'t>;

    ///
    fn eval(&self, regsiters: Self::Registers<'_>, consumer: &mut C, compiler: &mut COM);
}

///
pub trait Gate<F, COM = ()>
where
    COM: Compiler<F>,
{
    /// Gate Data
    type Data;

    /// Evaluates a STARK over `curr`, `next`, `public_inputs`, and `data` using `compiler`.
    fn eval(
        &self,
        curr: &[F],
        next: &[F],
        public_inputs: &[F],
        data: Self::Data,
        compiler: &mut COM,
    );
}
*/
