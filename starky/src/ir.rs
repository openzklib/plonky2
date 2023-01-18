//! STARK IR

// TODO: Use `AssertZero` and `AssertEq` traits

use plonky2::field::extension::Extendable;
use plonky2::field::packed::PackedField;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::ext_target::ExtensionTarget;
use plonky2::plonk::circuit_builder::CircuitBuilder;

/// Constraint
pub trait Constraint<F> {
    /// Asserts that `value == 0` in the constraint system.
    fn assert_zero(&mut self, value: F);

    /// Asserts that `lhs == rhs` by subtracting them and calling [`Self::assert_zero`].
    #[inline]
    fn assert_eq(&mut self, lhs: F, rhs: F)
    where
        Self: Sub<F>,
    {
        let diff = self.sub(lhs, rhs);
        self.assert_zero(diff);
    }
}

impl<F, C> Constraint<F> for &mut C
where
    C: Constraint<F>,
{
    #[inline]
    fn assert_zero(&mut self, value: F) {
        (**self).assert_zero(value)
    }
}

/// Constraint Filtered
pub trait ConstraintFiltered<F, Filter> {
    /// Asserts that `value == 0` whenever the `filter` is true.
    fn assert_zero_when(&mut self, filter: Filter, value: F);

    /// Asserts that `lhs == rhs` whenever the `filter` is true by subtracting them and calling
    /// [`Self::assert_zero_when`].
    #[inline]
    fn assert_eq_when(&mut self, filter: Filter, lhs: F, rhs: F)
    where
        Self: Sub<F>,
    {
        let diff = self.sub(lhs, rhs);
        self.assert_zero_when(filter, diff);
    }
}

///
pub trait Filter<F, C> {
    /// Asserts that `value == 0` whenever the `self` is true.
    fn assert_zero_when(self, value: F, consumer: &mut C);
}

/// All Rows Filter
pub struct All;

impl<F, C> Filter<F, C> for All
where
    C: Constraint<F>,
{
    #[inline]
    fn assert_zero_when(self, value: F, consumer: &mut C) {
        consumer.assert_zero(value)
    }
}

/*
impl<F, C> ConstraintFiltered<F, All> for C
where
    C: Constraint<F>,
{
    #[inline]
    fn assert_zero_when(&mut self, _: All, value: F) {
        self.assert_zero(value);
    }

    #[inline]
    fn assert_eq_when(&mut self, _: All, lhs: F, rhs: F)
    where
        Self: Sub<F>,
    {
        self.assert_eq(lhs, rhs);
    }
}
*/

/// Product Filter
pub struct Product<F>(pub F);

impl<F, C> Filter<F, C> for Product<F>
where
    C: Constraint<F> + Mul<F>,
{
    #[inline]
    fn assert_zero_when(self, value: F, consumer: &mut C) {
        let filtered_value = consumer.mul(value, self.0);
        consumer.assert_zero(filtered_value);
    }
}

/*
impl<F, C> ConstraintFiltered<F, Product<F>> for C
where
    C: Constraint<F> + Mul<F>,
{
    #[inline]
    fn assert_zero_when(&mut self, filter: Product<F>, value: F) {
        let filtered_value = self.mul(value, filter.0);
        self.assert_zero(filtered_value);
    }
}
*/

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

/// Addition
pub trait Add<F> {
    /// Adds `lhs` and `rhs` returning their sum.
    fn add(&mut self, lhs: F, rhs: F) -> F;

    /// Computes the sum over `iter`, returning [`Zero::zero`] if `iter` is empty.
    #[inline]
    fn sum<I>(&mut self, iter: I) -> F
    where
        Self: Zero<F>,
        I: IntoIterator<Item = F>,
    {
        iter.into_iter()
            .reduce(|lhs, rhs| self.add(lhs, rhs))
            .unwrap_or_else(|| self.zero())
    }
}

impl<F, C> Add<F> for &mut C
where
    C: Add<F>,
{
    #[inline]
    fn add(&mut self, lhs: F, rhs: F) -> F {
        (**self).add(lhs, rhs)
    }
}

impl<P> Add<P> for ()
where
    P: PackedField,
{
    #[inline]
    fn add(&mut self, lhs: P, rhs: P) -> P {
        lhs + rhs
    }
}

impl<F, const D: usize> Add<ExtensionTarget<D>> for CircuitBuilder<F, D>
where
    F: RichField + Extendable<D>,
{
    #[inline]
    fn add(&mut self, lhs: ExtensionTarget<D>, rhs: ExtensionTarget<D>) -> ExtensionTarget<D> {
        self.add_extension(lhs, rhs)
    }
}

/// Negation
pub trait Neg<F> {
    /// Returns the negation of `value`.
    fn neg(&mut self, value: F) -> F;
}

/// Subtraction
pub trait Sub<F> {
    /// Subtracts `lhs` and `rhs` returning their difference.
    fn sub(&mut self, lhs: F, rhs: F) -> F;
}

impl<F, C> Sub<F> for &mut C
where
    C: Sub<F>,
{
    #[inline]
    fn sub(&mut self, lhs: F, rhs: F) -> F {
        (**self).sub(lhs, rhs)
    }
}

impl<P> Sub<P> for ()
where
    P: PackedField,
{
    #[inline]
    fn sub(&mut self, lhs: P, rhs: P) -> P {
        lhs - rhs
    }
}

impl<F, const D: usize> Sub<ExtensionTarget<D>> for CircuitBuilder<F, D>
where
    F: RichField + Extendable<D>,
{
    #[inline]
    fn sub(&mut self, lhs: ExtensionTarget<D>, rhs: ExtensionTarget<D>) -> ExtensionTarget<D> {
        self.sub_extension(lhs, rhs)
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

/// Multiplication
pub trait Mul<F> {
    /// Multiplies `lhs` and `rhs` returning their product.
    fn mul(&mut self, lhs: F, rhs: F) -> F;

    /// Computes the product over `iter`, returning [`One::one`] if `iter` is empty.
    #[inline]
    fn product<I>(&mut self, iter: I) -> F
    where
        Self: One<F>,
        I: IntoIterator<Item = F>,
    {
        iter.into_iter()
            .reduce(|lhs, rhs| self.mul(lhs, rhs))
            .unwrap_or_else(|| self.one())
    }
}

impl<F, C> Mul<F> for &mut C
where
    C: Mul<F>,
{
    #[inline]
    fn mul(&mut self, lhs: F, rhs: F) -> F {
        (**self).mul(lhs, rhs)
    }
}

impl<P> Mul<P> for ()
where
    P: PackedField,
{
    #[inline]
    fn mul(&mut self, lhs: P, rhs: P) -> P {
        lhs * rhs
    }
}

impl<F, const D: usize> Mul<ExtensionTarget<D>> for CircuitBuilder<F, D>
where
    F: RichField + Extendable<D>,
{
    #[inline]
    fn mul(&mut self, lhs: ExtensionTarget<D>, rhs: ExtensionTarget<D>) -> ExtensionTarget<D> {
        self.mul_extension(lhs, rhs)
    }
}

/// Arithmetic over a Field
pub trait Arithmetic<F>: Add<F> + Mul<F> + Sub<F> {}

impl<F, C> Arithmetic<F> for C where C: Add<F> + Mul<F> + Sub<F> {}

/// IR Assertions
pub trait Assertions<F>: Sized {
    ///
    #[inline]
    fn assert_zero_product(&mut self, lhs: F, rhs: F)
    where
        Self: Constraint<F> + Mul<F>,
    {
        Product(lhs).assert_zero_when(rhs, self)
    }

    ///
    #[inline]
    fn assert_zero_transition(&mut self, value: F)
    where
        Self: ConstraintFiltered<F, Transition>,
    {
        self.assert_zero_when(Transition, value);
    }

    ///
    #[inline]
    fn assert_eq_transition(&mut self, lhs: F, rhs: F)
    where
        Self: ConstraintFiltered<F, Transition> + Sub<F>,
    {
        self.assert_eq_when(Transition, lhs, rhs);
    }

    ///
    #[inline]
    fn assert_zero_first_row(&mut self, value: F)
    where
        Self: ConstraintFiltered<F, FirstRow>,
    {
        self.assert_zero_when(FirstRow, value);
    }

    ///
    #[inline]
    fn assert_eq_first_row(&mut self, lhs: F, rhs: F)
    where
        Self: ConstraintFiltered<F, FirstRow> + Sub<F>,
    {
        self.assert_eq_when(FirstRow, lhs, rhs);
    }

    ///
    #[inline]
    fn assert_zero_last_row(&mut self, value: F)
    where
        Self: ConstraintFiltered<F, LastRow>,
    {
        self.assert_zero_when(LastRow, value);
    }

    ///
    #[inline]
    fn assert_eq_last_row(&mut self, lhs: F, rhs: F)
    where
        Self: ConstraintFiltered<F, LastRow> + Sub<F>,
    {
        self.assert_eq_when(LastRow, lhs, rhs);
    }
}

impl<F, COM> Assertions<F> for COM {}

/// Constant Allocation
pub trait Constant<T, F> {
    /// Allocates a constant `value` into the field type `F`.
    fn constant(&mut self, value: T) -> F;
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
