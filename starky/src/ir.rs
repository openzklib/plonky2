//! STARK IR

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

/// All Rows Filter
pub struct All;

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

/// Product Filter
pub struct Product<F>(pub F);

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

/// One
pub trait One<F> {
    /// Returns the multiplicative identity over `F`.
    fn one(&mut self) -> F;
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

/// IR Compiler
pub trait Compiler<F>:
    Constraint<F>
    + ConstraintFiltered<F, Transition>
    + ConstraintFiltered<F, FirstRow>
    + ConstraintFiltered<F, LastRow>
    + Add<F>
    + Mul<F>
    + Sub<F>
    + Sized
{
    ///
    #[inline]
    fn assert_zero_product(&mut self, lhs: F, rhs: F) {
        self.assert_zero_when(Product(lhs), rhs);
    }

    ///
    #[inline]
    fn assert_zero_transition(&mut self, value: F) {
        self.assert_zero_when(Transition, value);
    }

    ///
    #[inline]
    fn assert_eq_transition(&mut self, lhs: F, rhs: F) {
        self.assert_eq_when(Transition, lhs, rhs);
    }

    ///
    #[inline]
    fn assert_zero_first_row(&mut self, value: F) {
        self.assert_zero_when(FirstRow, value);
    }

    ///
    #[inline]
    fn assert_eq_first_row(&mut self, lhs: F, rhs: F) {
        self.assert_eq_when(FirstRow, lhs, rhs);
    }

    ///
    #[inline]
    fn assert_zero_last_row(&mut self, value: F) {
        self.assert_zero_when(LastRow, value);
    }

    ///
    #[inline]
    fn assert_eq_last_row(&mut self, lhs: F, rhs: F) {
        self.assert_eq_when(LastRow, lhs, rhs);
    }
}

impl<F, COM> Compiler<F> for COM where
    COM: Constraint<F>
        + ConstraintFiltered<F, Transition>
        + ConstraintFiltered<F, FirstRow>
        + ConstraintFiltered<F, LastRow>
        + Add<F>
        + Mul<F>
        + Sub<F>
{
}

/// Constant Allocation
pub trait Constant<T, F> {
    /// Allocates a constant `value` into the field type `F`.
    fn constant(&mut self, value: T) -> F;
}

/// STARK Evaluation
pub trait Eval<F, COM = ()>
where
    COM: Compiler<F>,
{
    /// Evaluates a STARK over `curr`, `next`, `public_inputs` using `compiler`.
    fn eval(&self, curr: &[F], next: &[F], public_inputs: &[F], compiler: &mut COM);
}
