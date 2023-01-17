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

/// All Rows Filter
pub struct All;

/// Transition Filter
pub struct Transition;

/// First Row Filter
pub struct FirstRow;

/// Last Row Filter
pub struct LastRow;

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

impl<F, C> ConstraintFiltered<F, All> for C
where
    C: Constraint<F>,
{
    #[inline]
    fn assert_zero_when(&mut self, _: All, value: F) {
        self.assert_zero(value)
    }

    #[inline]
    fn assert_eq_when(&mut self, _: All, lhs: F, rhs: F)
    where
        Self: Sub<F>,
    {
        self.assert_eq(lhs, rhs)
    }
}

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
{
    ///
    #[inline]
    fn assert_zero_transition(&mut self, value: F) {
        self.assert_zero_when(Transition, value)
    }

    ///
    #[inline]
    fn assert_eq_transition(&mut self, lhs: F, rhs: F) {
        self.assert_eq_when(Transition, lhs, rhs)
    }

    ///
    #[inline]
    fn assert_zero_first_row(&mut self, value: F) {
        self.assert_zero_when(FirstRow, value)
    }

    ///
    #[inline]
    fn assert_eq_first_row(&mut self, lhs: F, rhs: F) {
        self.assert_eq_when(FirstRow, lhs, rhs)
    }

    ///
    #[inline]
    fn assert_zero_last_row(&mut self, value: F) {
        self.assert_zero_when(LastRow, value);
    }

    ///
    #[inline]
    fn assert_eq_last_row(&mut self, lhs: F, rhs: F) {
        self.assert_eq_when(LastRow, lhs, rhs)
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

/// Fibonacci Example STARK
pub mod fibonacci {
    use super::*;

    /// Fibonacci STARK
    pub struct FibonacciStark;

    impl FibonacciStark {
        /// The first public input is `x0`.
        pub const FIRST_TERM: usize = 0;

        /// The second public input is `x1`.
        pub const SECOND_TERM: usize = 1;

        /// The third public input is the second element of the last row, which should be equal to the
        /// `num_rows`-th Fibonacci number.
        pub const FINAL_TERM: usize = 2;
    }

    impl<F, COM> Eval<F, COM> for FibonacciStark
    where
        F: Copy,
        COM: Compiler<F>,
    {
        #[inline]
        fn eval(&self, curr: &[F], next: &[F], public_inputs: &[F], compiler: &mut COM) {
            // Constrain Public Inputs
            compiler.assert_eq_first_row(public_inputs[Self::FIRST_TERM], curr[0]);
            compiler.assert_eq_first_row(public_inputs[Self::SECOND_TERM], curr[1]);
            compiler.assert_eq_last_row(public_inputs[Self::FINAL_TERM], curr[1]);

            // Add Fibonacci Terms
            let sum = compiler.add(curr[0], curr[1]);

            // Constrain Transition
            compiler.assert_eq_transition(next[0], curr[1]);
            compiler.assert_eq_transition(next[1], sum);
        }
    }
}
