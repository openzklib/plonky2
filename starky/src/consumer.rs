//! STARK Consumer

use crate::ir::{
    Add, Constant, Constraint, ConstraintFiltered, FirstRow, LastRow, Mul, One, Sub, Transition,
    Zero,
};

/// Consumer
pub trait Consumer<F, COM = ()> {
    /// Inserts the constraint that `value == 0` into `self`.
    fn constraint(&mut self, value: F, compiler: &mut COM);
}

impl<F, C, COM> Consumer<F, COM> for &mut C
where
    C: Consumer<F, COM>,
{
    #[inline]
    fn constraint(&mut self, value: F, compiler: &mut COM) {
        (**self).constraint(value, compiler)
    }
}

/// Filtered Consumer
pub trait FilteredConsumer<F, Filter, COM = ()> {
    /// Inserts the constraint that `value == 0` into `self`, conditioned on the `filter`.
    fn constraint_filtered(&mut self, filter: Filter, value: F, compiler: &mut COM);
}

impl<F, Filter, C, COM> FilteredConsumer<F, Filter, COM> for &mut C
where
    C: FilteredConsumer<F, Filter, COM>,
{
    #[inline]
    fn constraint_filtered(&mut self, filter: Filter, value: F, compiler: &mut COM) {
        (**self).constraint_filtered(filter, value, compiler)
    }
}

/// Consumer-Compiler Hybrid Structure
pub struct ConsumerCompiler<C, COM = ()> {
    /// Consumer
    pub consumer: C,

    /// Compiler
    pub compiler: COM,
}

impl<C, COM> ConsumerCompiler<C, COM> {
    /// Builds a new [`ConsumerCompiler`].
    #[inline]
    pub fn new(consumer: C, compiler: COM) -> Self {
        Self { consumer, compiler }
    }
}

/// Compiler
pub type Compiler<'t, C, COM> = ConsumerCompiler<&'t mut C, &'t mut COM>;

impl<'t, F, C, COM> Add<F> for Compiler<'t, C, COM>
where
    COM: Add<F>,
{
    #[inline]
    fn add(&mut self, lhs: F, rhs: F) -> F {
        self.compiler.add(lhs, rhs)
    }
}

impl<'t, F, C, COM> Sub<F> for Compiler<'t, C, COM>
where
    COM: Sub<F>,
{
    #[inline]
    fn sub(&mut self, lhs: F, rhs: F) -> F {
        self.compiler.sub(lhs, rhs)
    }
}

impl<'t, F, C, COM> Zero<F> for Compiler<'t, C, COM>
where
    COM: Zero<F>,
{
    #[inline]
    fn zero(&mut self) -> F {
        self.compiler.zero()
    }
}

impl<'t, F, C, COM> Mul<F> for Compiler<'t, C, COM>
where
    COM: Mul<F>,
{
    #[inline]
    fn mul(&mut self, lhs: F, rhs: F) -> F {
        self.compiler.mul(lhs, rhs)
    }
}

impl<'t, F, C, COM> One<F> for Compiler<'t, C, COM>
where
    COM: One<F>,
{
    #[inline]
    fn one(&mut self) -> F {
        self.compiler.one()
    }
}

impl<'t, F, C, COM> Constraint<F> for Compiler<'t, C, COM>
where
    C: Consumer<F, COM>,
{
    #[inline]
    fn assert_zero(&mut self, value: F) {
        self.consumer.constraint(value, self.compiler)
    }
}

impl<'t, F, Filter, C, COM> ConstraintFiltered<F, Filter> for Compiler<'t, C, COM>
where
    C: FilteredConsumer<F, Filter, COM>,
{
    #[inline]
    fn assert_zero_when(&mut self, filter: Filter, value: F) {
        self.consumer
            .constraint_filtered(filter, value, self.compiler);
    }
}

impl<'t, T, F, C, COM> Constant<T, F> for Compiler<'t, C, COM>
where
    COM: Constant<T, F>,
{
    #[inline]
    fn constant(&mut self, value: T) -> F {
        self.compiler.constant(value)
    }
}

/// Basic Consumer
pub mod basic {
    use plonky2::field::extension::Extendable;
    use plonky2::field::packed::PackedField;
    use plonky2::hash::hash_types::RichField;
    use plonky2::iop::ext_target::ExtensionTarget;
    use plonky2::iop::target::Target;
    use plonky2::plonk::circuit_builder::CircuitBuilder;

    use super::{Consumer as _, *};

    /// Scalar-Mul Addition
    pub trait ScalarMulAdd<T, E> {
        /// Performs a scalar multiplication and addition over `lhs`, `scalar`, and `rhs`.
        fn scalar_mul_add(&mut self, lhs: E, scalar: T, rhs: E) -> E;
    }

    impl<T, E, COM> ScalarMulAdd<T, E> for &mut COM
    where
        COM: ScalarMulAdd<T, E>,
    {
        #[inline]
        fn scalar_mul_add(&mut self, lhs: E, scalar: T, rhs: E) -> E {
            (**self).scalar_mul_add(lhs, scalar, rhs)
        }
    }

    impl<P> ScalarMulAdd<P::Scalar, P> for ()
    where
        P: PackedField,
    {
        #[inline]
        fn scalar_mul_add(&mut self, lhs: P, scalar: P::Scalar, rhs: P) -> P {
            (lhs * scalar) + rhs
        }
    }

    impl<F, const D: usize> ScalarMulAdd<Target, ExtensionTarget<D>> for CircuitBuilder<F, D>
    where
        F: RichField + Extendable<D>,
    {
        #[inline]
        fn scalar_mul_add(
            &mut self,
            lhs: ExtensionTarget<D>,
            scalar: Target,
            rhs: ExtensionTarget<D>,
        ) -> ExtensionTarget<D> {
            self.scalar_mul_add_extension(scalar, lhs, rhs)
        }
    }

    /// Basic Consumer
    pub struct Consumer<T, E> {
        /// Random values used to combine multiple constraints into one.
        pub alphas: Vec<T>,

        /// Running sums of constraints that have been emitted so far, scaled by powers of alpha.
        pub constraint_accs: Vec<E>,

        /// The evaluation of `X - g^(n-1)`.
        pub z_last: E,

        /// The evaluation of the Lagrange basis polynomial which is nonzero at the point associated
        /// with the first trace row, and zero at other points in the subgroup.
        pub lagrange_basis_first: E,

        /// The evaluation of the Lagrange basis polynomial which is nonzero at the point associated
        /// with the last trace row, and zero at other points in the subgroup.
        pub lagrange_basis_last: E,
    }

    impl<T, E> Consumer<T, E> {
        /// Builds a new [`Consumer`].
        #[inline]
        pub fn new(
            zero: E,
            alphas: Vec<T>,
            z_last: E,
            lagrange_basis_first: E,
            lagrange_basis_last: E,
        ) -> Self
        where
            E: Clone,
        {
            Self {
                constraint_accs: vec![zero; alphas.len()],
                alphas,
                z_last,
                lagrange_basis_first,
                lagrange_basis_last,
            }
        }

        /// Returns the accumulators for this consumer, dropping `self`.
        #[inline]
        pub fn into_accumulators(self) -> Vec<E> {
            self.constraint_accs
        }
    }

    impl<T, E, COM> super::Consumer<E, COM> for Consumer<T, E>
    where
        T: Clone,
        E: Clone,
        COM: ScalarMulAdd<T, E>,
    {
        #[inline]
        fn constraint(&mut self, value: E, compiler: &mut COM) {
            for (alpha, acc) in self.alphas.iter().zip(&mut self.constraint_accs) {
                *acc = compiler.scalar_mul_add(acc.clone(), alpha.clone(), value.clone());
            }
        }
    }

    impl<T, E, COM> FilteredConsumer<E, Transition, COM> for Consumer<T, E>
    where
        T: Clone,
        E: Clone,
        COM: Mul<E> + ScalarMulAdd<T, E>,
    {
        #[inline]
        fn constraint_filtered(&mut self, _: Transition, value: E, compiler: &mut COM) {
            let filtered_value = compiler.mul(self.z_last.clone(), value);
            self.constraint(filtered_value, compiler)
        }
    }

    impl<T, E, COM> FilteredConsumer<E, FirstRow, COM> for Consumer<T, E>
    where
        T: Clone,
        E: Clone,
        COM: Mul<E> + ScalarMulAdd<T, E>,
    {
        #[inline]
        fn constraint_filtered(&mut self, _: FirstRow, value: E, compiler: &mut COM) {
            let filtered_value = compiler.mul(self.lagrange_basis_first.clone(), value);
            self.constraint(filtered_value, compiler)
        }
    }

    impl<T, E, COM> FilteredConsumer<E, LastRow, COM> for Consumer<T, E>
    where
        T: Clone,
        E: Clone,
        COM: Mul<E> + ScalarMulAdd<T, E>,
    {
        #[inline]
        fn constraint_filtered(&mut self, _: LastRow, value: E, compiler: &mut COM) {
            let filtered_value = compiler.mul(self.lagrange_basis_last.clone(), value);
            self.constraint(filtered_value, compiler)
        }
    }

    /// Constraint Consumer
    pub type ConstraintConsumer<P> = Consumer<<P as PackedField>::Scalar, P>;

    /// Recursive Constraint Consumer
    pub type RecursiveConstraintConsumer<const D: usize> = Consumer<Target, ExtensionTarget<D>>;
}
