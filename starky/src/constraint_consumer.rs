//! Constraint Consumers

use alloc::vec;
use alloc::vec::Vec;

use plonky2::field::extension::Extendable;
use plonky2::field::packed::PackedField;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::ext_target::ExtensionTarget;
use plonky2::iop::target::Target;
use plonky2::plonk::circuit_builder::CircuitBuilder;

use crate::ir::{
    Add, Compiler, Constraint, ConstraintFiltered, FirstRow, LastRow, Mul, Sub, Transition,
};

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

/// Scalar-Mul Addition
pub trait ScalarMulAdd<T, E> {
    /// Performs a scalar multiplication and addition over `lhs`, `scalar`, and `rhs`.
    fn scalar_mul_add(&mut self, lhs: E, scalar: T, rhs: E) -> E;
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

/// Constraint Consumer
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

    /// Add one constraint valid on all rows.
    #[inline]
    pub fn constraint<COM>(&mut self, constraint: E, compiler: &mut COM)
    where
        T: Clone,
        E: Clone,
        COM: ScalarMulAdd<T, E>,
    {
        for (alpha, acc) in self.alphas.iter().zip(&mut self.constraint_accs) {
            *acc = compiler.scalar_mul_add(acc.clone(), alpha.clone(), constraint.clone());
        }
    }

    // TODO[remove]: Currently used by `permutation` logic.
    //
    /// Add one constraint, but first multiply it by a filter such that it will only apply to the
    /// first row of the trace.
    #[inline]
    pub fn constraint_first_row<COM>(&mut self, constraint: E, compiler: &mut COM)
    where
        T: Clone,
        E: Clone,
        COM: Mul<E> + ScalarMulAdd<T, E>,
    {
        let filtered_constraint = compiler.mul(constraint, self.lagrange_basis_first.clone());
        self.constraint(filtered_constraint, compiler);
    }
}

/// Constraint Compiler
pub struct ConstraintCompiler<'c, T, E, COM = ()> {
    /// Consumer Reference
    pub consumer: &'c mut Consumer<T, E>,

    /// Compiler Reference
    pub compiler: &'c mut COM,
}

impl<'c, T, E, COM> ConstraintCompiler<'c, T, E, COM> {
    /// Builds a new [`ConstraintCompiler`] from `consumer` and `compiler`.
    #[inline]
    pub fn new(consumer: &'c mut Consumer<T, E>, compiler: &'c mut COM) -> Self {
        Self { consumer, compiler }
    }
}

impl<'c, T, E, COM> Constraint<E> for ConstraintCompiler<'c, T, E, COM>
where
    T: Clone,
    E: Clone,
    COM: ScalarMulAdd<T, E>,
{
    #[inline]
    fn assert_zero(&mut self, value: E) {
        self.consumer.constraint(value, self.compiler)
    }
}

impl<'c, T, E, COM> ConstraintFiltered<E, Transition> for ConstraintCompiler<'c, T, E, COM>
where
    T: Clone,
    E: Clone,
    COM: Add<E> + Mul<E> + ScalarMulAdd<T, E> + Sub<E>,
{
    #[inline]
    fn assert_zero_when(&mut self, _: Transition, value: E) {
        self.assert_zero_product(self.consumer.z_last.clone(), value);
    }
}

impl<'c, T, E, COM> ConstraintFiltered<E, FirstRow> for ConstraintCompiler<'c, T, E, COM>
where
    T: Clone,
    E: Clone,
    COM: Add<E> + Mul<E> + ScalarMulAdd<T, E> + Sub<E>,
{
    #[inline]
    fn assert_zero_when(&mut self, _: FirstRow, value: E) {
        self.assert_zero_product(self.consumer.lagrange_basis_first.clone(), value);
    }
}

impl<'c, T, E, COM> ConstraintFiltered<E, LastRow> for ConstraintCompiler<'c, T, E, COM>
where
    T: Clone,
    E: Clone,
    COM: Add<E> + Mul<E> + ScalarMulAdd<T, E> + Sub<E>,
{
    #[inline]
    fn assert_zero_when(&mut self, _: LastRow, value: E) {
        self.assert_zero_product(self.consumer.lagrange_basis_last.clone(), value);
    }
}

impl<'c, T, E, COM> Add<E> for ConstraintCompiler<'c, T, E, COM>
where
    COM: Add<E>,
{
    #[inline]
    fn add(&mut self, lhs: E, rhs: E) -> E {
        self.compiler.add(lhs, rhs)
    }
}

impl<'c, T, E, COM> Sub<E> for ConstraintCompiler<'c, T, E, COM>
where
    COM: Sub<E>,
{
    #[inline]
    fn sub(&mut self, lhs: E, rhs: E) -> E {
        self.compiler.sub(lhs, rhs)
    }
}

impl<'c, T, E, COM> Mul<E> for ConstraintCompiler<'c, T, E, COM>
where
    COM: Mul<E>,
{
    #[inline]
    fn mul(&mut self, lhs: E, rhs: E) -> E {
        self.compiler.mul(lhs, rhs)
    }
}

/// Constraint Consumer
pub type ConstraintConsumer<P> = Consumer<<P as PackedField>::Scalar, P>;

/// Recursive Constraint Consumer
pub type RecursiveConstraintConsumer<const D: usize> = Consumer<Target, ExtensionTarget<D>>;

/*
/// Constraint Consumer
pub type ConstraintConsumer<P> = Consumer<<P as PackedField>::Scalar, P>;

impl<P> Constraint<P> for ConstraintConsumer<P>
where
    P: PackedField,
{
    #[inline]
    fn assert_zero(&mut self, value: P) {
        self.constraint(value, &mut ())
    }
}

impl<P> ConstraintFiltered<P, Transition> for ConstraintConsumer<P>
where
    P: PackedField,
{
    #[inline]
    fn assert_zero_when(&mut self, _: Transition, value: P) {
        self.assert_zero_product(self.z_last, value);
    }
}

impl<P> ConstraintFiltered<P, FirstRow> for ConstraintConsumer<P>
where
    P: PackedField,
{
    #[inline]
    fn assert_zero_when(&mut self, _: FirstRow, value: P) {
        self.assert_zero_product(self.lagrange_basis_first, value);
    }
}

impl<P> ConstraintFiltered<P, LastRow> for ConstraintConsumer<P>
where
    P: PackedField,
{
    #[inline]
    fn assert_zero_when(&mut self, _: LastRow, value: P) {
        self.assert_zero_product(self.lagrange_basis_last, value);
    }
}

impl<P> Add<P> for ConstraintConsumer<P>
where
    P: PackedField,
{
    #[inline]
    fn add(&mut self, lhs: P, rhs: P) -> P {
        lhs + rhs
    }
}

impl<P> Mul<P> for ConstraintConsumer<P>
where
    P: PackedField,
{
    #[inline]
    fn mul(&mut self, lhs: P, rhs: P) -> P {
        lhs * rhs
    }
}

impl<P> Sub<P> for ConstraintConsumer<P>
where
    P: PackedField,
{
    #[inline]
    fn sub(&mut self, lhs: P, rhs: P) -> P {
        lhs - rhs
    }
}

/// Constraint Consumer
pub type ConstraintConsumer<P> = Consumer<>;

/// Recursive Constraint Consumer
pub type RecursiveConstraintConsumer<const D: usize> = Consumer<Target, ExtensionTarget<D>>;

/// Recursive Constraint Compiler
pub struct RecursiveConstraintCompiler<'t, F, const D: usize>
where
    F: RichField + Extendable<D>,
{
    /// Consumer
    pub consumer: &'t mut RecursiveConstraintConsumer<D>,

    /// Circuit Builder
    pub builder: &'t mut CircuitBuilder<F, D>,
}

impl<'t, F, const D: usize> Constraint<ExtensionTarget<D>> for RecursiveConstraintCompiler<'t, F, D>
where
    F: RichField + Extendable<D>,
{
    #[inline]
    fn assert_zero(&mut self, value: ExtensionTarget<D>) {
        self.consumer.constraint(value, self.builder)
    }
}

impl<'t, F, const D: usize> ConstraintFiltered<ExtensionTarget<D>, Transition>
    for RecursiveConstraintCompiler<'t, F, D>
where
    F: RichField + Extendable<D>,
{
    #[inline]
    fn assert_zero_when(&mut self, _: Transition, value: ExtensionTarget<D>) {
        self.assert_zero_product(self.consumer.z_last, value);
    }
}

impl<'t, F, const D: usize> ConstraintFiltered<ExtensionTarget<D>, FirstRow>
    for RecursiveConstraintCompiler<'t, F, D>
where
    F: RichField + Extendable<D>,
{
    #[inline]
    fn assert_zero_when(&mut self, _: FirstRow, value: ExtensionTarget<D>) {
        self.assert_zero_product(self.consumer.lagrange_basis_first, value);
    }
}

impl<'t, F, const D: usize> ConstraintFiltered<ExtensionTarget<D>, LastRow>
    for RecursiveConstraintCompiler<'t, F, D>
where
    F: RichField + Extendable<D>,
{
    #[inline]
    fn assert_zero_when(&mut self, _: LastRow, value: ExtensionTarget<D>) {
        self.assert_zero_product(self.consumer.lagrange_basis_last, value);
    }
}

impl<'t, F, const D: usize> Add<ExtensionTarget<D>> for RecursiveConstraintCompiler<'t, F, D>
where
    F: RichField + Extendable<D>,
{
    #[inline]
    fn add(&mut self, lhs: ExtensionTarget<D>, rhs: ExtensionTarget<D>) -> ExtensionTarget<D> {
        self.builder.add_extension(lhs, rhs)
    }
}

impl<'t, F, const D: usize> Mul<ExtensionTarget<D>> for RecursiveConstraintCompiler<'t, F, D>
where
    F: RichField + Extendable<D>,
{
    #[inline]
    fn mul(&mut self, lhs: ExtensionTarget<D>, rhs: ExtensionTarget<D>) -> ExtensionTarget<D> {
        self.builder.mul_extension(lhs, rhs)
    }
}

impl<'t, F, const D: usize> Sub<ExtensionTarget<D>> for RecursiveConstraintCompiler<'t, F, D>
where
    F: RichField + Extendable<D>,
{
    #[inline]
    fn sub(&mut self, lhs: ExtensionTarget<D>, rhs: ExtensionTarget<D>) -> ExtensionTarget<D> {
        self.builder.sub_extension(lhs, rhs)
    }
}

*/
