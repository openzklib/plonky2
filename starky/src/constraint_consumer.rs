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

/// Constraint Consumer
pub type ConstraintConsumer<P> = Consumer<<P as PackedField>::Scalar, P>;

///
pub struct ConstraintCompiler<P>(pub ConstraintConsumer<P>)
where
    P: PackedField;

impl<P> Constraint<P> for ConstraintCompiler<P>
where
    P: PackedField,
{
    #[inline]
    fn assert_zero(&mut self, value: P) {
        self.0.constraint(value, &mut ())
    }
}

impl<P> ConstraintFiltered<P, Transition> for ConstraintCompiler<P>
where
    P: PackedField,
{
    #[inline]
    fn assert_zero_when(&mut self, _: Transition, value: P) {
        self.assert_zero_product(self.0.z_last, value);
    }
}

impl<P> ConstraintFiltered<P, FirstRow> for ConstraintCompiler<P>
where
    P: PackedField,
{
    #[inline]
    fn assert_zero_when(&mut self, _: FirstRow, value: P) {
        self.assert_zero_product(self.0.lagrange_basis_first, value);
    }
}

impl<P> ConstraintFiltered<P, LastRow> for ConstraintCompiler<P>
where
    P: PackedField,
{
    #[inline]
    fn assert_zero_when(&mut self, _: LastRow, value: P) {
        self.assert_zero_product(self.0.lagrange_basis_last, value);
    }
}

impl<P> Add<P> for ConstraintCompiler<P>
where
    P: PackedField,
{
    #[inline]
    fn add(&mut self, lhs: P, rhs: P) -> P {
        lhs + rhs
    }
}

impl<P> Mul<P> for ConstraintCompiler<P>
where
    P: PackedField,
{
    #[inline]
    fn mul(&mut self, lhs: P, rhs: P) -> P {
        lhs * rhs
    }
}

impl<P> Sub<P> for ConstraintCompiler<P>
where
    P: PackedField,
{
    #[inline]
    fn sub(&mut self, lhs: P, rhs: P) -> P {
        lhs - rhs
    }
}

/// Recursive Constraint Consumer
pub type RecursiveConstraintConsumer<const D: usize> = Consumer<Target, ExtensionTarget<D>>;

/// Recursive Constraint Compiler
pub struct RecursiveConstraintCompiler<F, const D: usize>
where
    F: RichField + Extendable<D>,
{
    /// Consumer
    pub consumer: RecursiveConstraintConsumer<D>,

    /// Circuit Builder
    pub builder: CircuitBuilder<F, D>,
}

impl<F, const D: usize> Constraint<ExtensionTarget<D>> for RecursiveConstraintCompiler<F, D>
where
    F: RichField + Extendable<D>,
{
    #[inline]
    fn assert_zero(&mut self, value: ExtensionTarget<D>) {
        self.consumer.constraint(value, &mut self.builder)
    }
}

impl<F, const D: usize> ConstraintFiltered<ExtensionTarget<D>, Transition>
    for RecursiveConstraintCompiler<F, D>
where
    F: RichField + Extendable<D>,
{
    #[inline]
    fn assert_zero_when(&mut self, _: Transition, value: ExtensionTarget<D>) {
        self.assert_zero_product(self.consumer.z_last, value);
    }
}

impl<F, const D: usize> ConstraintFiltered<ExtensionTarget<D>, FirstRow>
    for RecursiveConstraintCompiler<F, D>
where
    F: RichField + Extendable<D>,
{
    #[inline]
    fn assert_zero_when(&mut self, _: FirstRow, value: ExtensionTarget<D>) {
        self.assert_zero_product(self.consumer.lagrange_basis_first, value);
    }
}

impl<F, const D: usize> ConstraintFiltered<ExtensionTarget<D>, LastRow>
    for RecursiveConstraintCompiler<F, D>
where
    F: RichField + Extendable<D>,
{
    #[inline]
    fn assert_zero_when(&mut self, _: LastRow, value: ExtensionTarget<D>) {
        self.assert_zero_product(self.consumer.lagrange_basis_last, value);
    }
}

impl<F, const D: usize> Add<ExtensionTarget<D>> for RecursiveConstraintCompiler<F, D>
where
    F: RichField + Extendable<D>,
{
    #[inline]
    fn add(&mut self, lhs: ExtensionTarget<D>, rhs: ExtensionTarget<D>) -> ExtensionTarget<D> {
        self.builder.add_extension(lhs, rhs)
    }
}

impl<F, const D: usize> Mul<ExtensionTarget<D>> for RecursiveConstraintCompiler<F, D>
where
    F: RichField + Extendable<D>,
{
    #[inline]
    fn mul(&mut self, lhs: ExtensionTarget<D>, rhs: ExtensionTarget<D>) -> ExtensionTarget<D> {
        self.builder.mul_extension(lhs, rhs)
    }
}

impl<F, const D: usize> Sub<ExtensionTarget<D>> for RecursiveConstraintCompiler<F, D>
where
    F: RichField + Extendable<D>,
{
    #[inline]
    fn sub(&mut self, lhs: ExtensionTarget<D>, rhs: ExtensionTarget<D>) -> ExtensionTarget<D> {
        self.builder.sub_extension(lhs, rhs)
    }
}
