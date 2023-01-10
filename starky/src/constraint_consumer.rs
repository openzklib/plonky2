use alloc::vec;
use alloc::vec::Vec;

use plonky2::field::extension::Extendable;
use plonky2::field::packed::PackedField;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::ext_target::ExtensionTarget;
use plonky2::iop::target::Target;
use plonky2::plonk::circuit_builder::CircuitBuilder;

///
pub trait Sub<T> {
    ///
    fn sub(&mut self, lhs: &T, rhs: &T) -> T;
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

///
pub trait Mul<T> {
    ///
    fn mul(&mut self, lhs: &T, rhs: &T) -> T;
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

///
pub trait ScalarMulAdd<T, E> {
    ///
    fn scalar_mul_add(&mut self, lhs: &E, scalar: &T, rhs: &E) -> E;
}

impl<P> ScalarMulAdd<P::Scalar, P> for ()
where
    P: PackedField,
{
    #[inline]
    fn scalar_mul_add(&mut self, lhs: &P, scalar: &P::Scalar, rhs: &P) -> P {
        (*lhs * *scalar) + *rhs
    }
}

impl<F, const D: usize> ScalarMulAdd<Target, ExtensionTarget<D>> for CircuitBuilder<F, D>
where
    F: RichField + Extendable<D>,
{
    #[inline]
    fn scalar_mul_add(
        &mut self,
        lhs: &ExtensionTarget<D>,
        scalar: &Target,
        rhs: &ExtensionTarget<D>,
    ) -> ExtensionTarget<D> {
        self.scalar_mul_add_extension(*scalar, *lhs, *rhs)
    }
}

///
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
    ///
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

    ///
    #[inline]
    pub fn accumulators(self) -> Vec<E> {
        self.constraint_accs
    }

    /// Add one constraint valid on all rows except the last.
    #[inline]
    pub fn constraint_transition<COM>(&mut self, constraint: E, compiler: &mut COM)
    where
        COM: Mul<E> + ScalarMulAdd<T, E>,
    {
        let filtered_constraint = compiler.mul(&constraint, &self.z_last);
        self.constraint(filtered_constraint, compiler);
    }

    /// Add one constraint valid on all rows.
    #[inline]
    pub fn constraint<COM>(&mut self, constraint: E, compiler: &mut COM)
    where
        COM: ScalarMulAdd<T, E>,
    {
        for (alpha, acc) in self.alphas.iter().zip(&mut self.constraint_accs) {
            *acc = compiler.scalar_mul_add(acc, alpha, &constraint);
        }
    }

    /// Add one constraint, but first multiply it by a filter such that it will only apply to the
    /// first row of the trace.
    #[inline]
    pub fn constraint_first_row<COM>(&mut self, constraint: E, compiler: &mut COM)
    where
        COM: Mul<E> + ScalarMulAdd<T, E>,
    {
        let filtered_constraint = compiler.mul(&constraint, &self.lagrange_basis_first);
        self.constraint(filtered_constraint, compiler);
    }

    /// Add one constraint, but first multiply it by a filter such that it will only apply to the
    /// last row of the trace.
    #[inline]
    pub fn constraint_last_row<COM>(&mut self, constraint: E, compiler: &mut COM)
    where
        COM: Mul<E> + ScalarMulAdd<T, E>,
    {
        let filtered_constraint = compiler.mul(&constraint, &self.lagrange_basis_last);
        self.constraint(filtered_constraint, compiler);
    }
}

///
pub type ConstraintConsumer<P> = Consumer<<P as PackedField>::Scalar, P>;

///
pub type RecursiveConstraintConsumer<const D: usize> = Consumer<Target, ExtensionTarget<D>>;
