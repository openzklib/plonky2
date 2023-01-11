use alloc::vec;
use alloc::vec::Vec;

use plonky2::field::packed::PackedField;
use plonky2::iop::ext_target::ExtensionTarget;
use plonky2::iop::target::Target;

use crate::arithmetic::{Mul, ScalarMulAdd};

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

    /// Add one constraint valid on all rows except the last.
    #[inline]
    pub fn constraint_transition<COM>(&mut self, constraint: E, compiler: &mut COM)
    where
        T: Clone,
        E: Clone,
        COM: Mul<E, Output = E> + ScalarMulAdd<T, E>,
    {
        let filtered_constraint = compiler.mul(constraint, self.z_last.clone());
        self.constraint(filtered_constraint, compiler);
    }

    /// Add one constraint, but first multiply it by a filter such that it will only apply to the
    /// first row of the trace.
    #[inline]
    pub fn constraint_first_row<COM>(&mut self, constraint: E, compiler: &mut COM)
    where
        T: Clone,
        E: Clone,
        COM: Mul<E, Output = E> + ScalarMulAdd<T, E>,
    {
        let filtered_constraint = compiler.mul(constraint, self.lagrange_basis_first.clone());
        self.constraint(filtered_constraint, compiler);
    }

    /// Add one constraint, but first multiply it by a filter such that it will only apply to the
    /// last row of the trace.
    #[inline]
    pub fn constraint_last_row<COM>(&mut self, constraint: E, compiler: &mut COM)
    where
        T: Clone,
        E: Clone,
        COM: Mul<E, Output = E> + ScalarMulAdd<T, E>,
    {
        let filtered_constraint = compiler.mul(constraint, self.lagrange_basis_last.clone());
        self.constraint(filtered_constraint, compiler);
    }
}

///
pub type ConstraintConsumer<P> = Consumer<<P as PackedField>::Scalar, P>;

///
pub type RecursiveConstraintConsumer<const D: usize> = Consumer<Target, ExtensionTarget<D>>;
