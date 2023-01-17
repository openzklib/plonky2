use alloc::vec;
use alloc::vec::Vec;

use plonky2::field::extension::{Extendable, FieldExtension};
use plonky2::field::packed::PackedField;
use plonky2::fri::structure::{
    FriBatchInfo, FriBatchInfoTarget, FriInstanceInfo, FriInstanceInfoTarget, FriOracleInfo,
    FriPolynomialInfo,
};
use plonky2::hash::hash_types::RichField;
use plonky2::iop::ext_target::ExtensionTarget;
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::util::ceil_div_usize;

use crate::config::StarkConfig;
use crate::constraint_consumer::{
    self, ConstraintCompiler, ConstraintConsumer, Consumer, RecursiveConstraintConsumer,
};
use crate::ir::Compiler;
use crate::permutation::PermutationPair;
use crate::vars::{StarkEvaluationTargets, StarkEvaluationVars};

/// STARK Configuration
pub trait StarkConfiguration {
    /// Returns the total number of columns in the trace.
    fn columns(&self) -> usize;

    /// Returns the number of public inputs.
    fn public_inputs(&self) -> usize;

    /// The maximum constraint degree.
    fn constraint_degree(&self) -> usize;

    /// Pairs of lists of columns that should be permutations of one another. A permutation argument
    /// will be used for each such pair. Empty by default.
    #[inline]
    fn permutation_pairs(&self) -> Vec<PermutationPair> {
        vec![]
    }

    /// Returns the [`StarkMetadata`] structure over `self`.
    #[inline]
    fn metadata(&self) -> StarkMetadata {
        StarkMetadata {
            constraint_degree: self.constraint_degree(),
            columns: self.columns(),
            public_inputs: self.public_inputs(),
            permutation_pairs: self.permutation_pairs().len(),
        }
    }
}

/// Represents a STARK system.
pub trait Stark<F: RichField + Extendable<D>, const D: usize>: StarkConfiguration {
    ///
    fn eval<T, COM>(&self, curr: &[T], next: &[T], public_inputs: &[T], compiler: &mut COM)
    where
        T: Copy,
        COM: Compiler<T>;

    /// Evaluate constraints at a vector of points.
    ///
    /// The points are elements of a field `FE`, a degree `D2` extension of `F`. This lets us
    /// evaluate constraints over a larger domain if desired. This can also be called with `FE = F`
    /// and `D2 = 1`, in which case we are using the trivial extension, i.e. just evaluating
    /// constraints over `F`.
    fn eval_packed_generic<FE, P, const D2: usize>(
        &self,
        vars: StarkEvaluationVars<P>,
        yield_constr: &mut ConstraintConsumer<P>,
    ) where
        FE: FieldExtension<D2, BaseField = F>,
        P: PackedField<Scalar = FE>,
    {
        self.eval(
            vars.local_values,
            vars.next_values,
            vars.public_inputs,
            &mut ConstraintCompiler::new(yield_constr, &mut ()),
        )
    }

    /// Evaluate constraints at a vector of points from the base field `F`.
    #[inline]
    fn eval_packed_base<P: PackedField<Scalar = F>>(
        &self,
        vars: StarkEvaluationVars<P>,
        yield_constr: &mut ConstraintConsumer<P>,
    ) {
        self.eval_packed_generic(vars, yield_constr)
    }

    /// Evaluate constraints at a single point from the degree `D` extension field.
    #[inline]
    fn eval_ext(
        &self,
        vars: StarkEvaluationVars<F::Extension>,
        yield_constr: &mut ConstraintConsumer<F::Extension>,
    ) {
        self.eval_packed_generic(vars, yield_constr)
    }

    /// Evaluate constraints at a vector of points from the degree `D` extension field. This is like
    /// `eval_ext`, except in the context of a recursive circuit.
    /// Note: constraints must be added through`yeld_constr.constraint(builder, constraint)` in the
    /// same order as they are given in `eval_packed_generic`.
    fn eval_ext_circuit(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        vars: StarkEvaluationTargets<D>,
        yield_constr: &mut RecursiveConstraintConsumer<D>,
    ) {
        self.eval(
            vars.local_values,
            vars.next_values,
            vars.public_inputs,
            &mut ConstraintCompiler::new(yield_constr, builder),
        )
    }
}

/// STARK Metadata
pub struct StarkMetadata {
    /// Constraint Degree
    pub constraint_degree: usize,

    /// Number of Columns
    pub columns: usize,

    /// Number of Public Inputs
    pub public_inputs: usize,

    /// Number of Permutation Pairs
    pub permutation_pairs: usize,
}

impl StarkMetadata {
    /// The maximum constraint degree.
    #[inline]
    pub fn quotient_degree_factor(&self) -> usize {
        1.max(self.constraint_degree - 1)
    }

    ///
    #[inline]
    pub fn num_quotient_polys(&self, config: &StarkConfig) -> usize {
        self.quotient_degree_factor() * config.num_challenges
    }

    /// The number of permutation argument instances that can be combined into a single constraint.
    #[inline]
    pub fn permutation_batch_size(&self) -> usize {
        // The permutation argument constraints look like
        //     Z(x) \prod(...) = Z(g x) \prod(...)
        // where each product has a number of terms equal to the batch size. So our batch size
        // should be one less than our constraint degree, which happens to be our quotient degree.
        self.quotient_degree_factor()
    }

    ///
    #[inline]
    pub fn uses_permutation_args(&self) -> bool {
        self.permutation_pairs == 0
    }

    ///
    #[inline]
    pub fn num_permutation_instances(&self, config: &StarkConfig) -> usize {
        self.permutation_pairs * config.num_challenges
    }

    ///
    #[inline]
    pub fn num_permutation_batches(&self, config: &StarkConfig) -> usize {
        ceil_div_usize(
            self.num_permutation_instances(config),
            self.permutation_batch_size(),
        )
    }

    /// Computes the FRI instance used to prove a STARK with this metadata.
    #[inline]
    pub fn fri_instance<F, const D: usize>(
        &self,
        zeta: F::Extension,
        g: F,
        config: &StarkConfig,
    ) -> FriInstanceInfo<F, D>
    where
        F: RichField + Extendable<D>,
    {
        let mut oracles = vec![];
        let trace_info = FriPolynomialInfo::from_range(oracles.len(), 0..self.columns);
        oracles.push(FriOracleInfo {
            num_polys: self.columns,
            blinding: false,
        });
        let permutation_zs_info = if self.uses_permutation_args() {
            let num_z_polys = self.num_permutation_batches(config);
            let polys = FriPolynomialInfo::from_range(oracles.len(), 0..num_z_polys);
            oracles.push(FriOracleInfo {
                num_polys: num_z_polys,
                blinding: false,
            });
            polys
        } else {
            vec![]
        };
        let num_quotient_polys = self.quotient_degree_factor() * config.num_challenges;
        let quotient_info = FriPolynomialInfo::from_range(oracles.len(), 0..num_quotient_polys);
        oracles.push(FriOracleInfo {
            num_polys: num_quotient_polys,
            blinding: false,
        });
        let zeta_batch = FriBatchInfo {
            point: zeta,
            polynomials: [
                trace_info.clone(),
                permutation_zs_info.clone(),
                quotient_info,
            ]
            .concat(),
        };
        let zeta_next_batch = FriBatchInfo {
            point: zeta.scalar_mul(g),
            polynomials: [trace_info, permutation_zs_info].concat(),
        };
        let batches = vec![zeta_batch, zeta_next_batch];
        FriInstanceInfo { oracles, batches }
    }

    /// Computes the FRI instance used to prove a STARK with this metadata.
    #[inline]
    pub fn fri_instance_target<F, const D: usize>(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        zeta: ExtensionTarget<D>,
        g: F,
        config: &StarkConfig,
    ) -> FriInstanceInfoTarget<D>
    where
        F: RichField + Extendable<D>,
    {
        let mut oracles = vec![];
        let trace_info = FriPolynomialInfo::from_range(oracles.len(), 0..self.columns);
        oracles.push(FriOracleInfo {
            num_polys: self.columns,
            blinding: false,
        });
        let permutation_zs_info = if self.uses_permutation_args() {
            let num_z_polys = self.num_permutation_batches(config);
            let polys = FriPolynomialInfo::from_range(oracles.len(), 0..num_z_polys);
            oracles.push(FriOracleInfo {
                num_polys: num_z_polys,
                blinding: false,
            });
            polys
        } else {
            vec![]
        };
        let num_quotient_polys = self.quotient_degree_factor() * config.num_challenges;
        let quotient_info = FriPolynomialInfo::from_range(oracles.len(), 0..num_quotient_polys);
        oracles.push(FriOracleInfo {
            num_polys: num_quotient_polys,
            blinding: false,
        });
        let zeta_batch = FriBatchInfoTarget {
            point: zeta,
            polynomials: [
                trace_info.clone(),
                permutation_zs_info.clone(),
                quotient_info,
            ]
            .concat(),
        };
        let zeta_next = builder.mul_const_extension(g, zeta);
        let zeta_next_batch = FriBatchInfoTarget {
            point: zeta_next,
            polynomials: [trace_info, permutation_zs_info].concat(),
        };
        let batches = vec![zeta_batch, zeta_next_batch];
        FriInstanceInfoTarget { oracles, batches }
    }
}
