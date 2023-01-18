use alloc::vec;
use alloc::vec::Vec;

use plonky2::field::extension::{Extendable, FieldExtension};
use plonky2::fri::structure::{
    FriBatchInfo, FriBatchInfoTarget, FriInstanceInfo, FriInstanceInfoTarget, FriOracleInfo,
    FriPolynomialInfo,
};
use plonky2::hash::hash_types::RichField;
use plonky2::iop::ext_target::ExtensionTarget;
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::util::ceil_div_usize;

use crate::config::StarkConfig;
use crate::consumer::{Compiler, Consumer, ConsumerCompiler, FilteredConsumer};
use crate::ir::{Arithmetic, FirstRow, LastRow, Registers, Transition};
use crate::permutation::PermutationPair;

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

/// Standard Consumer
pub trait StandardConsumer<F, COM = ()>:
    Consumer<F, COM>
    + FilteredConsumer<F, Transition, COM>
    + FilteredConsumer<F, FirstRow, COM>
    + FilteredConsumer<F, LastRow, COM>
{
}

impl<F, C, COM> StandardConsumer<F, COM> for C where
    C: Consumer<F, COM>
        + FilteredConsumer<F, Transition, COM>
        + FilteredConsumer<F, FirstRow, COM>
        + FilteredConsumer<F, LastRow, COM>
{
}

/// STARK Evaluator
pub trait Stark<F, C, COM = ()>: StarkConfiguration
where
    C: StandardConsumer<F, COM>,
    COM: Arithmetic<F>,
{
    /// Evaluates the STARK over `curr`, `next`, and `public_inputs`.
    fn eval(&self, curr: &[F], next: &[F], public_inputs: &[F], compiler: Compiler<C, COM>);

    /// Evaluates the STARK over `registers`, placing the constraints in the `consumer`
    #[inline]
    fn eval_with(&self, registers: Registers<F>, consumer: &mut C, compiler: &mut COM) {
        self.eval(
            registers.local_values,
            registers.next_values,
            registers.public_inputs,
            ConsumerCompiler::new(consumer, compiler),
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
