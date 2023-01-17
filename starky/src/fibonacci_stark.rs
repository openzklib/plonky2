//! Fibonacci STARK

use alloc::vec;
use alloc::vec::Vec;
use core::marker::PhantomData;

use plonky2::field::extension::{Extendable, FieldExtension};
use plonky2::field::packed::PackedField;
use plonky2::field::polynomial::PolynomialValues;
use plonky2::hash::hash_types::RichField;
use plonky2::plonk::circuit_builder::CircuitBuilder;

use crate::constraint_consumer::{self, ConstraintConsumer, Consumer, RecursiveConstraintConsumer};
use crate::ir::{Compiler, Eval};
use crate::permutation::PermutationPair;
use crate::stark::{Stark, StarkConfiguration};
use crate::util::trace_rows_to_poly_values;
use crate::vars::{StarkEvaluationTargets, StarkEvaluationVars};

/// Toy STARK system used for testing.
///
/// Computes a Fibonacci sequence with state `[x0, x1, i, j]` using the state transition
/// `x0' <- x1, x1' <- x0 + x1, i' <- i+1, j' <- j+1`.
/// Note: The `i, j` columns are only used to test the permutation argument.
#[derive(Copy, Clone)]
pub struct FibonacciStark {
    pub num_rows: usize,
}

impl FibonacciStark {
    /// The first public input is `x0`.
    pub const PI_INDEX_X0: usize = 0;

    /// The second public input is `x1`.
    pub const PI_INDEX_X1: usize = 1;

    /// The third public input is the second element of the last row, which should be equal to the
    /// `num_rows`-th Fibonacci number.
    pub const PI_INDEX_RES: usize = 2;

    /// Builds a new [`FibonacciStark`].
    #[inline]
    pub fn new(num_rows: usize) -> Self {
        Self { num_rows }
    }

    /// Generate the trace using `x0, x1, 0, 1` as initial state values.
    fn generate_trace<F>(&self, x0: F, x1: F) -> Vec<PolynomialValues<F>>
    where
        F: RichField,
    {
        let mut trace_rows = (0..self.num_rows)
            .scan([x0, x1, F::ZERO, F::ONE], |acc, _| {
                let tmp = *acc;
                acc[0] = tmp[1];
                acc[1] = tmp[0] + tmp[1];
                acc[2] = tmp[2] + F::ONE;
                acc[3] = tmp[3] + F::ONE;
                Some(tmp)
            })
            .collect::<Vec<_>>();
        trace_rows[self.num_rows - 1][3] = F::ZERO; // So that column 2 and 3 are permutation of one another.
        trace_rows_to_poly_values(trace_rows)
    }
}

impl StarkConfiguration for FibonacciStark {
    #[inline]
    fn columns(&self) -> usize {
        4
    }

    #[inline]
    fn public_inputs(&self) -> usize {
        3
    }

    #[inline]
    fn constraint_degree(&self) -> usize {
        2
    }

    #[inline]
    fn permutation_pairs(&self) -> Vec<PermutationPair> {
        vec![PermutationPair::singletons(2, 3)]
    }
}

impl<F, COM> Eval<F, COM> for FibonacciStark
where
    F: Copy,
    COM: Compiler<F>,
{
    #[inline]
    fn eval(&self, curr: &[F], next: &[F], public_inputs: &[F], compiler: &mut COM) {
        // Constrain Public Inputs
        compiler.assert_eq_first_row(public_inputs[Self::PI_INDEX_X0], curr[0]);
        compiler.assert_eq_first_row(public_inputs[Self::PI_INDEX_X1], curr[1]);
        compiler.assert_eq_last_row(public_inputs[Self::PI_INDEX_RES], curr[1]);

        // Add Fibonacci Terms
        let sum = compiler.add(curr[0], curr[1]);

        // Constrain Transition
        compiler.assert_eq_transition(next[0], curr[1]);
        compiler.assert_eq_transition(next[1], sum);
    }
}

impl<F: RichField + Extendable<D>, const D: usize> Stark<F, D> for FibonacciStark {
    #[inline]
    fn eval_packed_generic<FE, P, const D2: usize>(
        &self,
        vars: StarkEvaluationVars<P>,
        yield_constr: &mut ConstraintConsumer<P>,
    ) where
        FE: FieldExtension<D2, BaseField = F>,
        P: PackedField<Scalar = FE>,
    {
        /* TODO:
        self.eval(
            vars.local_values,
            vars.next_values,
            vars.public_inputs,
            ConstraintCompiler(yield_constr),
        );
        */
        todo!()
    }

    #[inline]
    fn eval_ext_circuit(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        vars: StarkEvaluationTargets<D>,
        yield_constr: &mut RecursiveConstraintConsumer<D>,
    ) {
        /* TODO:
        self.eval(
            vars.local_values,
            vars.next_values,
            vars.public_inputs,
            RecursiveConstraintCompiler::new(yield_constr, builder),
        );
        */
    }
}

#[cfg(test)]
mod tests {
    use anyhow::Result;
    use plonky2::field::types::Field;
    use plonky2::iop::witness::PartialWitness;
    use plonky2::plonk::circuit_data::CircuitConfig;
    use plonky2::plonk::config::{AlgebraicHasher, GenericConfig, PoseidonGoldilocksConfig};
    use plonky2::util::timing::TimingTree;

    use super::*;
    use crate::config::StarkConfig;
    use crate::proof::StarkProofWithPublicInputs;
    use crate::prover::prove;
    use crate::recursive_verifier::{
        add_virtual_stark_proof_with_pis, set_stark_proof_with_pis_target,
        verify_stark_proof_circuit,
    };
    use crate::stark_testing::{test_stark_circuit_constraints, test_stark_low_degree};
    use crate::verifier::verify_stark_proof;

    fn fibonacci<F: Field>(n: usize, x0: F, x1: F) -> F {
        (0..n).fold((x0, x1), |x, _| (x.1, x.0 + x.1)).1
    }

    #[test]
    fn test_fibonacci_stark() -> Result<()> {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        type S = FibonacciStark;

        let config = StarkConfig::standard_fast_config();
        let num_rows = 1 << 5;
        let public_inputs = vec![F::ZERO, F::ONE, fibonacci(num_rows - 1, F::ZERO, F::ONE)];
        let stark = S::new(num_rows);
        let trace = stark.generate_trace(public_inputs[0], public_inputs[1]);
        let proof = prove::<F, C, S, D>(
            stark,
            &config,
            trace,
            public_inputs,
            &mut TimingTree::default(),
        )?;

        verify_stark_proof(stark, proof, &config)
    }

    #[test]
    fn test_fibonacci_stark_degree() -> Result<()> {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        type S = FibonacciStark;

        let num_rows = 1 << 5;
        let stark = S::new(num_rows);
        let metadata = stark.metadata();
        test_stark_low_degree::<F, _, D>(stark, metadata.columns, metadata.public_inputs)
    }

    #[test]
    fn test_fibonacci_stark_circuit() -> Result<()> {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        type S = FibonacciStark;

        let num_rows = 1 << 5;
        let stark = S::new(num_rows);
        let metadata = stark.metadata();
        test_stark_circuit_constraints::<F, C, S, D>(
            stark,
            metadata.columns,
            metadata.public_inputs,
        )
    }

    #[test]
    fn test_recursive_stark_verifier() -> Result<()> {
        init_logger();
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        type S = FibonacciStark;

        let config = StarkConfig::standard_fast_config();
        let num_rows = 1 << 5;
        let public_inputs = vec![F::ZERO, F::ONE, fibonacci(num_rows - 1, F::ZERO, F::ONE)];
        let stark = S::new(num_rows);
        let trace = stark.generate_trace(public_inputs[0], public_inputs[1]);
        let proof = prove::<F, C, S, D>(
            stark,
            &config,
            trace,
            public_inputs,
            &mut TimingTree::default(),
        )?;
        verify_stark_proof(stark, proof.clone(), &config)?;

        recursive_proof::<F, C, S, C, D>(stark, proof, &config, true)
    }

    fn recursive_proof<
        F: RichField + Extendable<D>,
        C: GenericConfig<D, F = F>,
        S: Stark<F, D> + Copy,
        InnerC: GenericConfig<D, F = F>,
        const D: usize,
    >(
        stark: S,
        inner_proof: StarkProofWithPublicInputs<F, InnerC, D>,
        inner_config: &StarkConfig,
        print_gate_counts: bool,
    ) -> Result<()>
    where
        InnerC::Hasher: AlgebraicHasher<F>,
    {
        let circuit_config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(circuit_config);
        let mut pw = PartialWitness::new();
        let degree_bits = inner_proof.proof.recover_degree_bits(inner_config);
        let pt = add_virtual_stark_proof_with_pis(&mut builder, stark, inner_config, degree_bits);
        set_stark_proof_with_pis_target(&mut pw, &pt, &inner_proof);

        verify_stark_proof_circuit::<F, InnerC, S, D>(&mut builder, stark, pt, inner_config);

        if print_gate_counts {
            builder.print_gate_counts(0);
        }

        let data = builder.build::<C>();
        let proof = data.prove(pw)?;
        data.verify(proof)
    }

    fn init_logger() {
        let _ = env_logger::builder().format_timestamp(None).try_init();
    }
}
