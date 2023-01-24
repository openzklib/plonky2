/// STARK that checks the access trace of a stack
/// this can be thought of as a form of "offline memory checking"
use std::borrow::Borrow;
use std::marker::PhantomData;

use plonky2::field::extension::{Extendable, FieldExtension};
use plonky2::field::packed::PackedField;
use plonky2::hash::hash_types::RichField;
use plonky2::plonk::circuit_builder::CircuitBuilder;

use crate::consumer::Compiler;
use crate::ir::{Add, Arithmetic, Assertions, Constraint, Mul, One, Sub};
use crate::lookup::eval_lookups;
use crate::permutation::PermutationPair;
use crate::stark::{StandardConsumer, Stark, StarkConfiguration};
use crate::starks::stack::layout::{
    sorted_access_permutation_pairs, StackRow, STACK_NUM_COLS_BASE,
};

// TODO: pub mod generation;
pub mod layout;

#[derive(Default)]
pub struct StackStark<const NUM_CHANNELS: usize>;

impl<const NUM_CHANNELS: usize> StarkConfiguration for StackStark<NUM_CHANNELS> {
    #[inline]
    fn columns(&self) -> usize {
        STACK_NUM_COLS_BASE + NUM_CHANNELS
    }

    #[inline]
    fn public_inputs(&self) -> usize {
        0
    }

    #[inline]
    fn constraint_degree(&self) -> usize {
        3
    }

    #[inline]
    fn permutation_pairs(&self) -> Vec<PermutationPair> {
        vec![PermutationPair {
            column_pairs: sorted_access_permutation_pairs(),
        }]
    }
}

impl<F, C, COM, const NUM_CHANNELS: usize> Stark<F, C, COM> for StackStark<NUM_CHANNELS>
where
    F: Copy,
    C: StandardConsumer<F, COM>,
    COM: Arithmetic<F>,
{
    #[inline]
    fn eval(&self, curr: &[F], next: &[F], public_inputs: &[F], mut compiler: Compiler<C, COM>) {
        let _ = public_inputs;
        let curr = StackRow::<F, NUM_CHANNELS>::from(curr);
        let next = StackRow::<F, NUM_CHANNELS>::from(next);

        let one = compiler.one();

        let is_push = compiler.sub(one, *curr.is_pop);
        let sp_add_one = compiler.add(*curr.sp, one);
        let sp_sub_one = compiler.sub(*curr.sp, one);

        /* FIXME: Embedd RW-Memory STARK */

        // STACK SEMANTICS

        // check that is_pop is binary (only operations are pop and push)
        compiler.assert_boolean(*curr.is_pop);

        // check SP starts at 0
        compiler.assert_zero_first_row(*curr.sp);

        // if the current operation is a pop, the following should be true:
        //
        // 1. addr should be sp - 1
        // 2. next sp should be sp - 1
        // 3. is_write should be 0
        //
        // a corrolary of this is stack underflows (pop when sp is 0) can't
        // happen since then the addresses wouldn't satisfy the continuity requirement.

        compiler
            .when(*curr.is_pop)
            .assert_eq(*curr.addr, sp_sub_one)
            .assert_eq_transition(*next.sp, sp_sub_one)
            .assert_zero(*curr.is_write);

        // if the current operation is a push, the following should be true:
        // 1. addr should be sp
        // 2. next sp should be sp + 1
        // 3. is_write should be 1

        compiler
            .when(is_push)
            .assert_eq(*curr.addr, *curr.sp)
            .assert_eq_transition(*next.sp, sp_add_one)
            .assert_one(*curr.is_write);
    }
}

#[cfg(test)]
mod tests {
    use anyhow::Result;
    use plonky2::field::types::Field;
    use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
    use plonky2::util::timing::TimingTree;
    use rand::Rng;

    use super::*;
    use crate::config::StarkConfig;
    use crate::prover::prove_no_ctl;
    use crate::stark_testing::test_stark_low_degree;
    use crate::starky2lib::stack::generation::StackGenerator;
    use crate::verifier::verify_stark_proof_no_ctl;

    #[test]
    fn test_stark_degree() -> Result<()> {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        type S = StackStark<F, D, 1>;

        let stark = S::new();
        test_stark_low_degree(stark)
    }

    #[test]
    fn test_random_trace() -> Result<()> {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        type S = StackStark<F, D, 1>;

        let mut generator = StackGenerator::<F, 1>::new();
        let mut rng = rand::thread_rng();
        let mut height = 0;
        for i in 0..500 {
            let is_pop = if height == 0 {
                false
            } else {
                rng.gen_range(0..2) == 1
            };

            if is_pop {
                height -= 1;
                generator.gen_pop(&[]);
            } else {
                height += 1;
                let value = F::rand_from_rng(&mut rng);
                generator.gen_push(value, &[]);
            }
        }

        let config = StarkConfig::standard_fast_config();
        let stark = S::new();
        let trace = generator.into_polynomial_values();
        let mut timing = TimingTree::default();
        let proof = prove_no_ctl::<F, C, S, D>(&stark, &config, &trace, [], &mut timing)?;
        verify_stark_proof_no_ctl(&stark, &proof, &config)?;

        Ok(())
    }
}
