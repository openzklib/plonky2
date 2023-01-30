//! STARK that checks the access trace of a stack
//! this can be thought of as a form of "offline memory checking"

use crate::consumer::Compiler;
use crate::gate::{Gate, Read};
use crate::ir::{Add, Arithmetic, Assertions, Constraint, One, Sub};
use crate::permutation::PermutationPair;
use crate::stark::{StandardConsumer, Stark, StarkConfiguration};
use crate::starks::stack::layout::{sorted_access_permutation_pairs, StackGate};

pub mod generation;
pub mod layout;

#[derive(Clone, Copy, Default, Eq, Hash, PartialEq)]
pub struct StackStark<const CHANNELS: usize>;

impl<const CHANNELS: usize> StarkConfiguration for StackStark<CHANNELS> {
    #[inline]
    fn columns(&self) -> usize {
        StackGate::<u8, CHANNELS>::SIZE
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

impl<F, C, COM, const CHANNELS: usize> Stark<F, C, COM> for StackStark<CHANNELS>
where
    F: Copy,
    C: StandardConsumer<F, COM>,
    COM: Arithmetic<F>,
{
    #[inline]
    fn eval(
        &self,
        mut curr: &[F],
        mut next: &[F],
        public_inputs: &[F],
        mut compiler: Compiler<C, COM>,
    ) {
        let curr = StackGate::<F, CHANNELS>::read(&mut curr);
        let next = StackGate::<F, CHANNELS>::read(&mut next);
        StackGate::eval(curr, next, public_inputs, &mut compiler);
    }
}

#[cfg(test)]
mod tests {
    use anyhow::Result;
    use plonky2::field::types::{Field, Sample};
    use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
    use plonky2::util::timing::TimingTree;
    use rand::Rng;

    use super::*;
    use crate::config::StarkConfig;
    use crate::prover::prove;
    use crate::stark_testing::{test_stark_circuit_constraints, test_stark_low_degree};
    use crate::starks::stack::generation::StackGenerator;
    use crate::verifier::verify_stark_proof;

    #[test]
    fn test_stark_degree() -> Result<()> {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        type S = StackStark<1>;

        let stark = S::default();
        let metadata = stark.metadata();
        test_stark_low_degree::<F, S, D>(stark, metadata.columns, metadata.public_inputs)?;
        test_stark_circuit_constraints::<F, C, S, D>(
            stark,
            metadata.columns,
            metadata.public_inputs,
        )?;
        Ok(())
    }

    #[test]
    fn test_random_trace() -> Result<()> {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        type S = StackStark<1>;

        let mut generator = StackGenerator::<F, 1>::new();
        let mut rng = rand::thread_rng();
        let mut height = 0;
        for _ in 0..500 {
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
                let value = F::sample(&mut rng);
                generator.gen_push(value, &[]);
            }
        }

        let config = StarkConfig::standard_fast_config();
        let stark = S::default();
        let trace = generator.into_polynomial_values();
        let mut timing = TimingTree::default();
        let proof = prove::<F, C, S, D>(stark, &config, trace, vec![], &mut timing)?;
        verify_stark_proof(stark, proof, &config)?;

        Ok(())
    }
}
