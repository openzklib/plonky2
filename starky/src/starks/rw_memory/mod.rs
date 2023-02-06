//! STARK that checks the access trace of a read-write memory this can be thought of as a
//! form of "offline memory checking"

use crate::consumer::Compiler;
use crate::gate::{Gate, Read};
use crate::ir::Arithmetic;
use crate::permutation::PermutationPair;
use crate::stark::{StandardConsumer, Stark, StarkConfiguration};
use crate::starks::rw_memory::layout::{sorted_access_permutation_pairs, RwMemoryGate};

pub mod generation;
pub mod layout;

/// Read-Write Memory STARK
#[derive(Clone, Copy, Default)]
pub struct RwMemoryStark<const CHANNELS: usize>;

impl<const CHANNELS: usize> StarkConfiguration for RwMemoryStark<CHANNELS> {
    #[inline]
    fn columns(&self) -> usize {
        RwMemoryGate::<u8, CHANNELS>::SIZE
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

impl<F, C, COM, const CHANNELS: usize> Stark<F, C, COM> for RwMemoryStark<CHANNELS>
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
        let curr = RwMemoryGate::<F, CHANNELS>::read(&mut curr);
        let next = RwMemoryGate::<F, CHANNELS>::read(&mut next);
        RwMemoryGate::<F, CHANNELS>::eval(curr, next, public_inputs, &mut compiler)
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
    use crate::stark_testing::{test_stark_circuit_constraints, test_stark_low_degree};
    use crate::starks::rw_memory::generation::RwMemoryGenerator;
    use crate::verifier::verify_stark_proof_no_ctl;

    #[test]
    fn test_stark() -> Result<()> {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        type S = RwMemoryStark<1>;

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
        type S = RwMemoryStark<1>;

        let mut generator = RwMemoryGenerator::<F, 1>::new();
        let mut rng = rand::thread_rng();
        let addrs = 0..100;
        for addr in addrs.clone() {
            generator.gen_write(addr, F::ZERO, &[0])
        }

        for _ in 0..500 {
            let addr = rng.gen_range(addrs.clone());
            let is_write = rng.gen_bool(0.5);
            if is_write {
                let val = rng.gen::<u32>();
                generator.gen_write(addr, F::from_canonical_u32(val), &[0]);
            } else {
                generator.gen_read(addr, &[0]);
            }
        }

        let config = StarkConfig::standard_fast_config();
        let stark = S::default();
        let trace = generator.into_polynomial_values();
        let mut timing = TimingTree::default();
        let proof = prove_no_ctl::<F, C, S, D>(&stark, &config, &trace, vec![], &mut timing)?;
        verify_stark_proof_no_ctl(&stark, proof, &config)?;

        Ok(())
    }
}
