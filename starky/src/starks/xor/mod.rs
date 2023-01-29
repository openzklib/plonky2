//! XOR STARK

use crate::consumer::Compiler;
use crate::gate::{Gate, Input, Read};
use crate::ir::{Arithmetic, Assertions};
use crate::stark::{StandardConsumer, Stark, StarkConfiguration};
use crate::starks::xor::layout::Row;

pub mod generation;
pub mod layout;

/// N-bit XOR up to 63 bits;
#[derive(Copy, Clone, Default)]
pub struct XorStark<const N: usize, const CHANNELS: usize>;

impl<const N: usize, const CHANNELS: usize> StarkConfiguration for XorStark<N, CHANNELS> {
    #[inline]
    fn columns(&self) -> usize {
        Row::<(), N, CHANNELS>::SIZE
    }

    #[inline]
    fn public_inputs(&self) -> usize {
        0
    }

    #[inline]
    fn constraint_degree(&self) -> usize {
        3
    }
}

impl<F, C, COM, const N: usize, const CHANNELS: usize> Stark<F, C, COM> for XorStark<N, CHANNELS>
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
        Row::<F, N, CHANNELS>::read_eval(&mut curr, &mut next, public_inputs, &mut compiler);
    }
}

#[cfg(test)]
mod tests {
    use anyhow::Result;
    use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
    use plonky2::util::timing::TimingTree;
    use rand::Rng;

    use super::generation::Generator;
    use super::*;
    use crate::config::StarkConfig;
    use crate::prover::prove;
    use crate::stark_testing::{test_stark_circuit_constraints, test_stark_low_degree};
    use crate::verifier::verify_stark_proof;

    macro_rules! test_xor {
        ($n:expr, $fn_name:ident) => {
            paste::item! {
                #[test]
                fn [<$fn_name>] () -> Result<()> {
                    const D: usize = 2;
                    type C = PoseidonGoldilocksConfig;
                    type F = <C as GenericConfig<D>>::F;
                    type S = XorStark<$n, 1>;

                    let config = StarkConfig::standard_fast_config();
                    let stark = S::default();
                    let metadata = stark.metadata();
                    test_stark_low_degree::<F, _, D>(stark, metadata.columns, metadata.public_inputs)?;
                    test_stark_circuit_constraints::<F, C, S, D>(
                        stark,
                        metadata.columns,
                        metadata.public_inputs,
                    )?;

                    let mut rng = rand::thread_rng();
                    let mut generator = Generator::<F, $n, 1>::new();
                    for _ in 0..32 {
                        let a = rng.gen_range(0..(1 << $n));
                        let b = rng.gen_range(0..(1 << $n));
                        generator.gen_op(a, b, 0);
                    }

                    let trace = generator.into_polynomial_values();
                    let mut timing = TimingTree::default();
                    let proof = prove::<F, C, S, D>(stark, &config, trace, vec![], &mut timing)?;
                    verify_stark_proof(stark, proof, &config)
                }
            }
        };
    }

    test_xor!(1, test_xor_1);
    test_xor!(2, test_xor_2);
    test_xor!(4, test_xor_4);
    test_xor!(12, test_xor_12);
    test_xor!(16, test_xor_16);
    test_xor!(32, test_xor_32);
    test_xor!(63, test_xor_63);
}
