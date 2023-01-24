#![allow(clippy::reversed_empty_ranges)]

use std::borrow::Borrow;
use std::marker::PhantomData;

use itertools::Itertools;
use plonky2::field::extension::{Extendable, FieldExtension};
use plonky2::field::packed::PackedField;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::ext_target::ExtensionTarget;
use plonky2::plonk::circuit_builder::CircuitBuilder;

use crate::consumer::basic::{ConstraintConsumer, RecursiveConstraintConsumer};
use crate::consumer::Compiler;
use crate::ir::{Add, Arithmetic, Assertions, Constant, Constraint, Mul, Sub};
use crate::stark::{StandardConsumer, Stark, StarkConfiguration};
use crate::starks::xor::layout::XorRow;

// TODO: pub mod generation;
pub mod layout;

/// N-bit XOR up to 63 bits;
#[derive(Default)]
pub struct XorStark<const N: usize, const NUM_CHANNELS: usize>;

/*
/// Computes the arithmetic generalization of `xor(x, y)`, i.e. `x + y - 2 x y`.
pub(crate) fn xor_gen<P: PackedField>(x: P, y: P) -> P {
    x + y - x * y.doubles()
}

/// Computes the arithmetic generalization of `xor(x, y)`, i.e. `x + y - 2 x y`.
pub(crate) fn xor_gen_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    x: ExtensionTarget<D>,
    y: ExtensionTarget<D>,
) -> ExtensionTarget<D> {
    let sum = builder.add_extension(x, y);
    builder.arithmetic_extension(-F::TWO, F::ONE, x, y, sum)
}
*/

impl<const N: usize, const NUM_CHANNELS: usize> StarkConfiguration for XorStark<N, NUM_CHANNELS> {
    #[inline]
    fn columns(&self) -> usize {
        3 + 2 * N + NUM_CHANNELS
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

impl<F, C, COM, const N: usize, const NUM_CHANNELS: usize> Stark<F, C, COM>
    for XorStark<N, NUM_CHANNELS>
where
    F: Copy,
    C: StandardConsumer<F, COM>,
    COM: Arithmetic<F>,
{
    #[inline]
    fn eval(&self, curr: &[F], next: &[F], public_inputs: &[F], mut compiler: Compiler<C, COM>) {
        let _ = (next, public_inputs);
        let row = XorRow::<F, N, NUM_CHANNELS>::from(curr);

        compiler.assert_bit_decomposition(*row.a, *row.a_bits);
        compiler.assert_bit_decomposition(*row.b, *row.b_bits);

        let output_bits = (0..N)
            .map(|i| compiler.xor(row.a_bits[i], row.b_bits[i]))
            .collect::<Vec<_>>();
        compiler.assert_bit_decomposition(*row.output, output_bits);

        for i in 0..NUM_CHANNELS {
            compiler.assert_boolean(row.channel_filters[i]);
        }
    }
}

#[cfg(test)]
mod tests {
    use anyhow::Result;
    use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
    use plonky2::util::timing::TimingTree;
    use rand::Rng;

    use super::generation::XorGenerator;
    use super::*;
    use crate::config::StarkConfig;
    use crate::prover::prove;
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

                    let mut rng = rand::thread_rng();
                    let mut generator = XorGenerator::<F, $n, 1>::new();
                    for _ in 0..32 {
                        let a = rng.gen_range(0..(1 << $n));
                        let b = rng.gen_range(0..(1 << $n));
                        generator.gen_op(a, b, 0);
                    }

                    let config = StarkConfig::standard_fast_config();
                    let stark = S::default();
                    let trace = generator.into_polynomial_values();
                    let mut timing = TimingTree::default();
                    let proof = prove::<F, C, S, D>(&stark, &config, &trace, [], &mut timing)?;
                    verify_stark_proof(&stark, proof, &config)
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
    test_xor!(63, test_xor_64);
}
