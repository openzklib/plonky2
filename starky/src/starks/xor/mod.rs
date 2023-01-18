#![allow(clippy::reversed_empty_ranges)]

use std::borrow::Borrow;
use std::marker::PhantomData;

use itertools::Itertools;
use plonky2::field::extension::{Extendable, FieldExtension};
use plonky2::field::packed::PackedField;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::ext_target::ExtensionTarget;
use plonky2::plonk::circuit_builder::CircuitBuilder;

use self::layout::XorLayout;
use crate::consumer::basic::{ConstraintConsumer, RecursiveConstraintConsumer};
use crate::consumer::Compiler;
use crate::ir::Arithmetic;
use crate::stark::{StandardConsumer, Stark, StarkConfiguration};

pub mod generation;
pub mod layout;

/// N-bit XOR up to 63 bits;
#[derive(Default)]
pub struct XorStark<const N: usize, const NUM_CHANNELS: usize>;

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

macro_rules! impl_xor_stark_n {
    ($n:expr, $channels:expr) => {
        impl StarkConfiguration for XorStark<$n, $channels> {
            #[inline]
            fn columns(&self) -> usize {
                3 + 2 * $n + $channels
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

        impl<F, C, COM> Stark<F, C, COM> for XorStark<$n, $channels>
        where
            C: StandardConsumer<F, COM>,
            COM: Arithmetic<F>,
        {
            #[inline]
            fn eval(
                &self,
                curr: &[F],
                next: &[F],
                public_inputs: &[F],
                compiler: Compiler<C, COM>,
            ) {
                /*
                let row: &XorLayout<F, $n, $channels> = curr.borrow();

                let addends = (0..$n)
                    .map(|i| {
                        builder.mul_const_extension(F::from_canonical_u64(1 << i), row.a_bits[i])
                    })
                    .collect_vec();
                let mut c = builder.add_many_extension(addends);
                c = builder.sub_extension(row.a, c);
                yield_constr.constraint(builder, c);

                let addends = (0..$n)
                    .map(|i| {
                        builder.mul_const_extension(F::from_canonical_u64(1 << i), row.a_bits[i])
                    })
                    .collect_vec();
                let mut c = builder.add_many_extension(addends);
                c = builder.sub_extension(row.b, c);
                yield_constr.constraint(builder, c);

                let addends = (0..$n)
                    .map(|i| {
                        let xor = xor_gen_circuit(builder, row.a_bits[i], row.b_bits[i]);
                        builder.mul_const_extension(F::from_canonical_u64(1 << i), xor)
                    })
                    .collect_vec();
                let mut c = builder.add_many_extension(addends);
                c = builder.sub_extension(row.output, c);
                yield_constr.constraint(builder, c);

                let one_ext = builder.one_extension();
                for i in 0..$channels {
                    let mut c = builder.sub_extension(one_ext, row.channel_filters[i]);
                    c = builder.mul_extension(row.channel_filters[i], c);
                    yield_constr.constraint(builder, c);
                }

                for i in 0..$n {
                    let mut c = builder.sub_extension(one_ext, row.a_bits[i]);
                    c = builder.mul_extension(row.a_bits[i], c);
                    yield_constr.constraint(builder, c);

                    let mut c = builder.sub_extension(one_ext, row.b_bits[i]);
                    c = builder.mul_extension(row.b_bits[i], c);
                    yield_constr.constraint(builder, c);
                }
                */
            }
        }

        /*
        impl<F: RichField + Extendable<D>, const D: usize> Stark<F, D>
            for XorStark<D, $n, $channels>
        {
            fn eval_packed_generic<FE, P, const D2: usize>(
                &self,
                vars: StarkEvaluationVars<FE, P, { Self::COLUMNS }, { Self::PUBLIC_INPUTS }>,
                yield_constr: &mut ConstraintConsumer<P>,
            ) where
                FE: FieldExtension<D2, BaseField = F>,
                P: PackedField<Scalar = FE>,
            {
                let row: &XorLayout<P, $n, $channels> = vars.local_values.borrow();

                let c: P = (0..$n)
                    .map(|i| row.a_bits[i] * FE::from_canonical_u64(1 << i))
                    .sum();
                yield_constr.constraint(row.a - c);

                let c: P = (0..$n)
                    .map(|i| row.b_bits[i] * FE::from_canonical_u64(1 << i))
                    .sum();
                yield_constr.constraint(row.b - c);

                let c: P = (0..$n)
                    .map(|i| xor_gen(row.a_bits[i], row.b_bits[i]) * FE::from_canonical_u64(1 << i))
                    .sum();
                yield_constr.constraint(row.output - c);

                for i in 0..$channels {
                    yield_constr
                        .constraint(row.channel_filters[i] * (P::ONES - row.channel_filters[i]));
                }

                for i in 0..$n {
                    yield_constr.constraint(row.a_bits[i] * (P::ONES - row.a_bits[i]));
                    yield_constr.constraint(row.b_bits[i] * (P::ONES - row.b_bits[i]));
                }
            }

            fn eval_ext_circuit(
                &self,
                builder: &mut CircuitBuilder<F, D>,
                vars: StarkEvaluationTargets<D, { Self::COLUMNS }, { Self::PUBLIC_INPUTS }>,
                yield_constr: &mut RecursiveConstraintConsumer<F, D>,
            ) {
                let row: &XorLayout<ExtensionTarget<D>, $n, $channels> = vars.local_values.borrow();

                let addends = (0..$n)
                    .map(|i| {
                        builder.mul_const_extension(F::from_canonical_u64(1 << i), row.a_bits[i])
                    })
                    .collect_vec();
                let mut c = builder.add_many_extension(addends);
                c = builder.sub_extension(row.a, c);
                yield_constr.constraint(builder, c);

                let addends = (0..$n)
                    .map(|i| {
                        builder.mul_const_extension(F::from_canonical_u64(1 << i), row.a_bits[i])
                    })
                    .collect_vec();
                let mut c = builder.add_many_extension(addends);
                c = builder.sub_extension(row.b, c);
                yield_constr.constraint(builder, c);

                let addends = (0..$n)
                    .map(|i| {
                        let xor = xor_gen_circuit(builder, row.a_bits[i], row.b_bits[i]);
                        builder.mul_const_extension(F::from_canonical_u64(1 << i), xor)
                    })
                    .collect_vec();
                let mut c = builder.add_many_extension(addends);
                c = builder.sub_extension(row.output, c);
                yield_constr.constraint(builder, c);

                let one_ext = builder.one_extension();
                for i in 0..$channels {
                    let mut c = builder.sub_extension(one_ext, row.channel_filters[i]);
                    c = builder.mul_extension(row.channel_filters[i], c);
                    yield_constr.constraint(builder, c);
                }

                for i in 0..$n {
                    let mut c = builder.sub_extension(one_ext, row.a_bits[i]);
                    c = builder.mul_extension(row.a_bits[i], c);
                    yield_constr.constraint(builder, c);

                    let mut c = builder.sub_extension(one_ext, row.b_bits[i]);
                    c = builder.mul_extension(row.b_bits[i], c);
                    yield_constr.constraint(builder, c);
                }
            }
        }
        */
    };
}

macro_rules! impl_xor_starks_for_num_channels {
    ($channels:expr) => {
        impl_xor_stark_n!(1, $channels);
        impl_xor_stark_n!(2, $channels);
        impl_xor_stark_n!(3, $channels);
        impl_xor_stark_n!(4, $channels);
        impl_xor_stark_n!(5, $channels);
        impl_xor_stark_n!(6, $channels);
        impl_xor_stark_n!(7, $channels);
        impl_xor_stark_n!(8, $channels);
        impl_xor_stark_n!(9, $channels);
        impl_xor_stark_n!(10, $channels);
        impl_xor_stark_n!(11, $channels);
        impl_xor_stark_n!(12, $channels);
        impl_xor_stark_n!(13, $channels);
        impl_xor_stark_n!(14, $channels);
        impl_xor_stark_n!(15, $channels);
        impl_xor_stark_n!(16, $channels);
        impl_xor_stark_n!(17, $channels);
        impl_xor_stark_n!(18, $channels);
        impl_xor_stark_n!(19, $channels);
        impl_xor_stark_n!(20, $channels);
        impl_xor_stark_n!(21, $channels);
        impl_xor_stark_n!(22, $channels);
        impl_xor_stark_n!(23, $channels);
        impl_xor_stark_n!(24, $channels);
        impl_xor_stark_n!(25, $channels);
        impl_xor_stark_n!(26, $channels);
        impl_xor_stark_n!(27, $channels);
        impl_xor_stark_n!(28, $channels);
        impl_xor_stark_n!(29, $channels);
        impl_xor_stark_n!(30, $channels);
        impl_xor_stark_n!(31, $channels);
        impl_xor_stark_n!(32, $channels);
        impl_xor_stark_n!(33, $channels);
        impl_xor_stark_n!(34, $channels);
        impl_xor_stark_n!(35, $channels);
        impl_xor_stark_n!(36, $channels);
        impl_xor_stark_n!(37, $channels);
        impl_xor_stark_n!(38, $channels);
        impl_xor_stark_n!(39, $channels);
        impl_xor_stark_n!(40, $channels);
        impl_xor_stark_n!(41, $channels);
        impl_xor_stark_n!(42, $channels);
        impl_xor_stark_n!(43, $channels);
        impl_xor_stark_n!(44, $channels);
        impl_xor_stark_n!(45, $channels);
        impl_xor_stark_n!(46, $channels);
        impl_xor_stark_n!(47, $channels);
        impl_xor_stark_n!(48, $channels);
        impl_xor_stark_n!(49, $channels);
        impl_xor_stark_n!(50, $channels);
        impl_xor_stark_n!(51, $channels);
        impl_xor_stark_n!(52, $channels);
        impl_xor_stark_n!(53, $channels);
        impl_xor_stark_n!(54, $channels);
        impl_xor_stark_n!(55, $channels);
        impl_xor_stark_n!(56, $channels);
        impl_xor_stark_n!(57, $channels);
        impl_xor_stark_n!(58, $channels);
        impl_xor_stark_n!(59, $channels);
        impl_xor_stark_n!(60, $channels);
        impl_xor_stark_n!(61, $channels);
        impl_xor_stark_n!(62, $channels);
        impl_xor_stark_n!(63, $channels);
    };
}

impl_xor_starks_for_num_channels!(0);
impl_xor_starks_for_num_channels!(1);
impl_xor_starks_for_num_channels!(2);
impl_xor_starks_for_num_channels!(3);
impl_xor_starks_for_num_channels!(4);
// impl_xor_starks_for_num_channels!(5);
// impl_xor_starks_for_num_channels!(6);
// impl_xor_starks_for_num_channels!(7);
// impl_xor_starks_for_num_channels!(8);
// impl_xor_starks_for_num_channels!(9);
// impl_xor_starks_for_num_channels!(10);
// impl_xor_starks_for_num_channels!(11);
// impl_xor_starks_for_num_channels!(12);
// impl_xor_starks_for_num_channels!(13);
// impl_xor_starks_for_num_channels!(14);
// impl_xor_starks_for_num_channels!(15);
// impl_xor_starks_for_num_channels!(16);
// impl_xor_starks_for_num_channels!(17);
// impl_xor_starks_for_num_channels!(18);
// impl_xor_starks_for_num_channels!(19);
// impl_xor_starks_for_num_channels!(20);
// impl_xor_starks_for_num_channels!(21);
// impl_xor_starks_for_num_channels!(22);
// impl_xor_starks_for_num_channels!(23);
// impl_xor_starks_for_num_channels!(24);
// impl_xor_starks_for_num_channels!(25);
// impl_xor_starks_for_num_channels!(26);
// impl_xor_starks_for_num_channels!(27);
// impl_xor_starks_for_num_channels!(28);
// impl_xor_starks_for_num_channels!(29);
// impl_xor_starks_for_num_channels!(30);
// impl_xor_starks_for_num_channels!(31);
// impl_xor_starks_for_num_channels!(32);
// impl_xor_starks_for_num_channels!(33);
impl_xor_starks_for_num_channels!(34);
// impl_xor_starks_for_num_channels!(35);
// impl_xor_starks_for_num_channels!(36);
// impl_xor_starks_for_num_channels!(37);
// impl_xor_starks_for_num_channels!(38);
// impl_xor_starks_for_num_channels!(39);
// impl_xor_starks_for_num_channels!(40);
// impl_xor_starks_for_num_channels!(41);
// impl_xor_starks_for_num_channels!(42);
// impl_xor_starks_for_num_channels!(43);
// impl_xor_starks_for_num_channels!(44);
// impl_xor_starks_for_num_channels!(45);
// impl_xor_starks_for_num_channels!(46);
// impl_xor_starks_for_num_channels!(47);
// impl_xor_starks_for_num_channels!(48);
// impl_xor_starks_for_num_channels!(49);
// impl_xor_starks_for_num_channels!(50);
// impl_xor_starks_for_num_channels!(51);
// impl_xor_starks_for_num_channels!(52);
// impl_xor_starks_for_num_channels!(53);
// impl_xor_starks_for_num_channels!(54);
// impl_xor_starks_for_num_channels!(55);
// impl_xor_starks_for_num_channels!(56);
// impl_xor_starks_for_num_channels!(57);
// impl_xor_starks_for_num_channels!(58);
// impl_xor_starks_for_num_channels!(59);
// impl_xor_starks_for_num_channels!(60);
// impl_xor_starks_for_num_channels!(61);
// impl_xor_starks_for_num_channels!(62);
// impl_xor_starks_for_num_channels!(63);
// impl_xor_starks_for_num_channels!(64);

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
