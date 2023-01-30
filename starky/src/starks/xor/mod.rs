//! XOR STARK

use plonky2::field::polynomial::PolynomialValues;
use plonky2::field::types::PrimeField64;
use plonky2::util::log2_ceil;

use crate::consumer::Compiler;
use crate::gate::{Gate, Read};
use crate::ir::{Arithmetic, Assertions, Constraint};
use crate::stark::{StandardConstraint, StandardConsumer, Stark, StarkConfiguration};
use crate::util::{is_power_of_two, trace_rows_to_poly_values};

/// Bits Values
pub struct Bits<T, const N: usize> {
    /// Value
    pub value: T,

    /// Bit Decomposition
    pub bits: [T; N],
}

impl<T, const N: usize> Bits<T, N> {
    /// Asserts that `self` is a valid bit-decomposition.
    #[inline]
    pub fn assert_valid<COM>(&self, compiler: &mut COM)
    where
        COM: Arithmetic<T> + Constraint<T>,
    {
        compiler.assert_bit_decomposition(&self.value, &self.bits);
    }
}

impl<T, const N: usize> Default for Bits<T, N>
where
    T: Copy + Default,
{
    #[inline]
    fn default() -> Self {
        Self {
            value: Default::default(),
            bits: [Default::default(); N],
        }
    }
}

/// XOR Row
pub struct Row<T, const N: usize, const CHANNELS: usize> {
    /// LHS Input
    pub lhs: Bits<T, N>,

    /// RHS Input
    pub rhs: Bits<T, N>,

    /// XOR Output
    pub output: T,

    /// Channel Filters
    pub channel_filters: [T; CHANNELS],
}

impl<T, const N: usize, const CHANNELS: usize> Row<T, N, CHANNELS> {
    /// Gate Size
    pub const SIZE: usize = core::mem::size_of::<Row<u8, N, CHANNELS>>();
}

impl<T, const N: usize, const CHANNELS: usize> From<Row<T, N, CHANNELS>>
    for [T; Row::<T, N, CHANNELS>::SIZE]
{
    #[inline]
    fn from(row: Row<T, N, CHANNELS>) -> Self {
        unsafe { crate::util::transmute_no_compile_time_size_checks(row) }
    }
}

impl<T, const N: usize, const CHANNELS: usize> Default for Row<T, N, CHANNELS>
where
    T: Copy + Default,
{
    #[inline]
    fn default() -> Self {
        Self {
            lhs: Default::default(),
            rhs: Default::default(),
            output: Default::default(),
            channel_filters: [Default::default(); CHANNELS],
        }
    }
}

impl<T, const N: usize, const CHANNELS: usize> Read<T> for Row<T, N, CHANNELS> {
    crate::impl_read_body!(T);
}

impl<T, const N: usize, const CHANNELS: usize, COM> Gate<T, COM> for Row<T, N, CHANNELS>
where
    COM: Arithmetic<T> + StandardConstraint<T>,
{
    #[inline]
    fn eval(row: &Self, _: &Self, _: &[T], compiler: &mut COM) {
        row.lhs.assert_valid(compiler);
        row.rhs.assert_valid(compiler);

        let output_bits = (0..N)
            .map(|i| compiler.xor(&row.lhs.bits[i], &row.rhs.bits[i]))
            .collect::<Vec<_>>();

        // NOTE: If we use `assert_bit_decomposition` the degree is too high.
        compiler.assert_bit_decomposition_with_unchecked_bits(&row.output, output_bits);

        for i in 0..CHANNELS {
            compiler.assert_boolean(&row.channel_filters[i]);
        }
    }
}

/* TODO:
pub fn ctl_cols_a(tid: TableID) -> impl Iterator<Item = CtlColSet> {
    (0..NUM_CHANNELS)
        .map(move |i| CtlColSet::new(tid, vec![Self::a_col()], Some(Self::channel_filter_col(i))))
}

pub fn ctl_cols_b(tid: TableID) -> impl Iterator<Item = CtlColSet> {
    (0..NUM_CHANNELS)
        .map(move |i| CtlColSet::new(tid, vec![Self::b_col()], Some(Self::channel_filter_col(i))))
}

pub fn ctl_cols_output(tid: TableID) -> impl Iterator<Item = CtlColSet> {
    (0..NUM_CHANNELS).map(move |i| {
        CtlColSet::new(
            tid,
            vec![Self::output_col()],
            Some(Self::channel_filter_col(i)),
        )
    })
}
*/

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

/// XOR Stark Generator
#[derive(Debug, Default)]
pub struct Generator<F: PrimeField64, const N: usize, const CHANNELS: usize>
where
    [(); Row::<F, N, CHANNELS>::SIZE]:,
{
    pub trace: Vec<[F; Row::<F, N, CHANNELS>::SIZE]>,
}

impl<F: PrimeField64, const N: usize, const CHANNELS: usize> Generator<F, N, CHANNELS>
where
    [(); Row::<F, N, CHANNELS>::SIZE]:,
{
    #[inline]
    pub fn new() -> Self {
        Self { trace: Vec::new() }
    }

    pub fn gen_op(&mut self, mut a: u64, mut b: u64, channel: usize) {
        debug_assert!(log2_ceil(a as usize) <= 1 << N, "a too large");
        debug_assert!(log2_ceil(b as usize) <= 1 << N, "b too large");

        let mut row = Row::<F, N, CHANNELS>::default();

        row.lhs.value = F::from_canonical_u64(a);
        row.rhs.value = F::from_canonical_u64(b);
        row.output = F::from_canonical_u64(a ^ b);

        if CHANNELS > 0 {
            assert!(channel < CHANNELS);
            row.channel_filters[channel] = F::ONE;
        }

        for i in 0..N {
            row.lhs.bits[i] = F::from_canonical_u64(a & 1);
            row.rhs.bits[i] = F::from_canonical_u64(b & 1);
            a >>= 1;
            b >>= 1;
        }

        self.trace.push(row.into());
    }

    pub fn into_polynomial_values(mut self) -> Vec<PolynomialValues<F>> {
        if !is_power_of_two(self.trace.len() as u64) {
            let next_power_of_two = self.trace.len().next_power_of_two();
            self.trace
                .resize(next_power_of_two, [F::ZERO; Row::<F, N, CHANNELS>::SIZE]);
        }
        trace_rows_to_poly_values(self.trace)
    }
}

#[cfg(test)]
mod tests {
    use anyhow::Result;
    use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
    use plonky2::util::timing::TimingTree;
    use rand::Rng;

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
