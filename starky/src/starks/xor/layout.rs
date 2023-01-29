//! XOR Layout

use crate::gate::{Gate, Read};
use crate::ir::{Arithmetic, Assertions, Constraint};
use crate::stark::StandardConstraint;

/// Bits Values
#[repr(C)]
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
#[repr(C)]
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
    /// Row Size
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
