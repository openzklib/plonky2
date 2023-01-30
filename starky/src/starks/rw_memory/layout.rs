//! RW Memory STARK Layout

use core::ops::Index;

use memoffset::offset_of;

use crate::gate::{Gate, Read};
use crate::ir::{Arithmetic, Assertions};
use crate::lookup::assert_lookup;
use crate::stark::StandardConstraint;

// TODO: use crate::cross_table_lookup::{CtlColSet, TableID};

/// Read/Write Memory Gate
#[derive(Clone, Debug)]
#[repr(C)]
pub struct RwMemoryGate<T, const CHANNELS: usize> {
    /// Address
    pub addr: T,

    /// Sorted Address
    pub addr_sorted: T,

    /// Value
    pub value: T,

    /// Sorted Values
    pub value_sorted: T,

    /// Read/Write Flag
    pub is_write: T,

    /// Sorted Read/Write Flag
    pub is_write_sorted: T,

    /// Sorted Timestamp
    pub timestamp_sorted: T,

    /// Timestamp
    pub timestamp: T,

    /// Used to range check addresses and timestamp differenes
    pub timestamp_permuted: T,

    /// Used for checking timestamp ordering via range check
    pub timestamp_sorted_diff: T,

    /// Used for checking timestamp ordering via range check
    pub timestamp_sorted_diff_permuted: T,

    /// Filter columns for each lookup channel
    ///
    /// `>1` channel can be helpful when a STARK only wants to read part of the memory
    pub filter_cols: [T; CHANNELS],
}

impl<T, const CHANNELS: usize> RwMemoryGate<T, CHANNELS> {
    /// Gate Size
    pub const SIZE: usize = core::mem::size_of::<RwMemoryGate<u8, CHANNELS>>();

    ///
    #[inline]
    pub fn borrow(slice: &[T; Self::SIZE]) -> &Self {
        unsafe { crate::util::transmute_no_compile_time_size_checks(slice) }
    }

    ///
    #[inline]
    pub fn borrow_mut(slice: &mut [T; Self::SIZE]) -> &mut Self {
        unsafe { crate::util::transmute_no_compile_time_size_checks(slice) }
    }
}

impl<T, const CHANNELS: usize> Default for RwMemoryGate<T, CHANNELS>
where
    T: Copy + Default,
    [T; RwMemoryGate::<T, CHANNELS>::SIZE]:,
{
    #[inline]
    fn default() -> Self {
        [Default::default(); Self::SIZE].into()
    }
}

impl<T, const CHANNELS: usize> From<RwMemoryGate<T, CHANNELS>>
    for [T; RwMemoryGate::<T, CHANNELS>::SIZE]
where
    [T; RwMemoryGate::<T, CHANNELS>::SIZE]:,
{
    #[inline]
    fn from(gate: RwMemoryGate<T, CHANNELS>) -> Self {
        unsafe { crate::util::transmute_no_compile_time_size_checks(gate) }
    }
}

impl<T, const CHANNELS: usize> From<[T; RwMemoryGate::<T, CHANNELS>::SIZE]>
    for RwMemoryGate<T, CHANNELS>
where
    [T; RwMemoryGate::<T, CHANNELS>::SIZE]:,
{
    #[inline]
    fn from(gate: [T; RwMemoryGate::<T, CHANNELS>::SIZE]) -> Self {
        unsafe { crate::util::transmute_no_compile_time_size_checks(gate) }
    }
}

impl<T, const CHANNELS: usize> Read<T> for RwMemoryGate<T, CHANNELS> {
    crate::impl_read_body!(T);
}

impl<T, const CHANNELS: usize> Index<usize> for RwMemoryGate<T, CHANNELS> {
    type Output = T;

    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        const SIZE: usize = core::mem::size_of::<RwMemoryGate<u8, 0>>();
        let array: &[T; SIZE] = unsafe { crate::util::transmute_no_compile_time_size_checks(self) };
        &array[index]
    }
}

impl<T, const CHANNELS: usize, COM> Gate<T, COM> for RwMemoryGate<T, CHANNELS>
where
    T: Copy,
    COM: Arithmetic<T> + StandardConstraint<T>,
{
    #[inline]
    fn eval(curr: &Self, next: &Self, _: &[T], compiler: &mut COM) {
        let one = compiler.one();

        let address_changed = compiler.sub(&next.addr_sorted, &curr.addr_sorted);
        let timestamp_changed = compiler.sub(&next.timestamp_sorted, &curr.timestamp_sorted);

        let address_unchanged = compiler.sub(&one, &address_changed);

        // TYPE CHECKS ===================================================================

        // Check that is_write is binary.
        compiler.assert_boolean(&curr.is_write);
        compiler.assert_boolean(&curr.is_write_sorted);

        // ADDRESSES =====================================================================

        // Check that sorted addresses are monotonic, continuous, and start at 0.
        //
        // We do this by ensuring either the sorted address increases by 0 or 1 at each curr_row and at
        // the first curr_row, the sorted addr is 0.

        compiler.assert_zero_first_row(&curr.addr_sorted);
        compiler.assert_zero_product_transition(&address_changed, &address_unchanged);

        // TIMESTAMPS ====================================================================

        // Check timestamps are increasing using a range check.
        //
        // This works as follows:
        // 1. Range check every timestamp to be in [1..num_rows].
        // 2. Range check the *difference* between the current and next timestamp to be in
        //    [1..num_rows] if address hasn't changed (i.e. we only care about timestamps for
        //    a particular address)
        // 3. This is enough. Let x, y be subsequent timestamps for a given address. x, y, and
        //    y - x are all in [1..num_rows]. Suppose "x > y" in the field. Then y - x > num_rows -><-
        //
        // This argument works as long as the number of rows is less than half of the field order, which
        // is very true for this library because we can only use up to 2^TWO_ADICITY rows and this is
        // usually far below the field size.
        //
        // We do this by enforcing the "unsorted" timestamps start at 1 and increment by 1 each row.
        // Then we apply a lookup against that col to check that the timestamp diffs are in [1..num_rows]
        // since timestamp_sorted is a permutation of timestamp, timestamp_sorted is guaranteed to be in
        // that range lookups are applied at the end of this function.

        compiler
            .when(address_unchanged)
            .assert_eq_transition(&next.timestamp_sorted_diff, &timestamp_changed);

        // Set the timestamp difference to 1 if the address changed as a dummy to indicate we don't care
        // (our range check doesn't include 0 because timestamps have to be unique).

        compiler
            .when(address_changed)
            .assert_eq_transition(&next.timestamp_sorted_diff, &one);

        // Check that "unsorted" timestamps start at 1 and increment by 1 each curr_row.

        compiler.assert_eq_first_row(&curr.timestamp, &one);
        compiler.assert_increments_by(&curr.timestamp, &next.timestamp, &one);

        // MEMORY TRACE ==================================================================

        // Check that the sorted memory trace is valid.
        //
        // To do this, we check the following at each step:
        // 1. If the address has changed, the memory trace is valid at this step
        // 2. If the address has not changed and the current operation is a write, the memory trace is
        //    valid at this step
        // 3. If the address has not changed and the current operation is a read, the memory trace is
        //    valid at this step iff the value is the same

        let next_is_not_write = compiler.sub(&one, &next.is_write_sorted);

        compiler
            .when_all([address_unchanged, next_is_not_write])
            .assert_eq_transition(&next.value_sorted, &curr.value_sorted);

        // LOOKUPS =======================================================================

        for (_, _, permuted_input, permuted_table) in lookup_permutation_sets() {
            assert_lookup(
                &curr[permuted_input],
                &next[permuted_input],
                &next[permuted_table],
                compiler,
            );
        }
    }
}

pub fn sorted_access_permutation_pairs() -> Vec<(usize, usize)> {
    type R = RwMemoryGate<u8, 0>;
    vec![
        (offset_of!(R, addr), offset_of!(R, addr_sorted)),
        (offset_of!(R, value), offset_of!(R, value_sorted)),
        (offset_of!(R, is_write), offset_of!(R, is_write_sorted)),
        (offset_of!(R, timestamp), offset_of!(R, timestamp_sorted)),
    ]
}

pub fn lookup_permutation_sets() -> Vec<(usize, usize, usize, usize)> {
    vec![(
        offset_of!(RwMemoryGate<u8, 0>, timestamp_sorted_diff),
        offset_of!(RwMemoryGate<u8, 0>, timestamp),
        offset_of!(RwMemoryGate<u8, 0>, timestamp_sorted_diff_permuted),
        offset_of!(RwMemoryGate<u8, 0>, timestamp_permuted),
    )]
}

/*
/// [is_write, addr, value, timestamp] for each channel
pub fn ctl_cols<const NUM_CHANNELS: usize>(tid: TableID) -> impl Iterator<Item = CtlColSet> {
    type R = RwMemoryRow<u8, 0>;
    (0..NUM_CHANNELS).map(move |i| {
        CtlColSet::new(
            tid,
            vec![
                offset_of!(R, is_write),
                offset_of!(R, addr),
                offset_of!(R, value),
                offset_of!(R, timestamp),
            ],
            Some(RW_MEMORY_NUM_COLS_BASE - (NUM_CHANNELS - i)),
        )
    })
}
*/
