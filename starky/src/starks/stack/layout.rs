use core::mem::size_of;
use core::ops::Index;

use memoffset::offset_of;

use crate::gate::{Gate, Read};
use crate::ir::{Arithmetic, Assertions, Constraint};
use crate::stark::StandardConstraint;
use crate::starks::rw_memory::layout::RwMemoryGate;

// TODO: use crate::cross_table_lookup::{CtlColSet, TableID};

/// Stack Gate
#[repr(C)]
pub struct StackGate<T, const CHANNELS: usize> {
    /// Stack Pointer
    pub sp: T,

    /// Push/Pop Flag
    pub is_pop: T,

    /// Read/Write Memory Gate
    pub rw_memory: RwMemoryGate<T, CHANNELS>,
}

impl<T, const CHANNELS: usize> StackGate<T, CHANNELS> {
    /// Stack Gate Size
    pub const SIZE: usize = core::mem::size_of::<StackGate<u8, CHANNELS>>();

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

impl<T, const CHANNELS: usize> Default for StackGate<T, CHANNELS>
where
    T: Copy + Default,
    [T; StackGate::<T, CHANNELS>::SIZE]:,
{
    #[inline]
    fn default() -> Self {
        [Default::default(); Self::SIZE].into()
    }
}

impl<T, const CHANNELS: usize> From<StackGate<T, CHANNELS>> for [T; StackGate::<T, CHANNELS>::SIZE]
where
    [T; StackGate::<T, CHANNELS>::SIZE]:,
{
    #[inline]
    fn from(gate: StackGate<T, CHANNELS>) -> Self {
        unsafe { crate::util::transmute_no_compile_time_size_checks(gate) }
    }
}

impl<T, const CHANNELS: usize> From<[T; StackGate::<T, CHANNELS>::SIZE]> for StackGate<T, CHANNELS>
where
    [T; StackGate::<T, CHANNELS>::SIZE]:,
{
    #[inline]
    fn from(gate: [T; StackGate::<T, CHANNELS>::SIZE]) -> Self {
        unsafe { crate::util::transmute_no_compile_time_size_checks(gate) }
    }
}

impl<T, const CHANNELS: usize> Read<T> for StackGate<T, CHANNELS> {
    crate::impl_read_body!(T);
}

impl<T, const CHANNELS: usize, COM> Gate<T, COM> for StackGate<T, CHANNELS>
where
    T: Copy,
    COM: Arithmetic<T> + StandardConstraint<T>,
{
    #[inline]
    fn eval(curr: &Self, next: &Self, public_inputs: &[T], compiler: &mut COM) {
        let one = compiler.one();

        let is_push = compiler.sub(&one, &curr.is_pop);
        let sp_add_one = compiler.add(&curr.sp, &one);
        let sp_sub_one = compiler.sub(&curr.sp, &one);

        // Stack Semantics ===============================================================

        // Check that is_pop is binary (only operations are pop and push)
        compiler.assert_boolean(&curr.is_pop);

        // Check SP starts at 0.
        compiler.assert_zero_first_row(&curr.sp);

        // If the current operation is a pop, the following should be true:
        //
        // 1. addr should be sp - 1
        // 2. next sp should be sp - 1
        // 3. is_write should be 0
        //
        // A corrolary of this is stack underflows (pop when sp is 0) can't happen since
        // then the addresses wouldn't satisfy the continuity requirement.

        compiler
            .when(curr.is_pop)
            .assert_eq(&curr.rw_memory.addr, &sp_sub_one)
            .assert_eq_transition(&next.sp, &sp_sub_one)
            .assert_zero(&curr.rw_memory.is_write);

        // If the current operation is a push, the following should be true:
        // 1. addr should be sp
        // 2. next sp should be sp + 1
        // 3. is_write should be 1

        compiler
            .when(is_push)
            .assert_eq(&curr.rw_memory.addr, &curr.sp)
            .assert_eq_transition(&next.sp, &sp_add_one)
            .assert_one(&curr.rw_memory.is_write);

        // R/W Memory Semantics ==========================================================

        RwMemoryGate::eval(&curr.rw_memory, &next.rw_memory, public_inputs, compiler);
    }
}

pub fn sorted_access_permutation_pairs() -> Vec<(usize, usize)> {
    let offset = offset_of!(StackGate::<u8, 0>, rw_memory);
    crate::starks::rw_memory::layout::sorted_access_permutation_pairs()
        .into_iter()
        .map(|(l, r)| (l + offset, r + offset))
        .collect()
}

pub fn lookup_permutation_sets() -> Vec<(usize, usize, usize, usize)> {
    let offset = offset_of!(StackGate::<u8, 0>, rw_memory);
    crate::starks::rw_memory::layout::lookup_permutation_sets()
        .into_iter()
        .map(|(i, t, ip, tp)| (i + offset, t + offset, ip + offset, tp + offset))
        .collect()
}

/*
/// [is_pop, value, timestamp] for each channel
pub fn ctl_cols<const NUM_CHANNELS: usize>(tid: TableID) -> impl Iterator<Item = CtlColSet> {
    (0..NUM_CHANNELS).map(move |i| {
        CtlColSet::new(
            tid,
            vec![
                offset_of!(StackRow<u8, NUM_CHANNELS>, is_pop),
                offset_of!(StackRow<u8, NUM_CHANNELS>, value),
                offset_of!(StackRow<u8, NUM_CHANNELS>, timestamp),
            ],
            Some(offset_of!(StackRow<u8, NUM_CHANNELS>, filter_cols) + i),
        )
    })
}
*/
