use core::borrow::{Borrow, BorrowMut};
use core::mem::{size_of, transmute};
use core::ops::Index;

use memoffset::offset_of;

// use crate::cross_table_lookup::{CtlColSet, TableID};
use crate::util::transmute_no_compile_time_size_checks;

///
pub struct StackRow<'t, T, const NUM_CHANNELS: usize> {
    // memory cols
    pub addr: &'t T,
    pub timestamp: &'t T,
    pub value: &'t T,
    pub is_write: &'t T,

    pub addr_sorted: &'t T,
    pub timestamp_sorted: &'t T,
    pub value_sorted: &'t T,
    pub is_write_sorted: &'t T,

    // used for checking timestamp ordering via range check
    pub timestamp_sorted_diff: &'t T,
    pub timestamp_sorted_diff_permuted: &'t T,

    // used to range check addresses and timestamp differenes
    pub timestamp_permuted: &'t T,

    pub sp: &'t T,
    // 1 if the current operation is a pop, 0 if it's a push
    pub is_pop: &'t T,

    // fitler cols for each lookup channel
    // >1 channel can be helpful when a STARK only wants to read part of the memory
    pub filter_cols: &'t [T; NUM_CHANNELS],
}

impl<'t, T, const NUM_CHANNELS: usize> From<&'t [T]> for StackRow<'t, T, NUM_CHANNELS> {
    #[inline]
    fn from(slice: &'t [T]) -> Self {
        Self {
            addr: &slice[0],
            timestamp: &slice[1],
            value: &slice[2],
            is_write: &slice[3],
            addr_sorted: &slice[4],
            timestamp_sorted: &slice[5],
            value_sorted: &slice[6],
            is_write_sorted: &slice[7],
            timestamp_sorted_diff: &slice[8],
            timestamp_sorted_diff_permuted: &slice[9],
            timestamp_permuted: &slice[10],
            sp: &slice[11],
            is_pop: &slice[12],
            filter_cols: (&slice[13..13 + NUM_CHANNELS]).try_into().expect(""),
        }
    }
}

impl<'t, T, const NUM_CHANNELS: usize> Index<usize> for StackRow<'t, T, NUM_CHANNELS> {
    type Output = T;

    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        match index {
            0 => self.addr,
            1 => self.timestamp,
            2 => self.value,
            3 => self.is_write,
            4 => self.addr_sorted,
            5 => self.timestamp_sorted,
            6 => self.value_sorted,
            7 => self.is_write_sorted,
            8 => self.timestamp_sorted_diff,
            9 => self.timestamp_sorted_diff_permuted,
            10 => self.timestamp_permuted,
            11 => self.sp,
            12 => self.is_pop,
            _ => &self.filter_cols[index - 13],
        }
    }
}

/*
#[repr(C)]
#[derive(Eq, PartialEq, Debug)]
pub struct StackRow<T: Copy, const NUM_CHANNELS: usize> {
    // memory cols
    pub(crate) addr: T,
    pub(crate) timestamp: T,
    pub(crate) value: T,
    pub(crate) is_write: T,

    pub(crate) addr_sorted: T,
    pub(crate) timestamp_sorted: T,
    pub(crate) value_sorted: T,
    pub(crate) is_write_sorted: T,

    // used for checking timestamp ordering via range check
    pub(crate) timestamp_sorted_diff: T,
    pub(crate) timestamp_sorted_diff_permuted: T,

    pub(crate) sp: T,
    // 1 if the current operation is a pop, 0 if it's a push
    pub(crate) is_pop: T,

    // used to range check addresses and timestamp differenes
    pub(crate) timestamp_permuted: T,

    // fitler cols for each lookup channel
    // >1 channel can be helpful when a STARK only wants to read part of the memory
    pub(crate) filter_cols: [T; NUM_CHANNELS],
}
*/

pub(crate) fn sorted_access_permutation_pairs() -> Vec<(usize, usize)> {
    vec![
        (
            offset_of!(StackRow<u8, 0>, addr),
            offset_of!(StackRow<u8, 0>, addr_sorted),
        ),
        (
            offset_of!(StackRow<u8, 0>, timestamp),
            offset_of!(StackRow<u8, 0>, timestamp_sorted),
        ),
        (
            offset_of!(StackRow<u8, 0>, value),
            offset_of!(StackRow<u8, 0>, value_sorted),
        ),
        (
            offset_of!(StackRow<u8, 0>, is_write),
            offset_of!(StackRow<u8, 0>, is_write_sorted),
        ),
    ]
}

pub(crate) fn lookup_permutation_sets() -> Vec<(usize, usize, usize, usize)> {
    vec![(
        offset_of!(StackRow<u8, 0>, timestamp_sorted_diff),
        offset_of!(StackRow<u8, 0>, timestamp),
        offset_of!(StackRow<u8, 0>, timestamp_sorted_diff_permuted),
        offset_of!(StackRow<u8, 0>, timestamp_permuted),
    )]
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

pub(crate) const STACK_NUM_COLS_BASE: usize = size_of::<StackRow<u8, 0>>();
