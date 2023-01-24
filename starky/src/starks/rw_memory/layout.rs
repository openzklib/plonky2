use core::borrow::{Borrow, BorrowMut};
use core::mem::{size_of, transmute};
use core::ops::Index;

use memoffset::offset_of;

// use crate::cross_table_lookup::{CtlColSet, TableID};
use crate::util::transmute_no_compile_time_size_checks;

///
pub struct RwMemoryRow<'t, T, const NUM_CHANNELS: usize> {
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

    // fitler cols for each lookup channel
    // >1 channel can be helpful when a STARK only wants to read part of the memory
    pub filter_cols: &'t [T; NUM_CHANNELS],
}

impl<'t, T, const NUM_CHANNELS: usize> From<&'t [T]> for RwMemoryRow<'t, T, NUM_CHANNELS> {
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
            filter_cols: (&slice[11..11 + NUM_CHANNELS]).try_into().expect(""),
        }
    }
}

impl<'t, T, const NUM_CHANNELS: usize> Index<usize> for RwMemoryRow<'t, T, NUM_CHANNELS> {
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
            _ => &self.filter_cols[index - 11],
        }
    }
}

/*

#[repr(C)]
#[derive(Eq, PartialEq, Debug)]
pub struct RwMemoryRow<T: Copy, const NUM_CHANNELS: usize> {
    // memory cols
    pub addr: T,
    pub timestamp: T,
    pub value: T,
    pub is_write: T,

    pub addr_sorted: T,
    pub timestamp_sorted: T,
    pub value_sorted: T,
    pub is_write_sorted: T,

    // used for checking timestamp ordering via range check
    pub timestamp_sorted_diff: T,
    pub timestamp_sorted_diff_permuted: T,

    // used to range check addresses and timestamp differenes
    pub timestamp_permuted: T,

    // fitler cols for each lookup channel
    // >1 channel can be helpful when a STARK only wants to read part of the memory
    pub filter_cols: [T; NUM_CHANNELS],
}
*/

pub(crate) fn sorted_access_permutation_pairs() -> Vec<(usize, usize)> {
    type R = RwMemoryRow<'static, u8, 0>;
    vec![
        (offset_of!(R, addr), offset_of!(R, addr_sorted)),
        (offset_of!(R, timestamp), offset_of!(R, timestamp_sorted)),
        (offset_of!(R, value), offset_of!(R, value_sorted)),
        (offset_of!(R, is_write), offset_of!(R, is_write_sorted)),
    ]
}

pub(crate) fn lookup_permutation_sets() -> Vec<(usize, usize, usize, usize)> {
    vec![(
        offset_of!(RwMemoryRow<u8, 0>, timestamp_sorted_diff),
        offset_of!(RwMemoryRow<u8, 0>, timestamp),
        offset_of!(RwMemoryRow<u8, 0>, timestamp_sorted_diff_permuted),
        offset_of!(RwMemoryRow<u8, 0>, timestamp_permuted),
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

pub(crate) const RW_MEMORY_NUM_COLS_BASE: usize = size_of::<RwMemoryRow<u8, 0>>();
