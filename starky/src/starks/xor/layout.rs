use std::borrow::{Borrow, BorrowMut};
use std::mem::transmute;

use crate::util::transmute_no_compile_time_size_checks;

pub struct XorRow<'t, T, const N: usize, const NUM_CHANNELS: usize> {
    pub a: &'t T,
    pub b: &'t T,
    pub output: &'t T,
    pub a_bits: &'t [T; N],
    pub b_bits: &'t [T; N],
    pub channel_filters: &'t [T; NUM_CHANNELS],
}

impl<'t, T, const N: usize, const NUM_CHANNELS: usize> From<&'t [T]>
    for XorRow<'t, T, N, NUM_CHANNELS>
{
    #[inline]
    fn from(slice: &'t [T]) -> Self {
        Self {
            a: &slice[0],
            b: &slice[1],
            output: &slice[2],
            a_bits: (&slice[3..(N + 3)]).try_into().expect(""),
            b_bits: (&slice[(N + 3)..(2 * N + 3)]).try_into().expect(""),
            channel_filters: (&slice[(2 * N + 3)..(2 * N + 3 + NUM_CHANNELS)])
                .try_into()
                .expect(""),
        }
    }
}

/*

#[repr(C)]
#[derive(Eq, PartialEq, Debug)]
pub struct XorLayout<T: Copy, const N: usize, const NUM_CHANNELS: usize> {
    pub(crate) a: T,
    pub(crate) b: T,
    pub(crate) output: T,
    pub(crate) a_bits: [T; N],
    pub(crate) b_bits: [T; N],
    pub(crate) channel_filters: [T; NUM_CHANNELS],
}

impl<T: Copy, const N: usize, const NUM_CHANNELS: usize> XorLayout<T, N, NUM_CHANNELS> {
    pub(crate) const fn a_col() -> usize {
        0
    }

    pub(crate) const fn b_col() -> usize {
        1
    }

    pub(crate) const fn output_col() -> usize {
        2
    }

    pub(crate) const fn channel_filter_col(channel: usize) -> usize {
        3 + 2 * N + channel
    }

    /* TODO:
    pub fn ctl_cols_a(tid: TableID) -> impl Iterator<Item = CtlColSet> {
        (0..NUM_CHANNELS).map(move |i| {
            CtlColSet::new(tid, vec![Self::a_col()], Some(Self::channel_filter_col(i)))
        })
    }

    pub fn ctl_cols_b(tid: TableID) -> impl Iterator<Item = CtlColSet> {
        (0..NUM_CHANNELS).map(move |i| {
            CtlColSet::new(tid, vec![Self::b_col()], Some(Self::channel_filter_col(i)))
        })
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
}

impl<T: Copy, const N: usize, const NUM_CHANNELS: usize> From<[T; 3 + 2 * N + NUM_CHANNELS]>
    for XorLayout<T, N, NUM_CHANNELS>
{
    fn from(row: [T; 3 + 2 * N + NUM_CHANNELS]) -> Self {
        unsafe { transmute_no_compile_time_size_checks(row) }
    }
}

impl<T: Copy, const N: usize, const NUM_CHANNELS: usize> From<XorLayout<T, N, NUM_CHANNELS>>
    for [T; 3 + 2 * N + NUM_CHANNELS]
{
    fn from(value: XorLayout<T, N, NUM_CHANNELS>) -> Self {
        unsafe { transmute_no_compile_time_size_checks(value) }
    }
}

impl<T: Copy, const N: usize, const NUM_CHANNELS: usize> Borrow<XorLayout<T, N, NUM_CHANNELS>>
    for [T; 3 + 2 * N + NUM_CHANNELS]
{
    fn borrow(&self) -> &XorLayout<T, N, NUM_CHANNELS> {
        unsafe { transmute(self) }
    }
}

impl<T: Copy, const N: usize, const NUM_CHANNELS: usize> BorrowMut<XorLayout<T, N, NUM_CHANNELS>>
    for [T; 3 + 2 * N + NUM_CHANNELS]
{
    fn borrow_mut(&mut self) -> &mut XorLayout<T, N, NUM_CHANNELS> {
        unsafe { transmute(self) }
    }
}

*/
