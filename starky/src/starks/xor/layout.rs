//! XOR Layout

pub struct Row<'t, T, const N: usize, const NUM_CHANNELS: usize> {
    pub a: &'t T,
    pub b: &'t T,
    pub output: &'t T,
    pub a_bits: &'t [T; N],
    pub b_bits: &'t [T; N],
    pub channel_filters: &'t [T; NUM_CHANNELS],
}

impl<'t, T, const N: usize, const NUM_CHANNELS: usize> From<&'t [T]>
    for Row<'t, T, N, NUM_CHANNELS>
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
