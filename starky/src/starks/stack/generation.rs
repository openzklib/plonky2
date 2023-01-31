//! Stack Gate Generator

use itertools::Itertools;
use plonky2::field::polynomial::PolynomialValues;
use plonky2::field::types::{Field, PrimeField64};
use plonky2::util::log2_ceil;

use crate::lookup::assign_lookup_table;
use crate::starks::stack::layout::lookup_permutation_sets;
use crate::starks::stack::StackGate;
use crate::util::trace_rows_to_poly_values;

/// Stack Generator
pub struct StackGenerator<F: Field, const CHANNELS: usize>
where
    [(); StackGate::<F, CHANNELS>::SIZE]:,
{
    timestamp: u64,
    stack: Vec<F>,
    trace: Vec<[F; StackGate::<F, CHANNELS>::SIZE]>,
}

#[derive(Copy, Clone, Debug)]
pub enum StackOp<F: Field> {
    Push(F),
    Pop(F),
}

impl<F: PrimeField64, const CHANNELS: usize> Default for StackGenerator<F, CHANNELS>
where
    [(); StackGate::<F, CHANNELS>::SIZE]:,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<F: PrimeField64, const CHANNELS: usize> StackGenerator<F, CHANNELS>
where
    [(); StackGate::<F, CHANNELS>::SIZE]:,
{
    pub fn new() -> Self {
        Self {
            timestamp: 1,
            trace: Vec::new(),
            stack: Vec::new(),
        }
    }

    // TODO: don't panic, define error type instead
    pub fn gen_ops(&mut self, ops: &[StackOp<F>], channels: &[usize]) {
        for &op in ops {
            match op {
                StackOp::Push(val) => {
                    self.gen_push(val, channels);
                }
                StackOp::Pop(val) => {
                    let correct_val = self.gen_pop(channels);
                    assert_eq!(correct_val, val);
                }
            }
        }
    }

    pub fn gen_push(&mut self, value: F, channels: &[usize]) {
        let mut row = StackGate {
            is_pop: F::ZERO,
            sp: F::from_canonical_u64(self.stack.len() as u64),
            ..Default::default()
        };

        row.rw_memory.timestamp = F::from_canonical_u64(self.timestamp);
        row.rw_memory.addr = F::from_canonical_u64(self.stack.len() as u64);
        row.rw_memory.value = value;
        row.rw_memory.is_write = F::ONE;

        Self::gen_channel_filters(&mut row, channels);

        self.stack.push(value);
        self.trace.push(row.into());
        self.timestamp += 1;
    }

    pub fn gen_pop(&mut self, channels: &[usize]) -> F {
        let mut row = StackGate::<F, CHANNELS>::default();
        let sp = self.stack.len() as u64;
        let value = self.stack.pop().expect("stack underflow");

        row.is_pop = F::ONE;
        row.sp = F::from_canonical_u64(sp);

        row.rw_memory.timestamp = F::from_canonical_u64(self.timestamp);
        row.rw_memory.addr = F::from_canonical_u64(self.stack.len() as u64);
        row.rw_memory.value = value;
        row.rw_memory.is_write = F::ZERO;

        Self::gen_channel_filters(&mut row, channels);

        self.trace.push(row.into());
        self.timestamp += 1;
        value
    }

    fn gen_channel_filters(row: &mut StackGate<F, CHANNELS>, channels: &[usize]) {
        for &channel in channels {
            debug_assert!(channel < CHANNELS);
            row.rw_memory.filter_cols[channel] = F::ONE;
        }
    }

    fn gen_sorted(&mut self) {
        let sorted_accesses = self
            .trace
            .iter()
            .map(|row_arr| {
                let row = StackGate::<F, CHANNELS>::borrow(row_arr);
                let addr = row.rw_memory.addr.to_canonical_u64();
                let timestamp = row.rw_memory.timestamp.to_canonical_u64();
                let value = row.rw_memory.value;
                let is_write = row.rw_memory.is_write;
                (addr, timestamp, value, is_write)
            })
            .sorted_by_cached_key(|(addr, timestamp, _, _)| (*addr, *timestamp));
        let mut prev_timestamp = None;
        let mut prev_addr = F::ZERO;
        for (i, (addr, timestamp, value, is_write)) in sorted_accesses.enumerate() {
            let row = StackGate::<F, CHANNELS>::borrow_mut(&mut self.trace[i]);
            row.rw_memory.addr_sorted = F::from_canonical_u64(addr);
            row.rw_memory.timestamp_sorted = F::from_canonical_u64(timestamp);
            row.rw_memory.value_sorted = value;
            row.rw_memory.is_write_sorted = is_write;
            (row.rw_memory.timestamp_sorted_diff, prev_timestamp) = match prev_timestamp {
                None => (F::ONE, Some(row.rw_memory.timestamp_sorted)),
                Some(prev) => {
                    if prev_addr == row.rw_memory.addr_sorted {
                        let diff = row.rw_memory.timestamp_sorted - prev;
                        (diff, Some(row.rw_memory.timestamp_sorted))
                    } else {
                        (F::ONE, Some(row.rw_memory.timestamp_sorted))
                    }
                }
            };
            prev_addr = row.rw_memory.addr_sorted;
        }
    }

    fn gen_luts(columns: &mut [PolynomialValues<F>]) {
        for (input, table, input_permuted, table_permuted) in lookup_permutation_sets() {
            assign_lookup_table(input, table, input_permuted, table_permuted, columns);
        }
    }

    fn pad_to_len(&mut self, log2_target_len: usize) {
        let target_len = 1 << (log2_ceil(self.trace.len()).max(log2_target_len));
        while self.trace.len() < target_len {
            self.gen_push(F::ZERO, &[]);
        }
    }

    pub fn into_polynomial_values_of_target_degree(
        mut self,
        log2_target_degree: usize,
    ) -> Vec<PolynomialValues<F>> {
        self.pad_to_len(log2_target_degree);
        self.gen_sorted();
        let mut values = trace_rows_to_poly_values(self.trace);
        Self::gen_luts(&mut values);
        values
    }

    pub fn into_polynomial_values(self) -> Vec<PolynomialValues<F>> {
        self.into_polynomial_values_of_target_degree(0)
    }
}
