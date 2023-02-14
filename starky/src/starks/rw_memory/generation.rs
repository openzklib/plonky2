//! Read/Write Generator

use itertools::Itertools;
use plonky2::field::polynomial::PolynomialValues;
use plonky2::field::types::{Field, PrimeField64};
use plonky2::util::log2_ceil;

use crate::lookup::assign_lookup_table;
use crate::starks::rw_memory::layout::{lookup_permutation_sets, RwMemoryGate};
use crate::util::trace_rows_to_poly_values;

///
pub struct RwMemoryGenerator<F: Field, const CHANNELS: usize>
where
    [(); RwMemoryGate::<F, CHANNELS>::SIZE]:,
{
    timestamp: u64,
    mem: Vec<Option<F>>,
    trace: Vec<[F; RwMemoryGate::<F, CHANNELS>::SIZE]>,
}

#[derive(Copy, Clone, Debug)]
pub enum MemOp<F: Field> {
    Read(usize),
    Write(usize, F),
}

impl<F: PrimeField64, const CHANNELS: usize> Default for RwMemoryGenerator<F, CHANNELS>
where
    [(); RwMemoryGate::<F, CHANNELS>::SIZE]:,
{
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<F: PrimeField64, const CHANNELS: usize> RwMemoryGenerator<F, CHANNELS>
where
    [(); RwMemoryGate::<F, CHANNELS>::SIZE]:,
{
    pub fn new() -> Self {
        Self {
            timestamp: 1,
            trace: Vec::new(),
            mem: Vec::new(),
        }
    }

    // TODO: don't panic, define error type instead
    pub fn gen_ops(&mut self, ops: &[MemOp<F>], channels: &[usize]) {
        for &op in ops {
            match op {
                MemOp::Read(addr) => {
                    self.gen_read(addr, channels);
                }
                MemOp::Write(addr, val) => self.gen_write(addr, val, channels),
            }
        }
    }

    fn read_from_mem(&mut self, addr: usize) -> F {
        if addr >= self.mem.len() {
            panic!("attempted to read from uninitialized memory")
        }
        self.mem[addr].expect("attempted to read from uninitialized memory")
    }

    pub fn gen_read(&mut self, addr: usize, channels: &[usize]) -> F {
        let mut row = RwMemoryGate::<F, CHANNELS>::default();

        let value = self.read_from_mem(addr);
        row.timestamp = F::from_canonical_u64(self.timestamp);
        row.addr = F::from_canonical_u64(addr as u64);
        row.value = value;
        row.is_write = F::ZERO;

        self.timestamp += 1;

        Self::gen_channel_filters(&mut row, channels);
        self.trace.push(row.into());

        value
    }

    fn write_to_mem(&mut self, addr: usize, val: F) {
        if addr >= self.mem.len() {
            self.mem.resize(addr + 1, None);
        }
        self.mem[addr] = Some(val);
    }

    pub fn gen_write(&mut self, addr: usize, value: F, channels: &[usize]) {
        let mut row = RwMemoryGate {
            timestamp: F::from_canonical_u64(self.timestamp),
            addr: F::from_canonical_u64(addr as u64),
            value,
            is_write: F::ONE,
            ..Default::default()
        };
        self.write_to_mem(addr, value);
        self.timestamp += 1;

        Self::gen_channel_filters(&mut row, channels);
        self.trace.push(row.into());
    }

    fn gen_channel_filters(row: &mut RwMemoryGate<F, CHANNELS>, channels: &[usize]) {
        for &channel in channels {
            debug_assert!(channel < CHANNELS);
            row.filter_cols[channel] = F::ONE;
        }
    }

    fn gen_sorted(&mut self) {
        let sorted_accesses = self
            .trace
            .iter()
            .map(|row_arr| {
                let row = RwMemoryGate::<F, CHANNELS>::borrow(row_arr);
                let addr = row.addr.to_canonical_u64();
                let timestamp = row.timestamp.to_canonical_u64();
                let value = row.value;
                let is_write = row.is_write;
                (addr, timestamp, value, is_write)
            })
            .sorted_by_cached_key(|(addr, timestamp, _, _)| (*addr, *timestamp));
        let mut prev_timestamp = None;
        let mut prev_addr = F::ZERO;
        for (i, (addr, timestamp, value, is_write)) in sorted_accesses.enumerate() {
            let row = RwMemoryGate::<F, CHANNELS>::borrow_mut(&mut self.trace[i]);
            row.addr_sorted = F::from_canonical_u64(addr);
            row.timestamp_sorted = F::from_canonical_u64(timestamp);
            row.value_sorted = value;
            row.is_write_sorted = is_write;
            (row.timestamp_sorted_diff, prev_timestamp) = match prev_timestamp {
                None => (F::ONE, Some(row.timestamp_sorted)),
                Some(prev) => {
                    if prev_addr == row.addr_sorted {
                        let diff = row.timestamp_sorted - prev;
                        (diff, Some(row.timestamp_sorted))
                    } else {
                        (F::ONE, Some(row.timestamp_sorted))
                    }
                }
            };
            prev_addr = row.addr_sorted;
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
            self.gen_read(0, &[]);
        }
    }

    fn mem_is_contiguous(&self) -> bool {
        if self.mem[0].is_none() {
            return false;
        }

        let addrs_accessed = self
            .mem
            .iter()
            .enumerate()
            .filter_map(|(i, v)| v.as_ref().map(|_| i))
            .sorted();
        for (curr, next) in addrs_accessed.tuple_windows() {
            if next != curr && next != curr + 1 {
                return false;
            }
        }

        true
    }

    pub fn into_polynomial_values_of_target_degree(
        mut self,
        log2_target_degree: usize,
    ) -> Vec<PolynomialValues<F>> {
        assert!(
            self.mem_is_contiguous(),
            "memory must form a contiguous segment whose address starts at 0"
        );
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
