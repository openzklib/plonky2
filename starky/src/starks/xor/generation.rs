use plonky2::field::polynomial::PolynomialValues;
use plonky2::field::types::PrimeField64;
use plonky2::util::log2_ceil;

use crate::starks::xor::layout::Row;
use crate::util::{is_power_of_two, trace_rows_to_poly_values};

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
