use alloc::vec::Vec;
use core::mem::{size_of, transmute_copy, ManuallyDrop};

use plonky2::field::polynomial::PolynomialValues;
use plonky2::field::types::Field;
use plonky2::util::transpose;

#[inline]
pub fn is_power_of_two(n: u64) -> bool {
    n & (n - 1) == 0
}

/// A helper function to transpose a row-wise trace and put it in the format that `prove` expects.
pub fn trace_rows_to_poly_values<F: Field, const COLUMNS: usize>(
    trace_rows: Vec<[F; COLUMNS]>,
) -> Vec<PolynomialValues<F>> {
    let trace_row_vecs = trace_rows
        .into_iter()
        .map(|row| row.to_vec())
        .collect::<Vec<_>>();
    let trace_col_vecs: Vec<Vec<F>> = transpose(&trace_row_vecs);
    trace_col_vecs
        .into_iter()
        .map(|column| PolynomialValues::new(column))
        .collect()
}

/// Transmutes `value` without compile-time size checks.
///
/// # Safety
///
/// The same safety requirements as [`transmute_copy`].
pub unsafe fn transmute_no_compile_time_size_checks<T, U>(value: T) -> U {
    debug_assert_eq!(size_of::<T>(), size_of::<U>());
    // Need ManuallyDrop so that `value` is not dropped by this function.
    let value = ManuallyDrop::new(value);
    // Copy the bit pattern. The original value is no longer safe to use.
    transmute_copy(&value)
}
