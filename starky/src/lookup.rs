//! Lookup Tables

use core::cmp::Ordering;

use itertools::Itertools;
use plonky2::field::polynomial::PolynomialValues;
use plonky2::field::types::PrimeField64;

use crate::gate::Gate;
use crate::ir::{Assertions, Constraint, ConstraintFiltered, LastRow, Mul, Sub};

/// Asserts a valid lookup over `curr_input`, `next_input`, and `next_table` in the `compiler`.
#[inline]
pub fn assert_lookup<T, COM>(curr_input: &T, next_input: &T, next_table: &T, compiler: &mut COM)
where
    T: Clone,
    COM: Constraint<T> + ConstraintFiltered<T, LastRow> + Mul<T> + Sub<T>,
{
    // A "vertical" diff between the local and next permuted inputs.
    let diff_input_prev = compiler.sub(next_input, curr_input);

    // A "horizontal" diff between the next permuted input and permuted table value.
    let diff_input_table = compiler.sub(next_input, next_table);

    compiler.assert_zero_product(&diff_input_prev, &diff_input_table);

    // This is actually constraining the first row, as per the spec, since `diff_input_table`
    // is a diff of the next row's values. In the context of `constraint_last_row`, the next
    // row is the first row.
    compiler.assert_zero_last_row(&diff_input_table);
}

/// Lookup Gate
pub struct Lookup<T> {
    /// Input Column
    pub input: T,

    /// Table Column
    pub table: T,

    /// Permuted Input Column
    pub permuted_input: T,

    /// Permuted Table Column
    pub permuted_table: T,
}

impl<T, COM> Gate<T, COM> for Lookup<T>
where
    T: Clone,
    COM: Constraint<T> + ConstraintFiltered<T, LastRow> + Mul<T> + Sub<T>,
{
    #[inline]
    fn eval(curr: &Self, next: &Self, _: &[T], compiler: &mut COM) {
        assert_lookup(
            &curr.permuted_input,
            &next.permuted_input,
            &next.permuted_table,
            compiler,
        )
    }
}

/// Given an input column and a table column, generate the permuted input and permuted table columns
/// used in the Halo2 permutation argument.
#[inline]
pub fn permuted_columns<F>(inputs: &[F], table: &[F]) -> (Vec<F>, Vec<F>)
where
    F: PrimeField64,
{
    let n = inputs.len();

    // The permuted inputs do not have to be ordered, but we found that sorting was faster than
    // hash-based grouping. We also sort the table, as this helps us identify "unused" table
    // elements efficiently.
    //
    // To compare elements, e.g. for sorting, we first need them in canonical form. It would be
    // wasteful to canonicalize in each comparison, as a single element may be involved in many
    // comparisons. So we will canonicalize once upfront, then use `to_noncanonical_u64` when
    // comparing elements.

    let mut sorted_inputs = inputs.iter().map(|x| x.to_canonical()).collect::<Vec<_>>();
    sorted_inputs.sort_unstable_by_key(|x| x.to_noncanonical_u64());

    let mut sorted_table = table.iter().map(|x| x.to_canonical()).collect::<Vec<_>>();
    sorted_table.sort_unstable_by_key(|x| x.to_noncanonical_u64());

    let mut unused_table_inds = Vec::with_capacity(n);
    let mut unused_table_vals = Vec::with_capacity(n);
    let mut permuted_table = vec![F::ZERO; n];
    let mut i = 0;
    let mut j = 0;
    while (j < n) && (i < n) {
        let input_val = sorted_inputs[i].to_noncanonical_u64();
        let table_val = sorted_table[j].to_noncanonical_u64();
        match input_val.cmp(&table_val) {
            Ordering::Greater => {
                unused_table_vals.push(sorted_table[j]);
                j += 1;
            }
            Ordering::Less => {
                if let Some(x) = unused_table_vals.pop() {
                    permuted_table[i] = x;
                } else {
                    unused_table_inds.push(i);
                }
                i += 1;
            }
            Ordering::Equal => {
                permuted_table[i] = sorted_table[j];
                i += 1;
                j += 1;
            }
        }
    }

    #[allow(clippy::needless_range_loop)] // indexing is just more natural here
    for jj in j..n {
        unused_table_vals.push(sorted_table[jj]);
    }
    for ii in i..n {
        unused_table_inds.push(ii);
    }
    for (ind, val) in unused_table_inds.into_iter().zip_eq(unused_table_vals) {
        permuted_table[ind] = val;
    }

    (sorted_inputs, permuted_table)
}

/// Assign lookup table to `columns` given the target columns.
#[inline]
pub fn assign_lookup_table<F>(
    input: usize,
    table: usize,
    input_permuted: usize,
    table_permuted: usize,
    columns: &mut [PolynomialValues<F>],
) where
    F: PrimeField64,
{
    let (permuted_input, permuted_table) =
        permuted_columns(&columns[input].values, &columns[table].values);
    columns[input_permuted] = PolynomialValues::new(permuted_input);
    columns[table_permuted] = PolynomialValues::new(permuted_table);
}
