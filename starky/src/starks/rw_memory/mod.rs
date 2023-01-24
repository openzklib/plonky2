//! STARK that checks the access trace of a read-write memory
//! this can be thought of as a form of "offline memory checking"

use crate::consumer::Compiler;
use crate::ir::{Arithmetic, Assertions, One, Sub};
use crate::permutation::PermutationPair;
use crate::stark::{StandardConsumer, Stark, StarkConfiguration};
use crate::starks::rw_memory::layout::{
    lookup_permutation_sets, sorted_access_permutation_pairs, RwMemoryRow, RW_MEMORY_NUM_COLS_BASE,
};

// TODO: pub mod generation;
pub mod layout;

/// Read-Write Memory STARK
#[derive(Default)]
pub struct RwMemoryStark<const NUM_CHANNELS: usize>;

impl<const NUM_CHANNELS: usize> StarkConfiguration for RwMemoryStark<NUM_CHANNELS> {
    #[inline]
    fn columns(&self) -> usize {
        RW_MEMORY_NUM_COLS_BASE + NUM_CHANNELS
    }

    #[inline]
    fn public_inputs(&self) -> usize {
        0
    }

    #[inline]
    fn constraint_degree(&self) -> usize {
        3
    }

    #[inline]
    fn permutation_pairs(&self) -> Vec<PermutationPair> {
        vec![PermutationPair {
            column_pairs: sorted_access_permutation_pairs(),
        }]
    }
}

impl<F, C, COM, const NUM_CHANNELS: usize> Stark<F, C, COM> for RwMemoryStark<NUM_CHANNELS>
where
    F: Copy,
    C: StandardConsumer<F, COM>,
    COM: Arithmetic<F>,
{
    #[inline]
    fn eval(&self, curr: &[F], next: &[F], public_inputs: &[F], mut compiler: Compiler<C, COM>) {
        let _ = public_inputs;
        let curr = RwMemoryRow::<F, NUM_CHANNELS>::from(curr);
        let next = RwMemoryRow::<F, NUM_CHANNELS>::from(next);

        let one = compiler.one();

        let address_changed = compiler.sub(next.addr_sorted, curr.addr_sorted);
        let timestamp_changed = compiler.sub(next.timestamp_sorted, curr.timestamp_sorted);

        let address_unchanged = compiler.sub(&one, &address_changed);

        // check sorted addresses are monotonic, continuous, and start at 0
        // we do this by ensuring either the sorted address increases by 0 or 1 at each curr_row and at
        // the first curr_row, the sorted addr is 0

        compiler.assert_zero_first_row(curr.addr_sorted);
        compiler.assert_zero_product_transition(&address_changed, &address_unchanged);

        // check timestamps are increasing using a range check
        // this works as follows:
        // 1. we range check every timestamp to be in [1..num_rows].
        // 2. we range check the *difference* between the current and next timestamp to be in
        //    [1..num_rows] if address hasn't changed (i.e. we only care about timestamps for
        //    a particular address)
        // 3. this is enough. Let x, y be subsequent timestamps for a given address. x, y, and
        //    y - x are all in [1..num_rows]. Suppose "x > y" in the field. Then y - x > num_rows -><-
        //
        // this argument works as long as the number of rows is less than half of the field order, which
        // is very true for this library because we can only use up to 2^TWO_ADICITY rows and this is
        // usually far below the field size.
        //
        // we do this by enforcing the "unsorted" timestamps start at 1 and increment by 1 each row.
        // Then we apply a lookup against that col to check that the timestamp diffs are in [1..num_rows]
        // since timestamp_sorted is a permutation of timestamp, timestamp_sorted is guaranteed to be in
        // that range lookups are applied at the end of this function

        compiler
            .when(address_unchanged)
            .assert_eq_transition(next.timestamp_sorted_diff, &timestamp_changed);

        // set the timestamp difference to 1 if the address changed as a dummy to indicate we don't care
        // (our range check doesn't include 0 because timestamps have to be unique)

        compiler
            .when(address_changed)
            .assert_eq_transition(next.timestamp_sorted_diff, &one);

        // check that is_write is binary
        compiler.assert_boolean(curr.is_write);
        compiler.assert_boolean(curr.is_write_sorted);

        // check that "unsorted" timestamps start at 1 and increment by 1 each curr_row
        compiler.assert_eq_first_row(curr.timestamp, &one);
        compiler.assert_increments_by(curr.timestamp, next.timestamp, &one);

        // check that the sorted memory trace is valid
        // to do this, we check the following at each step;
        // 1. if the address has changed, the memory trace is valid at this step
        // 2. if the address has not changed and the current operation is a write, the memory trace is
        //    valid at this step
        // 3. if the address has not changed and the current operation is a read, the memory trace is
        //    valid at this step iff the value is the same

        let next_is_not_write = compiler.sub(&one, next.is_write_sorted);

        compiler
            .when_all([address_unchanged, next_is_not_write])
            .assert_eq_transition(next.value_sorted, curr.value_sorted);

        // Apply all of the lookups.
        for (_, _, input, table) in lookup_permutation_sets() {
            compiler.assert_lookup(&curr[input], &next[input], &next[table]);
        }
    }
}

/* TODO:
#[cfg(test)]
mod tests {
    use anyhow::Result;
    use plonky2::field::types::Field;
    use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
    use plonky2::util::timing::TimingTree;
    use rand::Rng;

    use super::*;
    use crate::config::StarkConfig;
    use crate::prover::prove_no_ctl;
    use crate::stark_testing::test_stark_low_degree;
    use crate::starks::rw_memory::generation::RwMemoryGenerator;
    use crate::verifier::verify_stark_proof_no_ctl;

    /*
    #[test]
    fn test_stark_degree() -> Result<()> {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        type S = RwMemoryStark<1>;

        let stark = S::new();
        test_stark_low_degree(stark)
    }
    */

    /*
    #[test]
    fn test_random_trace() -> Result<()> {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        type S = StackStark<F, D, 1>;

        let mut generator = RwMemoryGenerator::<F, 1>::new();
        let mut rng = rand::thread_rng();
        let addrs = 0..100;
        for addr in addrs.clone() {
            generator.gen_write(addr, F::ZERO, &[0])
        }

        for i in 0..500 {
            let addr = rng.gen_range(addrs.clone());
            let is_write = rng.gen_bool(0.5);
            if is_write {
                let val = rng.gen::<u32>();
                generator.gen_write(addr, F::from_canonical_u32(val), &[0]);
            } else {
                generator.gen_read(addr, &[0]);
            }
        }

        let config = StarkConfig::standard_fast_config();
        let stark = S::new();
        let trace = generator.into_polynomial_values();
        let mut timing = TimingTree::default();
        let proof = prove_no_ctl::<F, C, S, D>(&stark, &config, &trace, [], &mut timing)?;
        verify_stark_proof_no_ctl(&stark, &proof, &config)?;

        Ok(())
    }
    */
}
*/
