use itertools::Itertools;
use plonky2::hash::poseidon::{
    Poseidon, ALL_ROUND_CONSTANTS, HALF_N_FULL_ROUNDS, N_PARTIAL_ROUNDS, N_ROUNDS,
};

use crate::gate::{Gate, Read};
use crate::ir::{Add, Arithmetic, Assertions, Constant, Constraint, Mul};
use crate::stark::StandardConstraint;
use crate::starks::xor::Bits;

const WIDTH: usize = 12;

#[derive(Clone, Debug)]
#[repr(C)]
pub struct PoseidonPermutationGate<T, F, const CHANNELS: usize> {
    // 0000: PADDING
    // 0001: FIRST_FULL_ROUNDS
    // 0001: PARTIAL_ROUNDS
    // 0010: SECOND_FULL_ROUNDS
    // 0100: OUTPUT
    pub microcode_bits: Bits<T, 4>,

    // the ith bit is set at the ith round
    pub round_bits: Bits<T, N_ROUNDS>,

    // registers for input to the current round
    pub state: [T; WIDTH],

    // registers for current round's round constants
    pub round_constants: [T; WIDTH],

    // registers for computing sbox monomials
    pub sbox_registers: [[T; 3]; WIDTH],

    // phantom
    pub _marker: core::marker::PhantomData<F>,
}

impl<T, F, const CHANNELS: usize> PoseidonPermutationGate<T, F, CHANNELS> {
    /// Gate Size
    pub const SIZE: usize = core::mem::size_of::<PoseidonPermutationGate<u8, F, CHANNELS>>();

    ///
    #[inline]
    pub fn borrow(slice: &[T; Self::SIZE]) -> &Self {
        unsafe { crate::util::transmute_no_compile_time_size_checks(slice) }
    }

    ///
    #[inline]
    pub fn borrow_mut(slice: &mut [T; Self::SIZE]) -> &mut Self {
        unsafe { crate::util::transmute_no_compile_time_size_checks(slice) }
    }
}

impl<T, F, const CHANNELS: usize> Default for PoseidonPermutationGate<T, F, CHANNELS>
where
    T: Copy + Default,
    [T; PoseidonPermutationGate::<T, F, CHANNELS>::SIZE]:,
{
    #[inline]
    fn default() -> Self {
        [Default::default(); Self::SIZE].into()
    }
}

impl<T, F, const CHANNELS: usize> From<PoseidonPermutationGate<T, F, CHANNELS>>
    for [T; PoseidonPermutationGate::<T, F, CHANNELS>::SIZE]
where
    [T; PoseidonPermutationGate::<T, F, CHANNELS>::SIZE]:,
{
    #[inline]
    fn from(gate: PoseidonPermutationGate<T, F, CHANNELS>) -> Self {
        unsafe { crate::util::transmute_no_compile_time_size_checks(gate) }
    }
}

impl<T, F, const CHANNELS: usize> From<[T; PoseidonPermutationGate::<T, F, CHANNELS>::SIZE]>
    for PoseidonPermutationGate<T, F, CHANNELS>
where
    [T; PoseidonPermutationGate::<T, F, CHANNELS>::SIZE]:,
{
    #[inline]
    fn from(gate: [T; PoseidonPermutationGate::<T, F, CHANNELS>::SIZE]) -> Self {
        unsafe { crate::util::transmute_no_compile_time_size_checks(gate) }
    }
}

impl<T, F, const CHANNELS: usize> Read<T> for PoseidonPermutationGate<T, F, CHANNELS> {
    crate::impl_read_body!(T);
}

impl<T, F, COM, const CHANNELS: usize> Gate<T, COM> for PoseidonPermutationGate<T, F, CHANNELS>
where
    F: Poseidon,
    T: Copy,
    COM: Arithmetic<T> + StandardConstraint<T> + Constant<F, T>,
{
    #[inline]
    fn eval(curr: &Self, next: &Self, _: &[T], compiler: &mut COM) {
        let one = compiler.one();

        // MICROCODES
        // check that the microcode bits are bits and sum to zero or one
        compiler.assert_boolean(&curr.microcode_bits.value);
        Bits::assert_valid(&curr.microcode_bits, compiler);

        let curr_is_padding = compiler.sub(&one, &curr.microcode_bits.value);
        let curr_is_first_full_rounds = curr.microcode_bits.bits[0];
        let curr_is_partial_rounds = curr.microcode_bits.bits[1];
        let curr_is_second_full_rounds = curr.microcode_bits.bits[2];
        let curr_is_output = curr.microcode_bits.bits[3];

        let next_is_padding = compiler.sub(&one, &next.microcode_bits.value);
        let next_is_first_full_rounds = next.microcode_bits.bits[0];
        let next_is_partial_rounds = next.microcode_bits.bits[1];
        let next_is_second_full_rounds = next.microcode_bits.bits[2];
        let next_is_output = next.microcode_bits.bits[3];

        // ROUND BITS
        // check that the round bits are bits and sum to one
        compiler.assert_one(&curr.round_bits.value);
        Bits::assert_valid(&curr.round_bits, compiler);

        // ROUND_CONSTANTS
        let all_round_constants = ALL_ROUND_CONSTANTS
            .iter()
            .map(|c| compiler.constant(&F::from_canonical_u64(*c)))
            .collect::<Vec<_>>();

        // MDS_MATRIX_CIRC
        let mds_matrix_circ = <F as Poseidon>::MDS_MATRIX_CIRC
            .iter()
            .map(|c| compiler.constant(&F::from_canonical_u64(*c)))
            .collect::<Vec<_>>();

        // MDS_MATRIX_DIAG
        let mds_matrix_diag = <F as Poseidon>::MDS_MATRIX_DIAG
            .iter()
            .map(|c| compiler.constant(&F::from_canonical_u64(*c)))
            .collect::<Vec<_>>();

        // ADD ROUND CONSTANTS

        // ALL_ROUND_CONSTANTS[i + WIDTH * curr_round]
        // we do this by selecting via a sum over the round_bits
        // degree 2
        let mut this_round_constants = Vec::with_capacity(WIDTH);
        for i in 0..WIDTH {
            let mut sum = compiler.zero();
            for round_idx in 0..N_ROUNDS {
                let round_bit = curr.round_bits.bits[round_idx];
                let constant = all_round_constants[i + WIDTH * round_idx];
                let term = compiler.mul(&round_bit, &constant);
                sum = compiler.add(&sum, &term);
            }

            this_round_constants.push(sum);
        }

        // assert current round constants are `this_round_constants`
        for (curr_round_const, this_round_constants) in
            curr.round_constants.iter().zip(this_round_constants)
        {
            compiler.assert_eq(curr_round_const, &this_round_constants);
        }

        // add round constants
        // degree 1
        let state = curr
            .state
            .iter()
            .zip(curr.round_constants)
            .map(|(state, constant)| compiler.add(state, &constant))
            .collect_vec();

        // apply sbox layer
        // sbox is x |--> x^7
        // when in FULL_ROUNDS (first or second), we want to apply it to every state element
        // when in PARTIAL_ROUNDS, when want to only apply it to the 0th state element only
        // we do this by computing a^7 + b for each state element `x`, where...
        //  in PARTIAL ROUNDS, a = 0, b = x for all but the 0th state element, which has a = x, b = 0
        // 	in FULL ROUNDS, a = x, b = 0

        let curr_is_full_rounds =
            compiler.add(&curr_is_first_full_rounds, &curr_is_second_full_rounds);

        compiler.assert_eq(&curr.sbox_registers[0][0], &curr.state[0]);
        let a = curr.sbox_registers[0][0];
        let a2 = compiler.square(&a);
        let a3 = compiler.mul(&a, &a2);
        compiler.assert_eq(&a3, &curr.sbox_registers[0][1]);

        let a6 = compiler.mul(&curr.sbox_registers[0][1], &curr.sbox_registers[0][1]);
        let out = compiler.mul(&a6, &a);
        compiler.assert_eq(&out, &curr.sbox_registers[0][2]);

        for (i, x) in state.iter().enumerate().skip(1) {
            let a = compiler.mul(&x, &curr_is_full_rounds);
            compiler.assert_eq(&curr.sbox_registers[i][0], &a);

            let a2 = compiler.square(&curr.sbox_registers[i][0]);
            let a3 = compiler.mul(&curr.sbox_registers[i][0], &a2);
            compiler.assert_eq(&a3, &curr.sbox_registers[i][1]);

            let a6 = compiler.mul(&curr.sbox_registers[i][1], &curr.sbox_registers[i][1]);
            let a7 = compiler.mul(&a6, &a);
            let b = compiler.mul(&curr_is_partial_rounds, &a);
            let out = compiler.add(&a7, &b);
            compiler.assert_eq(&out, &curr.sbox_registers[i][2]);
        }

        let state = curr.sbox_registers.iter().map(|sbox| sbox[2]).collect_vec();

        // multiply by MDS matrix
        for i in 0..WIDTH {
            let mut sum = compiler.zero();
            for j in 0..WIDTH {
                sum = compiler.mul_add(&mds_matrix_circ[j], &state[(i + j) % WIDTH], &sum);
            }

            sum = compiler.mul_add(&mds_matrix_diag[i], &state[i], &sum);

            // assurt sum is mds_output[i]
            compiler.assert_eq_transition(&sum, &next.state[i]);
        }

        // INITIAL
        // round bits start with 0th bit set
        compiler.assert_one_first_row(&curr.round_bits.bits[0]);

        // TRANSITIONS
        // round bits shifted right by one unless the current microcode is OUTPUT or PADDING
        {
            let curr_is_output_or_padding = compiler.add(&curr_is_output, &curr_is_padding);
            let cond = compiler.sub(&one, &curr_is_output_or_padding);
            let mut compiler = compiler.when(cond);

            for i in 0..N_ROUNDS {
                let curr_bit = curr.round_bits.bits[i];
                let next_bit = next.round_bits.bits[(i + 1) % N_ROUNDS];
                compiler.assert_eq_transition(&curr_bit, &next_bit);
            }
        }

        // 0th round bit is set if current microcode is OUTPUT_OR_PADDING
        {
            let cond = compiler.add(&curr_is_output, &curr_is_padding);
            let mut compiler = compiler.when(cond);

            compiler.assert_one(&next.round_bits.bits[0]);
        }

        // FIRST_FULL_ROUNDS -> PARTIAL_ROUNDS after HALF_N_FULL_ROUNDS
        {
            let cond = compiler.mul(&curr_is_first_full_rounds, &next_is_partial_rounds);
            let mut compiler = compiler.when(cond);

            compiler.assert_one(&curr.round_bits.bits[HALF_N_FULL_ROUNDS - 1]);
            compiler.assert_one(&next.round_bits.bits[HALF_N_FULL_ROUNDS]);
        }

        // PARTIAL_ROUNDS -> SECOND_FULL_ROUNDS after HALF_N_FULL_ROUNDS + N_PARTIAL_ROUNDS
        {
            let next_is_second_full_rounds = next.microcode_bits.bits[2];
            let cond = compiler.mul(&curr_is_partial_rounds, &next_is_second_full_rounds);
            let mut compiler = compiler.when(cond);

            compiler.assert_one(&curr.round_bits.bits[HALF_N_FULL_ROUNDS + N_PARTIAL_ROUNDS - 1]);
            compiler.assert_one(&next.round_bits.bits[HALF_N_FULL_ROUNDS + N_PARTIAL_ROUNDS]);
        }

        // SECOND_FULL_ROUNDS -> OUTPUT after N_ROUNDS
        {
            let next_is_output = next.microcode_bits.bits[3];
            let cond = compiler.mul(&curr_is_second_full_rounds, &next_is_output);
            let mut compiler = compiler.when(cond);

            compiler.assert_one(&curr.round_bits.bits[N_ROUNDS - 1]);
            compiler.assert_one(&next.round_bits.bits[0]);
        }

        // transition to PADDING only when the current microcode is OUTPUT or PADDING
        {
            let mut compiler = compiler.when(next_is_padding);
            let curr_is_padding_or_output = compiler.add(&curr_is_output, &curr_is_padding);
            compiler.assert_one(&curr_is_padding_or_output);
        }

        // always transition to PADDING when current microcode is PADDING
        {
            let mut compiler = compiler.when(curr_is_padding);
            compiler.assert_one(&next_is_padding);
        }
    }
}
