use itertools::Itertools;
use plonky2::hash::poseidon::{
    Poseidon, ALL_ROUND_CONSTANTS, HALF_N_FULL_ROUNDS, N_PARTIAL_ROUNDS, N_ROUNDS,
};

use crate::gate::{Gate, Read};
use crate::ir::{Add, Arithmetic, Assertions, Constant, Constraint, Mul};
use crate::stark::StandardConstraint;
use crate::starks::xor::Bits;

const WIDTH: usize = 12;
const N_ROUND_BITS: usize = N_ROUNDS + 1;

#[derive(Clone, Debug)]
#[repr(C)]
pub struct PoseidonPermutationGate<T, F, const CHANNELS: usize> {
    // the ith bit is set at the ith round
    pub round_bits: Bits<T, N_ROUND_BITS>,

    // registers for input to the current round
    pub state: [T; WIDTH],

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

        // ROUND BITS
        // check that the round bits are bits and sum to one
        compiler.assert_one(&curr.round_bits.value);
        Bits::assert_valid(&curr.round_bits, compiler);

        // OPCODE SELECTORS
        // check that the microcode bits are bits and sum to zero or one
        let curr_is_first_full_rounds = compiler.sum(&curr.round_bits.bits[0..HALF_N_FULL_ROUNDS]);
        let curr_is_partial_rounds = compiler.sum(&curr.round_bits.bits[HALF_N_FULL_ROUNDS..(HALF_N_FULL_ROUNDS + N_PARTIAL_ROUNDS)]);
        let curr_is_second_full_rounds = compiler.sum(&curr.round_bits.bits[(HALF_N_FULL_ROUNDS + N_PARTIAL_ROUNDS)..(HALF_N_FULL_ROUNDS + N_PARTIAL_ROUNDS + HALF_N_FULL_ROUNDS)]);
        let curr_is_output = compiler.sum(&curr.round_bits.bits[(HALF_N_FULL_ROUNDS + N_PARTIAL_ROUNDS + HALF_N_FULL_ROUNDS)..]);

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

        // add round constants
        // degree 2
        let state = curr
            .state
            .iter()
            .zip(this_round_constants)
            .map(|(state, constant)| compiler.add(state, &constant))
            .collect_vec();

        // apply sbox layer
        // sbox is x |--> x^7
        // | x | x^3 | x x^3 x^3 |
        // when in FULL_ROUNDS (first or second), we want to apply it to every state element
        // when in PARTIAL_ROUNDS, when want to only apply it to the 0th state element only
        // we do this by computing a^7 + b for each state element `x`, where...
        //  in PARTIAL ROUNDS, a = 0, b = x for all but the 0th state element, which has a = x, b = 0
        // 	in FULL ROUNDS, a = x, b = 0

        let curr_is_full_rounds =
            compiler.add(&curr_is_first_full_rounds, &curr_is_second_full_rounds);

        compiler.assert_eq(&curr.sbox_registers[0][0], &state[0]);
        let a = curr.sbox_registers[0][0];
        let a2 = compiler.square(&a);
        let a3 = compiler.mul(&a, &a2);
        compiler.assert_eq(&a3, &curr.sbox_registers[0][1]);

        let a6 = compiler.mul(&curr.sbox_registers[0][1], &curr.sbox_registers[0][1]);
        let out = compiler.mul(&a6, &a);
        compiler.assert_eq(&out, &curr.sbox_registers[0][2]);

        for (i, x) in state.iter().enumerate().skip(1) {
            // sbox_registers[i][0] = x if curr_is_full_rounds else 0
            // true because `curr_is_full_rounds` is binary
            let a = compiler.mul(&x, &curr_is_full_rounds);
            compiler.assert_eq(&curr.sbox_registers[i][0], &a);

            // sbox_registers[i][1] = sbox_registers[i][0]^3
            let a2 = compiler.square(&curr.sbox_registers[i][0]);
            let a3 = compiler.mul(&curr.sbox_registers[i][0], &a2);
            compiler.assert_eq(&a3, &curr.sbox_registers[i][1]);

            // a7 = sbox_registers[i][1] * sbox_registers[i][1] * sbox_registers[i][1]
            let a6 = compiler.mul(&curr.sbox_registers[i][1], &curr.sbox_registers[i][1]);
            let a7 = compiler.mul(&a6, &a);

            // b = x if curr_is_partial_rounds else 0
            let b = compiler.mul(&curr_is_partial_rounds, &x);

            // sbox_registers[i][2] = a7 + b = x^7 if curr_is_full_rounds else x
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

            // next.state = sum if we're not in the output row
            let cond = compiler.sub(&one, &curr_is_output);
            compiler.when(cond).assert_eq_transition(
                &sum, &next.state[i]
            );
        }

        // INITIAL
        // round bits start with 0th bit set
        compiler.assert_one_first_row(&curr.round_bits.bits[0]);

        // otherwise, round bits shifted right by one
        {
            // TODO: add "bitshift" gadget to compiler
            for i in 0..N_ROUND_BITS {
                let curr_bit = curr.round_bits.bits[i];
                let next_bit = next.round_bits.bits[(i + 1) % N_ROUND_BITS];
                compiler.assert_eq_transition(&curr_bit, &next_bit);
            }
        }
    }
}
