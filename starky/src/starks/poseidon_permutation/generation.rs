use itertools::Itertools;
use plonky2::{field::types::{Field, PrimeField64}, hash::poseidon::{Poseidon, N_ROUNDS, HALF_N_FULL_ROUNDS, N_PARTIAL_ROUNDS, ALL_ROUND_CONSTANTS}};
use alloc::vec::Vec;

use super::layout::*;

/// Poseidon Generator
pub struct PoseidonPermutationGenerator<F: Field, const CHANNELS: usize>
where
    [(); PoseidonPermutationGate::<F, F, CHANNELS>::SIZE]:,
	F: Poseidon,
{
    trace: Vec<[F; PoseidonPermutationGate::<F, F, CHANNELS>::SIZE]>,
}

impl<F: PrimeField64 + Poseidon, const CHANNELS: usize> Default for PoseidonPermutationGenerator<F, CHANNELS>
where
	[(); PoseidonPermutationGate::<F, F, CHANNELS>::SIZE]:,
{
	fn default() -> Self {
		Self::new()
	}
}

impl<F: PrimeField64 + Poseidon, const CHANNELS: usize> PoseidonPermutationGenerator<F, CHANNELS>
where
	[(); PoseidonPermutationGate::<F, F, CHANNELS>::SIZE]:,
{
	pub fn new() -> Self {
		Self {
			trace: Vec::new(),
		}
	}

	pub fn gen_permutation(&mut self, mut state: [F; WIDTH]) -> [F; WIDTH] {
		for i in 0..HALF_N_FULL_ROUNDS {
			state = self.gen_full_round(state, i);
		}

		for i in HALF_N_FULL_ROUNDS..HALF_N_FULL_ROUNDS+N_PARTIAL_ROUNDS {
			state = self.gen_partial_round(state, i);
		}

		for i in HALF_N_FULL_ROUNDS+N_PARTIAL_ROUNDS..N_ROUNDS {
			state = self.gen_full_round(state, i);
		}

		self.gen_output_round(state);

		state
	}

	fn gen_full_round(&mut self, state: [F; WIDTH], round: usize) -> [F; WIDTH] {
		let mut row = PoseidonPermutationGate::<F, F, CHANNELS>::default();
		row.state.copy_from_slice(&state);
		row.round_bits.bits[round] = F::ONE;

		let added_round_constants = self.add_round_constants(&mut row, round);
		self.full_sbox_layer(&mut row, added_round_constants);
		let state = self.mds_layer(&mut row);

		self.trace.push(row.into());
		state
	}

	fn gen_partial_round(&mut self, state: [F; WIDTH], round: usize) -> [F; WIDTH] {
		let mut row = PoseidonPermutationGate::<F, F, CHANNELS>::default();
		row.state.copy_from_slice(&state);
		row.round_bits.bits[round] = F::ONE;

		let added_round_constants = self.add_round_constants(&mut row, round);
		self.partial_sbox_layer(&mut row, added_round_constants);
		let state = self.mds_layer(&mut row);

		self.trace.push(row.into());
		state
	}

	fn gen_output_round(&mut self, state: [F; WIDTH]) {
		// round constants are "0" in the STARK for output round since we select via the first N_ROUDNS round bits
		// curr is neither full rounds nor partial rounds, so both a and b are zero (see comment in `eval` code), so we skip the sbox layer
		// we also ignore the MDS layer, since we don't constrain the next state in the output round
		// therefore we do nothing but copy the state and set the round bit here

		let mut row = PoseidonPermutationGate::<F, F, CHANNELS>::default();
		row.state.copy_from_slice(&state);
		row.round_bits.bits[N_ROUNDS] = F::ONE;
		self.trace.push(row.into());
	}

	fn add_round_constants(&mut self, row: &mut PoseidonPermutationGate<F, F, CHANNELS>, round: usize) -> [F; WIDTH] {
		let round_constants = (0..WIDTH).map(|i| F::from_canonical_u64(ALL_ROUND_CONSTANTS[i + WIDTH * round]));
		let mut added_round_constants = [F::ZERO; WIDTH];
		for (o, (a, b)) in added_round_constants.iter_mut().zip(round_constants.zip(row.state)) {
			*o = a + b;
		}
		
		added_round_constants
	}

	fn full_sbox_layer(&mut self, row: &mut PoseidonPermutationGate<F, F, CHANNELS>, added_round_constants: [F; WIDTH]) {
		for ([a, a3, a7], x) in row.sbox_registers.iter_mut().zip(added_round_constants) {
			*a = x;
			*a3 = x * x * x;
			*a7 = x * *a3 * *a3;
		};
	}

	fn partial_sbox_layer(&mut self, row: &mut PoseidonPermutationGate<F, F, CHANNELS>, added_round_constants: [F; WIDTH]) {
		// 0th element gets sbox
		let [a, a3, a7] = &mut row.sbox_registers[0];
		let x = added_round_constants[0];
		*a = x;
		*a3 = x * x * x;
		*a7 = x * *a3 * *a3;

		// rest pass through
		for ([_, _, a7], x) in row.sbox_registers.iter_mut().zip(added_round_constants).skip(1) {
			*a7 = x;
		};
	}

	fn mds_layer(&mut self, row: &mut PoseidonPermutationGate<F, F, CHANNELS>) -> [F; WIDTH] {
		let mut new_state = [F::ZERO; WIDTH];
        let state = row.sbox_registers.iter().map(|sbox| sbox[2]).collect_vec();

		for i in 0..WIDTH {
			let mut sum = F::ZERO;
			for j in 0..WIDTH {
				sum += F::from_canonical_u64(<F as Poseidon>::MDS_MATRIX_CIRC[j]) * state[(i + j) % WIDTH];
			}

			sum += F::from_canonical_u64(<F as Poseidon>::MDS_MATRIX_DIAG[i]) * state[i];

			new_state[i] = sum;
		}

		new_state
	}
}