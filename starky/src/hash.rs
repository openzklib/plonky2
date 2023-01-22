use plonky2::hash::hashing::{SPONGE_WIDTH, SPONGE_RATE};

use crate::ir::{Zero, One};

pub type SpongeState<T> = [T; SPONGE_WIDTH];

pub trait Permutation<T, COM = ()> {
	fn permute(state: &SpongeState<T>, compiler: &mut COM) -> SpongeState<T>;
}

pub trait HashOut<T: Copy + Clone> {
	fn to_vec(&self) -> Vec<T>;
}

pub trait Hasher<T, COM = ()>
where
	T: Copy + Clone,
	COM: One<T> + Zero<T>,
{
	type Permutation: Permutation<T, COM>;
	type Hash: HashOut<T>;

	fn hash_no_pad(input: &[T], compiler: &mut COM)-> Self::Hash;
    fn two_to_one(left: Self::Hash, right: Self::Hash, compiler: &mut COM) -> Self::Hash;
	
    /// Pad the message using the `pad10*1` rule, then hash it.
    fn hash_pad(input: &[T], compiler: &mut COM) -> Self::Hash {
        let mut padded_input = input.to_vec();
        padded_input.push(compiler.one());
        while (padded_input.len() + 1) % SPONGE_WIDTH != 0 {
            padded_input.push(compiler.zero());
        }
        padded_input.push(compiler.one());
        Self::hash_no_pad(&padded_input, compiler)
    }
}

// Hash a message without any padding step. Note that this can enable length-extension attacks.
// However, it is still collision-resistant in cases where the input has a fixed length.
fn hash_n_to_m_no_pad<T, P, COM>(
	inputs: &[T],
	num_outputs: usize,
	compiler: &mut COM,
) -> Vec<T>
where
	T: Copy + Clone,
	P: Permutation<T, COM>,
	COM: One<T> + Zero<T>
{
	let mut state = [compiler.zero(); SPONGE_WIDTH];

	// Absorb all input chunks.
	for input_chunk in inputs.chunks(SPONGE_RATE) {
		state[..input_chunk.len()].copy_from_slice(input_chunk);
		state = P::permute(&state, compiler);
	}

	// Squeeze until we have the desired number of outputs.
	let mut outputs = Vec::new();
	loop {
		for &item in state.iter().take(SPONGE_RATE) {
			outputs.push(item);
			if outputs.len() == num_outputs {
				return outputs;
			}
		}
		state = P::permute(&state, compiler);
	}
}

fn hash_n_to_hash_no_pad<T, P, COM>(inputs: &[T], compiler: &mut COM) -> HashOut4<T>
where
	T: Copy + Clone,
	P: Permutation<T, COM>,
	COM: One<T> + Zero<T>
{
	HashOut4::from_vec(hash_n_to_m_no_pad::<T, P, COM>(&inputs, 4, compiler))
}

// A one-way compression function which takes two 4-element inputs and returns a 4-element output.
fn compress<T, P, COM>(x: HashOut4<T>, y: HashOut4<T>, compiler: &mut COM) -> HashOut4<T>
where
	T: Copy + Clone,
	P: Permutation<T, COM>,
	COM: One<T> + Zero<T>
{
	let mut perm_inputs = [compiler.zero(); SPONGE_WIDTH];
	perm_inputs[..4].copy_from_slice(&x.elements);
	perm_inputs[4..8].copy_from_slice(&y.elements);
	HashOut4 {
		elements: P::permute(&perm_inputs, compiler)[..4].try_into().unwrap(),
	}
}

pub struct HashOut4<T> {
	pub elements: [T; 4],
}

impl<T: Copy + Clone> HashOut4<T> {
	pub fn from_vec(elements: Vec<T>) -> Self {
		assert_eq!(elements.len(), 4);
		Self {
			elements: [elements[0], elements[1], elements[2], elements[3]],
		}
	}
}

impl<T: Copy + Clone> HashOut<T> for HashOut4<T> {
	fn to_vec(&self) -> Vec<T> {
		self.elements.to_vec()
	}
}

pub mod poseidon {
    use plonky2::hash::hash_types::RichField;

    use super::{HashOut4, Hasher, hash_n_to_hash_no_pad, compress, Permutation, SpongeState};

	pub struct PoseidonHash;
	impl<F: RichField> Hasher<F, ()> for PoseidonHash
	{
		type Permutation = PoseidonPermutation;
		type Hash = HashOut4<F>;

		fn hash_no_pad(input: &[F], compiler: &mut ()) -> Self::Hash {
			hash_n_to_hash_no_pad::<F, Self::Permutation, ()>(input, compiler)
		}

		fn two_to_one(left: Self::Hash, right: Self::Hash, compiler: &mut ()) -> Self::Hash {
			compress::<F, Self::Permutation, ()>(left, right, compiler)
		}
	}
	pub struct PoseidonPermutation;
	impl<F: RichField> Permutation<F, ()> for PoseidonPermutation {
		fn permute(input: &SpongeState<F>, _compiler: &mut ()) -> SpongeState<F> {
			F::poseidon(*input)
		}
	}
}