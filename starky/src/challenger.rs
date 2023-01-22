use plonky2::hash::hashing::SPONGE_WIDTH;

use crate::{ir::{One, Zero, Extension}, hash::{Hasher, SpongeState, HashOut}};

/// Observes prover messages, and generates challenges by hashing the transcript, a la Fiat-Shamir.
/// Acts as a sponge, and can be compacted to a state.
pub trait Challenger<T, E, H, COM = ()>
where
	T: Copy + Clone,
	E: Copy + Clone,
	H: Hasher<T, COM>,
	COM: One<T> + Zero<T>
{
	/// instantiate a new challenger using the given sponge state
	fn from_state(state: SpongeState<T>) -> Self;
	/// abosrb any unprocessed inputs into the spongeA and squeeze out remaining state
	fn compact(&mut self, compiler: &mut COM) -> SpongeState<T>;
	/// absorb a field element
	fn observe_element(&mut self, element: T, compiler: &mut COM);

	/// absorb an extension field element
	fn observe_extension_element<const D: usize>(&mut self, element: E, compiler: &mut COM)
	where
		E: Extension<T, D>
	{
		self.observe_elements(&element.to_basefield_array(), compiler);
	}

	fn observe_hash<OuterHasher: Hasher<T, COM>>(&mut self, hash: OuterHasher::Hash, compiler: &mut COM) {
		self.observe_elements(&hash.to_vec(), compiler);
	}

	fn observe_elements(&mut self, elements: &[T], compiler: &mut COM) {
		for &element in elements {
			self.observe_element(element, compiler);
		}
	}

	fn observe_extension_elements(&mut self, elements: &[E], compiler: &mut COM)
	where
		E: Extension<T, SPONGE_WIDTH>
	{
		for &element in elements {
			self.observe_extension_element(element, compiler);
		}
	}

	fn observe_cap<OuterHasher: Hasher<T, COM>>(&mut self, cap: Vec<OuterHasher::Hash>, compiler: &mut COM) {
		for hash in cap {
			self.observe_hash::<OuterHasher>(hash, compiler);
		}
	}

	/// squeeze out a challenge
	fn get_challenge(&mut self, compiler: &mut COM) -> T;

	/// squeeze out an extension challenge
	fn get_extension_challenge<const D: usize>(&mut self, compiler: &mut COM) -> E
	where
		E: Extension<T, D>
	{
        let mut arr = [compiler.zero(); D];
        arr.copy_from_slice(&self.get_n_challenges(D, compiler));
        E::from_basefield_array(&arr)
	}

	fn get_n_challenges(&mut self, n: usize, compiler: &mut COM) -> Vec<T> {
        (0..n).map(|_| self.get_challenge(compiler)).collect()
	}

	fn get_n_extension_challenges<const D: usize>(&mut self, n: usize, compiler: &mut COM) -> Vec<E>
	where
		E: Extension<T, D>
	{
		(0..n).map(|_| self.get_extension_challenge(compiler)).collect()
	}
}


pub mod basic {
	use core::marker::PhantomData;
	use plonky2::hash::hashing::{SPONGE_RATE, SPONGE_WIDTH};
	use crate::ir::{One, Zero};
	use crate::hash::{Hasher, Permutation};

	use super::Challenger;

	/// basic challenger
	pub struct BasicChallenger<T, E, H, COM = ()>
	where
		T: Copy + Clone,
		E: Copy + Clone,
		H: Hasher<T, COM>,
		COM: One<T> + Zero<T>
	{
		pub(crate) sponge_state: [T; SPONGE_WIDTH],
		pub(crate) input_buffer: Vec<T>,
		output_buffer: Vec<T>,
		_phantom_hasher: PhantomData<H>,
		_phantom_compiler: PhantomData<COM>,
		_phantom_extension: PhantomData<E>,
	}

	impl<T, E, H, COM> BasicChallenger<T, E, H, COM>
	where
		T: Copy + Clone,
		E: Copy + Clone,
		H: Hasher<T, COM>,
		COM: One<T> + Zero<T>
	{
		fn duplexing(&mut self, compiler: &mut COM) {
			assert!(self.input_buffer.len() <= SPONGE_RATE);

			// Overwrite the first r elements with the inputs. This differs from a standard sponge,
			// where we would xor or add in the inputs. This is a well-known variant, though,
			// sometimes called "overwrite mode".
			for (i, input) in self.input_buffer.drain(..).enumerate() {
				self.sponge_state[i] = input;
			}

			// Apply the permutation.
			self.sponge_state = H::Permutation::permute(&self.sponge_state, compiler);

			self.output_buffer.clear();
			self.output_buffer
				.extend_from_slice(&self.sponge_state[0..SPONGE_RATE]);
		}
	}

	impl<T, E, H, COM> Challenger<T, E, H, COM> for BasicChallenger<T, E, H, COM>
	where
		T: Copy + Clone,
		E: Copy + Clone,
		H: Hasher<T, COM>,
		COM: One<T> + Zero<T>
	{
		fn from_state(state: super::SpongeState<T>) -> Self {
			Self {
				sponge_state: state,
				input_buffer: Vec::with_capacity(SPONGE_RATE),
				output_buffer: Vec::with_capacity(SPONGE_RATE),
				_phantom_hasher: PhantomData,
				_phantom_compiler: PhantomData,
				_phantom_extension: PhantomData,
			}
		}

		fn compact(&mut self, compiler: &mut COM) -> super::SpongeState<T> {
			if !self.input_buffer.is_empty() {
				self.duplexing(compiler);
			}
			self.output_buffer.clear();
			self.sponge_state
		}

		fn observe_element(&mut self, element: T, compiler: &mut COM) {
			// Any buffered outputs are now invalid, since they wouldn't reflect this input.
			self.output_buffer.clear();

			self.input_buffer.push(element);

			if self.input_buffer.len() == SPONGE_RATE {
				self.duplexing(compiler);
			}
		}

		fn get_challenge(&mut self, compiler: &mut COM) -> T {
			// If we have buffered inputs, we must perform a duplexing so that the challenge will
			// reflect them. Or if we've run out of outputs, we must perform a duplexing to get more.
			if !self.input_buffer.is_empty() || self.output_buffer.is_empty() {
				self.duplexing(compiler);
			}

			self.output_buffer
				.pop()
				.expect("Output buffer should be non-empty")
		}
	}


	



	// TODO: make this not conflict
	// impl<T, COM> Zero<HashOut<T>> for COM
	// where
	// 	T: Copy + Clone,
	// 	COM: Zero<T>
	// {
	// 	fn zero(&mut self) -> HashOut<T> {
	// 		HashOut {
	// 			elements: [self.zero(); 4],
	// 		}
	// 	}
	// }
}