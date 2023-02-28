use crate::{stark::{StandardConsumer, Stark, StarkConfiguration, StandardConstraint}, ir::{Arithmetic, Constant}, consumer::Compiler, gate::{Read, Gate}};

pub mod layout;
pub mod generation;

use layout::*;
use plonky2::hash::poseidon::Poseidon;


#[derive(Clone, Copy, Default, Eq, Hash, PartialEq)]
pub struct PoseidonPermutationStark<F: Poseidon, const CHANNELS: usize> {
	_phantom: std::marker::PhantomData<F>,
}

impl<F: Poseidon, const CHANNELS: usize> StarkConfiguration for PoseidonPermutationStark<F, CHANNELS> {
    #[inline]
    fn columns(&self) -> usize {
        PoseidonPermutationGate::<u8, u8, CHANNELS>::SIZE
    }

    #[inline]
    fn public_inputs(&self) -> usize {
        0
    }

    #[inline]
    fn constraint_degree(&self) -> usize {
        3
    }
}


impl<T, F, C, COM, const CHANNELS: usize> Stark<T, C, COM> for PoseidonPermutationStark<F, CHANNELS>
where
	T: Copy,
    F: Poseidon,
    C: StandardConsumer<T, COM>,
    COM: Arithmetic<T> + StandardConstraint<T> + Constant<F, T>
{
    #[inline]
    fn eval(
        &self,
        mut curr: &[T],
        mut next: &[T],
        public_inputs: &[T],
        mut compiler: Compiler<C, COM>,
    ) {
		let curr = PoseidonPermutationGate::<T, F, CHANNELS>::read(&mut curr);
		let next = PoseidonPermutationGate::<T, F, CHANNELS>::read(&mut next);
		PoseidonPermutationGate::eval(curr, next, public_inputs, &mut compiler);
    }
}

#[cfg(test)]
mod tests {
	use crate::stark_testing::{test_stark_low_degree, test_stark_circuit_constraints};

	use super::*;

    use anyhow::Result;
    use plonky2::plonk::config::{PoseidonGoldilocksConfig, GenericConfig};

    #[test]
    fn test_stark_degree() -> Result<()> {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        type S = PoseidonPermutationStark<F, 0>;

        let stark = S::default();
        let metadata = stark.metadata();
        test_stark_low_degree::<F, S, D>(stark, metadata.columns, metadata.public_inputs)?;
        test_stark_circuit_constraints::<F, C, S, D>(
            stark,
            metadata.columns,
            metadata.public_inputs,
        )?;
        Ok(())
    }
}