use plonky2::field::extension::{Extendable, FieldExtension};
use plonky2::field::packed::PackedField;
use plonky2::hash::hash_types::RichField;
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::config::GenericConfig;

use crate::config::StarkConfig;
use crate::constraint_consumer::{self, ConstraintConsumer, Consumer, RecursiveConstraintConsumer};
use crate::permutation::{
    eval_permutation_checks, eval_permutation_checks_circuit, PermutationCheck,
    PermutationCheckDataTarget, PermutationCheckVars,
};
use crate::stark::Stark;
use crate::vars::{StarkEvaluation, StarkEvaluationTargets, StarkEvaluationVars};

/* TODO:
///
pub fn eval_vanishing_poly_2<F, C, S, T, E, COM, const D: usize>(
    stark: &S,
    config: &StarkConfig,
    vars: StarkEvaluation<E>,
    permutation_data: Option<PermutationCheck<T, E>>,
    consumer: &mut Consumer<T, E>,
    compiler: &mut COM,
) where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    S: Stark<F, D>,
    T: Copy,
    E: Clone,
    COM: constraint_consumer::Mul<E>
        + constraint_consumer::ScalarMulAdd<T, E>
        + constraint_consumer::Sub<E>,
{
    stark.eval(
        vars.local_values,
        vars.next_values,
        vars.public_inputs,
        consumer,
        compiler,
    );
    if let Some(permutation_data) = permutation_data {
        todo!()
    }
}
*/

pub(crate) fn eval_vanishing_poly<F, FE, P, C, S, const D: usize, const D2: usize>(
    stark: &S,
    config: &StarkConfig,
    vars: StarkEvaluationVars<P>,
    permutation_data: Option<PermutationCheckVars<P, D2>>,
    consumer: &mut ConstraintConsumer<P>,
) where
    F: RichField + Extendable<D>,
    FE: FieldExtension<D2, BaseField = F>,
    P: PackedField<Scalar = FE>,
    C: GenericConfig<D, F = F>,
    S: Stark<F, D>,
{
    stark.eval_packed_generic(vars, consumer);
    if let Some(permutation_data) = permutation_data {
        eval_permutation_checks::<F, FE, P, C, S, D, D2>(
            stark,
            config,
            vars,
            permutation_data,
            consumer,
        );
    }
}

pub(crate) fn eval_vanishing_poly_circuit<F, C, S, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    stark: &S,
    config: &StarkConfig,
    vars: StarkEvaluationTargets<D>,
    permutation_data: Option<PermutationCheckDataTarget<D>>,
    consumer: &mut RecursiveConstraintConsumer<D>,
) where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    S: Stark<F, D>,
{
    stark.eval_ext_circuit(builder, vars, consumer);
    if let Some(permutation_data) = permutation_data {
        eval_permutation_checks_circuit::<F, S, D>(
            builder,
            stark,
            config,
            vars,
            permutation_data,
            consumer,
        );
    }
}
