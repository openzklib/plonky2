use plonky2::field::extension::{Extendable, FieldExtension};
use plonky2::field::packed::PackedField;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::ext_target::ExtensionTarget;
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::config::GenericConfig;

use crate::config::StarkConfig;
use crate::consumer::basic::{ConstraintConsumer, RecursiveConstraintConsumer};
use crate::cross_table_lookup::CtlCheckVars;
use crate::ir::Registers;
use crate::permutation::{
    eval_permutation_checks, eval_permutation_checks_circuit, PermutationCheckDataTarget,
    PermutationCheckVars,
};
use crate::stark::Stark;

pub(crate) fn eval_vanishing_poly<F, FE, P, C, S, const D: usize, const D2: usize>(
    stark: &S,
    config: &StarkConfig,
    registers: Registers<P>,
    permutation_data: Option<PermutationCheckVars<P, D2>>,
    ctl_vars: Option<&CtlCheckVars<F, FE, P, D2>>,
    consumer: &mut ConstraintConsumer<P>,
) where
    F: RichField + Extendable<D>,
    FE: FieldExtension<D2, BaseField = F>,
    P: PackedField<Scalar = FE>,
    C: GenericConfig<D, F = F>,
    S: Stark<P, ConstraintConsumer<P>>,
{
    stark.eval_with(registers, consumer, &mut ());
    if let Some(permutation_data) = permutation_data {
        eval_permutation_checks::<F, FE, P, C, S, D, D2>(
            stark,
            config,
            registers,
            permutation_data,
            consumer,
        );
    }
}

pub(crate) fn eval_vanishing_poly_circuit<F, C, S, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    stark: &S,
    config: &StarkConfig,
    registers: Registers<ExtensionTarget<D>>,
    permutation_data: Option<PermutationCheckDataTarget<D>>,
    consumer: &mut RecursiveConstraintConsumer<D>,
) where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    S: Stark<ExtensionTarget<D>, RecursiveConstraintConsumer<D>, CircuitBuilder<F, D>>,
{
    stark.eval_with(registers, consumer, builder);
    if let Some(permutation_data) = permutation_data {
        eval_permutation_checks_circuit::<F, S, D>(
            builder,
            stark,
            config,
            registers,
            permutation_data,
            consumer,
        );
    }
}
