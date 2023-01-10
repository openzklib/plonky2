use plonky2::iop::ext_target::ExtensionTarget;

/// STARK Row Evaluation
#[derive(Clone, Copy, Debug)]
pub struct StarkEvaluation<'t, T> {
    pub local_values: &'t [T],
    pub next_values: &'t [T],
    pub public_inputs: &'t [T],
}

/// STARK Evaluation Variables
pub type StarkEvaluationVars<'a, P> = StarkEvaluation<'a, P>;

/// STARK Evaluation Targets
pub type StarkEvaluationTargets<'a, const D: usize> = StarkEvaluation<'a, ExtensionTarget<D>>;
