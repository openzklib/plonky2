use core::iter;
use core::ops::Range;

use anyhow::{anyhow, Result};
use itertools::Itertools;
use log::{info, Level};
use plonky2_field::extension::Extendable;
use plonky2_field::goldilocks_field::GoldilocksField;
use plonky2_field::types::Field;

use crate::gates::gate::GateRef;
use crate::gates::noop::NoopGate;
use crate::gates::selectors::UNUSED_SELECTOR;
use crate::hash::hash_types::RichField;
use crate::iop::ext_target::ExtensionTarget;
use crate::iop::target::{BoolTarget, Target};
use crate::iop::witness::{PartialWitness, WitnessWrite};
use crate::plonk::circuit_builder::CircuitBuilder;
use crate::plonk::circuit_data::{CircuitConfig, CommonCircuitData, VerifierOnlyCircuitData};
use crate::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
use crate::plonk::plonk_common::eval_l_0_circuit;
use crate::plonk::proof::ProofWithPublicInputs;
use crate::plonk::prover::prove;
use crate::plonk::vars::EvaluationTargets;
use crate::util::partial_products::check_partial_products_circuit;
use crate::util::reducing::ReducingFactorTarget;
use crate::util::timing::TimingTree;
use crate::with_context;

///
pub struct ProofTuple<F, C, const D: usize>
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
{
    proof_with_pis: ProofWithPublicInputs<F, C, D>,
    verifier_only_data: VerifierOnlyCircuitData<C, D>,
    common_data: CommonCircuitData<F, D>,
}

impl<F, C, const D: usize> ProofTuple<F, C, D>
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
{
    pub fn new(
        proof: ProofWithPublicInputs<F, C, D>,
        verifier: VerifierOnlyCircuitData<C, D>,
        common: CommonCircuitData<F, D>,
    ) -> Self {
        Self {
            proof_with_pis: proof,
            verifier_only_data: verifier,
            common_data: common,
        }
    }
}

///
pub type GoldilocksProofTuple = ProofTuple<GoldilocksField, PoseidonGoldilocksConfig, 2>;

/// Produce common data for the padded verifier.
pub fn padded_common_data() -> CommonCircuitData<GoldilocksField, 2>
where
{
    // TODO: Figure out how to choose this. For now this just returns the common data of a
    // factorial circuit with size 5.
    use circuits::factorial_proof;
    let log2_size = 5;
    factorial_proof::<_, PoseidonGoldilocksConfig, 2>(
        &CircuitConfig::standard_recursion_config(),
        log2_size,
    )
    .expect("factorial failed")
    .common_data
}

/// Evaluate vanishing polynomial at `x` for "any" circuit up to a maximum size.
pub fn padded_eval_vanishing_poly_circuit(
    builder: &mut CircuitBuilder<GoldilocksField, 2>,
    _instance_common_data: &CommonCircuitData<GoldilocksField, 2>,
    x: ExtensionTarget<2>,
    x_pow_deg: ExtensionTarget<2>,
    vars: EvaluationTargets<2>,
    local_zs: &[ExtensionTarget<2>],
    next_zs: &[ExtensionTarget<2>],
    partial_products: &[ExtensionTarget<2>],
    s_sigmas: &[ExtensionTarget<2>],
    betas: &[Target],
    gammas: &[Target],
    alphas: &[Target],
) -> Vec<ExtensionTarget<2>> {
    let common_data = padded_common_data();

    // Original Body:
    let max_degree = common_data.quotient_degree_factor;
    let num_prods = common_data.num_partial_products;

    // TODO: Gate constraints
    // Maybe give this the full `common_data` but modify `vars.local_constants` to reflect
    // whether a given gate belongs to `instance_common_data`.
    // let constraint_terms = with_context!(
    //     builder,
    //     "evaluate gate constraints",
    //     padded_evaluate_gate_constraints_circuit::<GoldilocksField, PoseidonGoldilocksConfig, 2>(
    //         builder,
    //         &common_data,
    //         vars,
    //     )
    // );

    // The L_0(x) (Z(x) - 1) vanishing terms.
    let mut vanishing_z_1_terms = Vec::new();
    // The terms checking the partial products.
    let mut vanishing_partial_products_terms = Vec::new();

    let l_0_x = eval_l_0_circuit(builder, common_data.degree(), x, x_pow_deg);

    // Holds `k[i] * x`.
    // This is constant time so long as the number of sigma polynomials is the same
    let mut s_ids = Vec::new();
    for j in 0..common_data.config.num_routed_wires {
        let k = builder.constant(common_data.k_is[j]);
        s_ids.push(builder.scalar_mul_ext(k, x));
    }

    for i in 0..common_data.config.num_challenges {
        let z_x = local_zs[i];
        let z_gx = next_zs[i];

        // L_0(x) (Z(x) - 1) = 0.
        vanishing_z_1_terms.push(builder.mul_sub_extension(l_0_x, z_x, l_0_x));

        let mut numerator_values = Vec::new();
        let mut denominator_values = Vec::new();

        for j in 0..common_data.config.num_routed_wires {
            let wire_value = vars.local_wires[j];
            let beta_ext = builder.convert_to_ext(betas[i]);
            let gamma_ext = builder.convert_to_ext(gammas[i]);

            // The numerator is `beta * s_id + wire_value + gamma`, and the denominator is
            // `beta * s_sigma + wire_value + gamma`.
            let wire_value_plus_gamma = builder.add_extension(wire_value, gamma_ext);
            let numerator = builder.mul_add_extension(beta_ext, s_ids[j], wire_value_plus_gamma);
            let denominator =
                builder.mul_add_extension(beta_ext, s_sigmas[j], wire_value_plus_gamma);
            numerator_values.push(numerator);
            denominator_values.push(denominator);
        }

        // The partial products considered for this iteration of `i`.
        let current_partial_products = &partial_products[i * num_prods..(i + 1) * num_prods];
        // Check the quotient partial products.
        // Is this constant time? No, it loops over the numerator/denominator values in chunks
        // of size max_degree. Also it uses `builder.mul_many_extensions(chunk)`, which multiplies
        // all elements of a chunk together.
        let partial_product_checks = check_partial_products_circuit(
            builder,
            &numerator_values,
            &denominator_values,
            current_partial_products,
            z_x,
            z_gx,
            max_degree,
        );
        vanishing_partial_products_terms.extend(partial_product_checks);
    }

    let vanishing_terms = [
        vanishing_z_1_terms,
        vanishing_partial_products_terms,
        // constraint_terms,
    ]
    .concat();

    alphas
        .iter()
        .map(|&alpha| {
            let alpha = builder.convert_to_ext(alpha);
            let mut alpha = ReducingFactorTarget::new(alpha);
            alpha.reduce(&vanishing_terms, builder)
        })
        .collect()
}

pub fn padded_evaluate_gate_constraints_circuit<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    const D: usize,
>(
    builder: &mut CircuitBuilder<F, D>,
    master_common_data: &CommonCircuitData<F, D>,
    instance_common_data: &CommonCircuitData<F, D>,
    used_gates: &[BoolTarget], // public input list of which gates from master list are used
    vars: EvaluationTargets<D>,
) -> Vec<ExtensionTarget<D>> {
    // This has length equal to the largest number of polynomial constraints imposed by any gate,
    // so we should give it its worst-case length.
    let mut all_gate_constraints =
        vec![builder.zero_extension(); master_common_data.num_gate_constraints];
    // Padding length to use in filter computation
    let padding_length = master_common_data.gates.len() - instance_common_data.gates.len();

    for (i, gate) in master_common_data.gates.iter().enumerate() {
        // Compute what this gate's index would be in `instance_common_data.gates`.
        // If not present then it doesn't matter what value comes here b/c filter will return 0.
        // Q: Should this be in-circuit?
        let instance_index = instance_common_data
            .gates
            .iter()
            .position(|g| g == gate)
            .unwrap_or(0);
        // Look up `selector_index` from `instance_common_data.selectors_info.selector_indices`
        let selector_index = instance_common_data.selectors_info.selector_indices[instance_index];
        // Num selectors should be taken from instance because it's part of the definition of
        // the selector polynomial used by the prover
        with_context!(
            builder,
            &format!("evaluate {} constraints", gate.0.id()),
            padded_eval_filtered_circuit(
                builder,
                gate,
                used_gates[i],
                padding_length,
                vars,
                instance_index,
                selector_index,
                instance_common_data.selectors_info.groups[selector_index].clone(),
                instance_common_data.selectors_info.num_selectors(),
                &mut all_gate_constraints,
            )
        );
    }
    all_gate_constraints
}

/// Adds this gate's filtered constraints into the `combined_gate_constraints` buffer.
fn padded_eval_filtered_circuit<F, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    gate: &GateRef<F, D>,
    padding_value: BoolTarget,
    padding_length: usize,
    mut vars: EvaluationTargets<D>,
    j: usize,
    selector_index: usize,
    group_range: Range<usize>,
    num_selectors: usize,
    combined_gate_constraints: &mut [ExtensionTarget<D>],
) where
    F: RichField + Extendable<D>,
{
    println!("Padded filtered eval for gate {}", gate.0.id());
    let padding = (0..padding_length)
        .map(|_| padding_value.target.to_ext_target(builder.zero()))
        .collect::<Vec<_>>();
    let filter = padded_compute_filter_circuit(
        builder,
        &padding,
        j,
        group_range,
        vars.local_constants[selector_index],
        num_selectors > 1,
    );
    vars.remove_prefix(num_selectors);
    let my_constraints = gate.0.eval_unfiltered_circuit(builder, vars);
    for (acc, c) in combined_gate_constraints.iter_mut().zip(my_constraints) {
        *acc = builder.mul_add_extension(filter, c, *acc);
    }
}

fn padded_compute_filter_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    padding: &[ExtensionTarget<D>],
    j: usize,
    group_range: Range<usize>,
    s: ExtensionTarget<D>,
    many_selectors: bool,
) -> ExtensionTarget<D> {
    debug_assert!(group_range.contains(&j));
    let mut v = group_range
        .filter(|&i| i != j)
        .chain(many_selectors.then_some(UNUSED_SELECTOR))
        .map(|i| {
            let c = builder.constant_extension(F::Extension::from_canonical_usize(i));
            builder.sub_extension(c, s)
        })
        .collect::<Vec<_>>();
    v.extend(padding);
    println!("Computed filter as a product of {} values", v.len());
    builder.mul_many_extension(v)
}

/// Constant time version of `check_partial_products_circuit`.
pub fn padded_check_partial_products_circuit<F: RichField + Extendable<D>, const D: usize>(
    padded_size: usize,
    builder: &mut CircuitBuilder<F, D>,
    numerators: &[ExtensionTarget<D>],
    denominators: &[ExtensionTarget<D>],
    partials: &[ExtensionTarget<D>],
    z_x: ExtensionTarget<D>,
    z_gx: ExtensionTarget<D>,
    max_degree: usize,
) -> Vec<ExtensionTarget<D>> {
    debug_assert!(max_degree > 1);
    let one = builder.one().to_ext_target(builder.zero());
    let ones = (0..max_degree).map(|_| one).collect::<Vec<_>>();
    // Padding
    let mut partials: Vec<_> = partials.to_vec();
    let mut numerators: Vec<_> = numerators.to_vec();
    let mut denominators: Vec<_> = denominators.to_vec();

    while partials.len() < padded_size {
        partials.push(one);
        numerators.extend(ones.clone());
        denominators.extend(ones.clone());
    }

    let product_accs = iter::once(&z_x)
        .chain(partials.iter())
        .chain(iter::once(&z_gx));
    let chunk_size = max_degree;
    numerators
        .chunks(chunk_size)
        .zip_eq(denominators.chunks(chunk_size))
        .zip_eq(product_accs.tuple_windows())
        .map(|((nume_chunk, deno_chunk), (&prev_acc, &next_acc))| {
            let nume_product = builder.mul_many_extension(nume_chunk);
            let deno_product = builder.mul_many_extension(deno_chunk);
            let next_acc_deno = builder.mul_extension(next_acc, deno_product);
            // Assert that next_acc * deno_product = prev_acc * nume_product.
            builder.mul_sub_extension(prev_acc, nume_product, next_acc_deno)
        })
        .collect()
}

/// When an operation `f` depends on a circuit size parameter that influences the time-complexity
/// of `f`, this function will perform the operation for all parameter values from `range` and return
/// only the value from the desired parameter value `n`.
pub fn constant_time_operation_circuit<OP, T, F, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    f: &mut OP,
    range: Range<usize>,
    n: usize,
) -> ExtensionTarget<D>
where
    F: RichField + Extendable<D>,
    OP: FnMut(&mut CircuitBuilder<F, D>, usize) -> ExtensionTarget<D>,
{
    let mut result = builder.add_virtual_extension_target();
    let zero = builder.zero();
    let _ = range
        .map(|m| {
            let value = f(builder, m);
            // Is this the right way to allocate this bool?
            let bit = builder.constant_bool(m == n);
            let bit_ext: ExtensionTarget<D> = bit.target.to_ext_target(zero);
            result = builder.arithmetic_extension(F::ONE, F::ONE, bit_ext, value, result);
        })
        .collect::<Vec<_>>();
    result
}

/// Custom way to display circuit and proof metadata.
pub fn display_circuit_proof_info<F, C, const D: usize>(
    proof_tuple: &ProofTuple<F, C, D>,
    circuit_name: String,
) where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
{
    println!("\nProperties of a {circuit_name} circuit and proof \n");

    // Configuration
    println!("\n{circuit_name} configuration data:");
    println!(
        "Num challenges: {}",
        proof_tuple.common_data.config.num_challenges
    );

    // FRI Configuration
    println!("\n{circuit_name} FRI config:");
    println!(
        "Cap size: {}",
        proof_tuple.common_data.config.fri_config.num_cap_elements()
    );
    println!(
        "Number of query rounds: {}",
        proof_tuple.common_data.config.fri_config.num_query_rounds
    );

    // Common Data
    println!("\n{circuit_name} common data:");
    println!("Degree: {}", proof_tuple.common_data.degree());
    println!("Num Constants: {}", proof_tuple.common_data.num_constants);
    println!(
        "Num Public Inputs: {}",
        proof_tuple.common_data.num_public_inputs
    );
    println!(
        "Num Partial Products: {}",
        proof_tuple.common_data.num_partial_products
    );
    println!(
        "Number of sigma polynomials: {}",
        proof_tuple.common_data.k_is.len()
    );
    println!(
        "Degree of quotient polynomial: {}",
        proof_tuple.common_data.quotient_degree()
    );
    println!(
        "Gate types: {:?}",
        proof_tuple
            .common_data
            .gates
            .iter()
            .map(|g| g.0.id())
            .collect::<Vec<_>>()
    );
    println!(
        "Number of selector polynomials: {}",
        proof_tuple.common_data.selectors_info.num_selectors()
    );

    // Verifier
    println!("\n{circuit_name} verifier data:");
    println!(
        "Length of constants_sigmas_cap: {}",
        proof_tuple.verifier_only_data.constants_sigmas_cap.len()
    );

    // Proof
    println!("\n{circuit_name} proof data:");
    println!(
        "Length of wires_cap: {}",
        proof_tuple.proof_with_pis.proof.wires_cap.len()
    );
    // println!("Length of wires_cap: {}", proof_tuple.proof_with_pis.proof.plonk_zs_partial_products_cap.len());
    // println!("Length of wires_cap: {}", proof_tuple.proof_with_pis.proof.quotient_polys_cap.len());
    println!(
        "Length of sigma openings: {}",
        proof_tuple.proof_with_pis.proof.openings.plonk_sigmas.len()
    );
    println!(
        "Length of wires openings: {}",
        proof_tuple.proof_with_pis.proof.openings.wires.len()
    );
    println!(
        "Length of partial product openings: {}",
        proof_tuple
            .proof_with_pis
            .proof
            .openings
            .partial_products
            .len()
    );
    println!(
        "Length of plonk_zs: {}",
        proof_tuple.proof_with_pis.proof.openings.plonk_zs.len()
    );

    // FRI Proof
    println!("\n{circuit_name} FRI proof data:");
    println!(
        "Number of reduced polynomials: {}",
        proof_tuple
            .proof_with_pis
            .proof
            .opening_proof
            .commit_phase_merkle_caps
            .len()
    );
    println!(
        "Number of query rounds: {}",
        proof_tuple
            .proof_with_pis
            .proof
            .opening_proof
            .query_round_proofs
            .len()
    );
    println!(
        "Number of final poly coefficients: {}",
        proof_tuple
            .proof_with_pis
            .proof
            .opening_proof
            .final_poly
            .len()
    );
}

/// Sample circuits for experiments
pub mod circuits {
    use super::*;

    pub fn factorial_proof<
        F: RichField + Extendable<D>,
        C: GenericConfig<D, F = F>,
        const D: usize,
    >(
        config: &CircuitConfig,
        log2_size: usize,
    ) -> Result<ProofTuple<F, C, D>> {
        let num_rounds = 1 << log2_size;
        info!("Constructing inner proof with {num_rounds} rounds");
        let mut builder = CircuitBuilder::<F, D>::new(config.clone());

        // The arithmetic circuit.
        let initial = builder.add_virtual_target();
        let mut cur_target = initial;
        for i in 2..num_rounds {
            let i_target = builder.constant(F::from_canonical_u32(i));
            cur_target = builder.mul(cur_target, i_target);
        }

        // Public inputs are the initial value (provided below) and the result (which is generated).
        builder.register_public_input(initial);
        builder.register_public_input(cur_target);

        let mut pw = PartialWitness::new();
        pw.set_target(initial, F::ONE);

        let data = builder.build::<C>();
        let mut timing = TimingTree::new("prove", Level::Debug);
        let proof = prove(&data.prover_only, &data.common, pw, &mut timing)?;
        timing.print();

        data.verify(proof.clone())?;
        Ok(ProofTuple::new(proof, data.verifier_only, data.common))
    }

    /// Creates a dummy proof which should have `2 ** log2_size` rows.
    pub fn dummy_proof<F: RichField + Extendable<D>, C: GenericConfig<D, F = F>, const D: usize>(
        config: &CircuitConfig,
        log2_size: usize,
    ) -> Result<ProofTuple<F, C, D>> {
        // 'size' is in degree, but we want number of noop gates. A non-zero amount of padding will be added and size will be rounded to the next power of two. To hit our target size, we go just under the previous power of two and hope padding is less than half the proof.
        let num_dummy_gates = match log2_size {
            0 => return Err(anyhow!("size must be at least 1")),
            1 => 0,
            2 => 1,
            n => (1 << (n - 1)) + 1,
        };
        info!("Constructing inner proof with {} gates", num_dummy_gates);
        let mut builder = CircuitBuilder::<F, D>::new(config.clone());
        for _ in 0..num_dummy_gates {
            builder.add_gate(NoopGate, vec![]);
        }
        builder.print_gate_counts(0);

        let data = builder.build::<C>();
        let inputs = PartialWitness::new();

        let mut timing = TimingTree::new("prove", Level::Debug);
        let proof = prove(&data.prover_only, &data.common, inputs, &mut timing)?;
        timing.print();
        data.verify(proof.clone())?;

        Ok(ProofTuple::new(proof, data.verifier_only, data.common))
    }
}

#[cfg(test)]
mod tests {
    use circuits::{dummy_proof, factorial_proof};

    use super::*;
    use crate::plonk::vanishing_poly::evaluate_gate_constraints_circuit;

    // cargo test --package plonky2 --lib --all-features -- recursion::padding_experiments::tests::evaluate_gate_constraints_padding_test --exact --nocapture
    #[test]
    fn evaluate_gate_constraints_padding_test() {
        let config = CircuitConfig::standard_recursion_config();
        let master_circuit_size = 5;
        let instance_circuit_size = 5;
        let master_common_data = factorial_proof::<GoldilocksField, PoseidonGoldilocksConfig, 2>(
            &config,
            master_circuit_size,
        )
        .expect("factorial")
        .common_data;
        let instance_tuple = dummy_proof::<GoldilocksField, PoseidonGoldilocksConfig, 2>(
            &config,
            instance_circuit_size,
        )
        .expect("dummy");
        // We need to know which of the factorial circuit's gates are used by the dummy circuit.
        // This can be determined by hand by running the other tests. It's [1 1 1 0 0]
        let used_gates = [true, true, true, false, false];

        let mut builder = CircuitBuilder::<GoldilocksField, 2>::new(config);
        let mut pw = PartialWitness::new();
        let used_gates = used_gates
            .iter()
            .map(|&b| builder.constant_bool(b))
            .collect::<Vec<_>>();
        let proof_with_pis = builder
            .add_virtual_proof_with_pis::<PoseidonGoldilocksConfig>(&instance_tuple.common_data);
        pw.set_proof_with_pis_target(&proof_with_pis, &instance_tuple.proof_with_pis);
        let public_inputs_hash = builder
            .hash_n_to_hash_no_pad::<<PoseidonGoldilocksConfig as GenericConfig<2>>::Hasher>(
                proof_with_pis.public_inputs.clone(),
            );
        let vars = EvaluationTargets {
            local_constants: &proof_with_pis.proof.openings.constants,
            local_wires: &proof_with_pis.proof.openings.wires,
            public_inputs_hash: &public_inputs_hash,
        };

        let padded_gate_constraint_evaluations =
            padded_evaluate_gate_constraints_circuit::<_, PoseidonGoldilocksConfig, 2>(
                &mut builder,
                &master_common_data,
                &instance_tuple.common_data,
                &used_gates,
                vars,
            );
        println!(
            "Padded gate constraint evaluations has length {} \n",
            padded_gate_constraint_evaluations.len()
        );
        let original_gate_constraint_evaluations =
            evaluate_gate_constraints_circuit::<_, PoseidonGoldilocksConfig, 2>(
                &mut builder,
                &instance_tuple.common_data,
                vars,
            );
        println!(
            "Original gate constraint evaluations has length {}",
            original_gate_constraint_evaluations.len()
        );
        // Assert equality of the two methods. Note that the vectors of gate constraint evaluations
        // will have different lengths in general. We expect their leading entries to agree.
        let _ = padded_gate_constraint_evaluations
            .iter()
            .zip(original_gate_constraint_evaluations.iter())
            .map(|(&padded, &original)| {
                builder.connect_extension(padded, original);
            })
            .collect::<Vec<_>>();

        // The builder now describes a circuit that checks the gate constraints in two ways and asserts their equality.
        let data = builder.build::<PoseidonGoldilocksConfig>();
        let mut timing = TimingTree::new("prove", Level::Debug);
        let proof = prove(&data.prover_only, &data.common, pw, &mut timing)
            .expect("Proof generation failed");
        timing.print();
        data.verify(proof).expect("Proof verification failed");
    }

    // cargo test --package plonky2 --lib --all-features -- recursion::padding_experiments::tests::factorial_circuit_info --exact --nocapture
    #[test]
    fn factorial_circuit_info() {
        let config = CircuitConfig::standard_recursion_config();
        let log2_size = 5;
        let circuit_name = format!("Factorial_{log2_size}");
        let proof_tuple: GoldilocksProofTuple =
            factorial_proof(&config, log2_size).expect("Unable to form factorial proof tuple");

        display_circuit_proof_info(&proof_tuple, circuit_name);
    }

    // cargo test --package plonky2 --lib --all-features -- recursion::padding_experiments::tests::dummy_circuit_info --exact --nocapture
    #[test]
    fn dummy_circuit_info() {
        let config = CircuitConfig::standard_recursion_config();
        let log2_size = 3;
        let circuit_name = format!("Dummy_{log2_size}");
        let proof_tuple: GoldilocksProofTuple =
            dummy_proof(&config, log2_size).expect("Unable to form factorial proof tuple");

        display_circuit_proof_info(&proof_tuple, circuit_name);
    }
}
