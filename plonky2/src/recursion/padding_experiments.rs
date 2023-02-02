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
use crate::plonk::circuit_data::{
    CircuitConfig, CommonCircuitData, VerifierCircuitData, VerifierCircuitTarget,
    VerifierOnlyCircuitData,
};
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
#[derive(Clone, Debug)]
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


/// Evaluate vanishing polynomial at `x` for "any" circuit up to a maximum size.
/// Assumes vars, s_sigmas, partial_products have been padded already. Will still
/// select on their values to ensure only used wire values make it in to computation.
pub fn padded_eval_vanishing_poly_circuit<F, C, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    global_common_data: &CommonCircuitData<F, D>,
    padded_verifier_data: &PaddedVerifierDataTarget,
    num_selectors: usize,   // How should this be supplied?
    instance_degree: usize, // How should this be supplied?
    x: ExtensionTarget<D>,
    x_pow_deg: ExtensionTarget<D>,
    vars: EvaluationTargets<D>,
    local_zs: &[ExtensionTarget<D>],
    next_zs: &[ExtensionTarget<D>],
    partial_products: &[ExtensionTarget<D>],
    s_sigmas: &[ExtensionTarget<D>],
    betas: &[Target],
    gammas: &[Target],
    alphas: &[Target],
) -> Vec<ExtensionTarget<D>>
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
{
    let max_degree = global_common_data.quotient_degree_factor;
    let num_prods = global_common_data.num_partial_products;

    let constraint_terms = with_context!(
        builder,
        "evaluate gate constraints",
        padded_evaluate_gate_constraints_circuit::<F, C, D>(
            builder,
            global_common_data,
            padded_verifier_data,
            num_selectors,
            vars,
        )
    );

    // The L_0(x) (Z(x) - 1) vanishing terms.
    let mut vanishing_z_1_terms = Vec::new();
    // The terms checking the partial products.
    let mut vanishing_partial_products_terms = Vec::new();

    let l_0_x = eval_l_0_circuit(builder, instance_degree, x, x_pow_deg);

    // Holds `k[i] * x`.
    // This is constant time so long as the number of sigma polynomials is the same
    let mut s_ids = Vec::new();
    // We don't trust prover to provide only as many values as instance.num_routed_wires, so we filter their input
    let mut s_sigmas_filtered = Vec::new();
    let one = builder.one_extension();
    // Padding here is needed only
    for j in 0..global_common_data.config.num_routed_wires {
        // let k = builder.constant(global_common_data.k_is[j]); // no longer constants
        s_ids.push(builder.scalar_mul_ext(padded_verifier_data.k_is[j], x));
        
        s_sigmas_filtered.push(builder.select_ext(
            padded_verifier_data.used_wires[j],
            s_sigmas[j],
            one, // Pad with same value used to pad k_is in `pad_verifier_data`
        ));
    }

    // TODO: Pad or assume num_challenges is fixed?
    for i in 0..global_common_data.config.num_challenges {
        let z_x = local_zs[i];
        let z_gx = next_zs[i];

        // L_0(x) (Z(x) - 1) = 0.
        vanishing_z_1_terms.push(builder.mul_sub_extension(l_0_x, z_x, l_0_x));

        let mut numerator_values = Vec::new();
        let mut denominator_values = Vec::new();
        let beta_ext = builder.convert_to_ext(betas[i]);
        let gamma_ext = builder.convert_to_ext(gammas[i]);

        // Note that the conditional selecting done here is to account for an instance circuit with fewer
        // routed wires than the global configuration. It's not clear that we need to support this case,
        // however, as all the standard plonky2 configs use 80 routed wires.
        for j in 0..global_common_data.config.num_routed_wires {
            // No need to select on this because below we select num/denom values based on whether wire used
            let wire_value = vars.local_wires[j];

            // The numerator is `beta * s_id + wire_value + gamma`, and the denominator is
            // `beta * s_sigma + wire_value + gamma`.
            let wire_value_plus_gamma = builder.add_extension(wire_value, gamma_ext);
            let mut numerator =
                builder.mul_add_extension(beta_ext, s_ids[j], wire_value_plus_gamma);
            numerator = builder.select_ext(padded_verifier_data.used_wires[j], numerator, one);
            let mut denominator = // s_ids and s_sigmas will be padded with 1 when extra routed wires
                builder.mul_add_extension(beta_ext, s_sigmas[j], wire_value_plus_gamma);
            denominator = builder.select_ext(padded_verifier_data.used_wires[j], denominator, one);
            numerator_values.push(numerator);
            denominator_values.push(denominator);
        }

        // The partial products considered for this iteration of `i`.
        // Note: The padding will have to be "interleaved" with the values for different challenge rounds,
        // but that happens at witness generation
        let current_partial_products = &partial_products[i * num_prods..(i + 1) * num_prods];
        let current_partial_products_filtered = current_partial_products
            .iter()
            .zip(padded_verifier_data.used_partial_product.iter())
            .map(|(&value, &bit)| builder.select_ext(bit, value, one))
            .collect::<Vec<_>>();
        // Check the quotient partial products.
        // Is this constant time? It loops over the numerator/denominator values in chunks
        // of size max_degree. Also it uses `builder.mul_many_extensions(chunk)`, which multiplies
        // all elements of a chunk together. Since numerator_values and denominator_values have been
        // padded to global config's size, this is constant time.
        let partial_product_checks = check_partial_products_circuit(
            builder,
            &numerator_values,
            &denominator_values,
            &current_partial_products_filtered,
            z_x,
            z_gx,
            max_degree,
        );
        vanishing_partial_products_terms.extend(partial_product_checks);
    }

    // This is now of a fixed size
    let vanishing_terms = [
        vanishing_z_1_terms,
        vanishing_partial_products_terms,
        constraint_terms,
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

/// The selector data of a single gate from global gate list.
#[derive(Debug, Clone)]
pub struct PaddedSelectorsInfo {
    /// 0 if gate is unused in instance circuit, 1 if used.
    pub padding_value: bool,

    /// Encoding of selector groups in context of global gate list
    pub selector_bits: Vec<bool>,

    /// Selector index from instance circuit in context of global gate list
    pub selector_index: usize,

    /// Whether the instance circuit used multiple selector groups
    pub num_selectors: bool, // could move to `PaddedVerifierData`
}

/// Target carrying selector data of a single gate from global gate list.
#[derive(Debug, Clone)]
pub struct PaddedSelectorsInfoTarget {
    /// 0 if gate is unused in instance circuit, 1 if used.
    pub padding_value: BoolTarget,

    /// Encoding of selector groups in context of global gate list
    pub selector_bits: Vec<BoolTarget>,

    /// Selector indices from instance circuit in context of global gate list.
    pub selector_index: Target,

    // /// Number of selector groups used in instance circuit
    // pub num_selectors: usize,
    /// `num_selectors > 1`
    pub many_selectors: BoolTarget,
}

/// Padded form of `VerifierData`
/// There could be a compressed "Pre-PaddedVerifierData" that this is computed from, e.g. used_wires: usize
#[derive(Debug, Clone)]
pub struct PaddedVerifierData<F, C, const D: usize>
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
{
    /// The verifier data of some circuit
    pub instance_verifier_data: VerifierCircuitData<F, C, D>,

    /// For each gate of some global gate list, a `Vec<bool>` encoding its representation
    /// within the selector groups of `instance_verifier_data`.
    pub selector_info: Vec<PaddedSelectorsInfo>,

    /// For each wire of global common data, k_i coset shift value if used in instance and 0 otherwise
    pub k_is: Vec<F>,

    /// For each wire of global common data, true if used by instance
    pub used_wires: Vec<bool>,

    /// For each partial product term of common data, true if used by instance
    pub used_partial_product: Vec<bool>,
}

/// Target version of `PaddedVerifierData
#[derive(Debug, Clone)]
pub struct PaddedVerifierDataTarget {
    /// The verifier data of some circuit
    pub instance_verifier_data: VerifierCircuitTarget,

    /// For each gate of some global gate list, a `PaddedSelectorsInfoTarget` encoding its representation
    /// within the selector groups of `instance_verifier_data`.
    pub selector_info: Vec<PaddedSelectorsInfoTarget>,

    /// For each wire of global common data, k_i coset shift value if used in instance and 0 otherwise
    pub k_is: Vec<Target>,

    /// For each wire of global common data, true if used by instance
    pub used_wires: Vec<BoolTarget>,

    /// For each partial product term of common data, true if used by instance
    pub used_partial_product: Vec<BoolTarget>,
}

/// Pads `instance_verifier_data` relative to `global_common_data`. Expresses the gate selector
/// groups in terms of the global gate set and pads the `k_is` to have same length as global number
/// of routed wires.
pub fn pad_verifier_data<F, C, const D: usize>(
    global_common_data: &CommonCircuitData<F, D>,
    instance_verifier_data: &VerifierCircuitData<F, C, D>,
) -> PaddedVerifierData<F, C, D>
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
{
    let selector_info = global_common_data
        .gates
        .iter()
        .map(|gate| selector_padding(global_common_data, &instance_verifier_data.common, gate))
        .collect();
    let mut used_wires = Vec::with_capacity(global_common_data.config.num_routed_wires);
    let k_is = (0..global_common_data.config.num_routed_wires)
        .map(|i| {
            if i < instance_verifier_data.common.config.num_routed_wires {
                // TODO: < or <=?
                used_wires.push(true);
                instance_verifier_data.common.k_is[i]
            } else {
                used_wires.push(false);
                F::ONE
            }
        })
        .collect();

    let used_partial_product = (0..global_common_data.num_partial_products)
        .map(|i| i < instance_verifier_data.common.num_partial_products)
        .collect();
    PaddedVerifierData {
        instance_verifier_data: instance_verifier_data.clone(),
        selector_info,
        k_is,
        used_wires,
        used_partial_product,
    }
}

/// Pads proof of an instance circuit to size appropriate for `global_common_data`.
pub fn pad_proof<F, C, const D: usize>(
    global_common_data: &CommonCircuitData<F, D>,
    proof_with_pis: ProofWithPublicInputs<F, C, D>,
) -> ProofWithPublicInputs<F, C, D>
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
{
    // What all needs to be padded?
    // - Extra wire openings
    // - Extra partial product openings (if config equal these will be too)
    // - Num public inputs
    // - FRI Proof:
    //      - number of coefficients of final_poly. Coefficients are ordered [a_0, a_1, ... ] so you can append 0's to end
    let mut padded_proof = proof_with_pis.clone();
    println!(
        "Global common data uses {:?} routed wires",
        global_common_data.config.num_routed_wires
    );
    println!(
        "Global common data uses {:?} total wires",
        global_common_data.config.num_wires
    );

    println!(
        "Instance has {:?} wire openings",
        proof_with_pis.proof.openings.wires.len()
    );
    println!(
        "Global common data has {:?} challenge rounds",
        global_common_data.config.num_challenges
    );
    println!(
        "Instance uses {:?} routed wires",
        proof_with_pis.proof.openings.wires.len() / global_common_data.config.num_challenges
    );

    let padding_wires =
        global_common_data.config.num_wires - proof_with_pis.proof.openings.wires.len();
    println!("Adding {padding_wires} additional wire openings");
    padded_proof
        .proof
        .openings
        .wires
        .extend((0..padding_wires).map(|_| F::Extension::ZERO));

    println!(
        "Global common data uses {:?} public inputs",
        global_common_data.num_public_inputs
    );
    println!(
        "Proof has {:?} public inputs",
        proof_with_pis.public_inputs.len()
    );
    let padding_pub_ins = global_common_data.num_public_inputs - proof_with_pis.public_inputs.len();
    padded_proof
        .public_inputs
        .extend((0..padding_pub_ins).map(|_| F::ZERO));

    println!(
        "Global common data has FRI final poly length {:?}",
        global_common_data.fri_params.final_poly_len()
    );
    println!(
        "Proof has final FRI poly of length {:?}",
        proof_with_pis.proof.opening_proof.final_poly.len()
    );
    // let padding_final_poly_coeffs = global_common_data.fri_params.final_poly_len()
    //     - proof_with_pis.proof.opening_proof.final_poly.len();
    // padded_proof
    //     .proof
    //     .opening_proof
    //     .final_poly
    //     .coeffs
    //     .extend((0..padding_final_poly_coeffs).map(|_| F::Extension::ZERO));

    padded_proof
}

pub fn padded_evaluate_gate_constraints_circuit<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    const D: usize,
>(
    builder: &mut CircuitBuilder<F, D>,
    global_common_data: &CommonCircuitData<F, D>,
    padded_verifier_data: &PaddedVerifierDataTarget,
    num_selectors: usize, // TODO: How should this be supplied?
    vars: EvaluationTargets<D>,
) -> Vec<ExtensionTarget<D>> {
    // This has length equal to the largest number of polynomial constraints imposed by any gate,
    // so we should give it its worst-case length.
    let mut all_gate_constraints =
        vec![builder.zero_extension(); global_common_data.num_gate_constraints];

    for (i, gate) in global_common_data.gates.iter().enumerate() {
        with_context!(
            builder,
            &format!("evaluate {} constraints", gate.0.id()),
            padded_eval_filtered_circuit(
                builder,
                gate,
                vars,
                &padded_verifier_data.selector_info[i],
                num_selectors,
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
    mut vars: EvaluationTargets<D>,
    selector_info: &PaddedSelectorsInfoTarget,
    num_selectors: usize, // TODO: How should this be supplied?
    combined_gate_constraints: &mut [ExtensionTarget<D>],
) where
    F: RichField + Extendable<D>,
{
    let s = builder
        .random_access_extension(selector_info.selector_index, vars.local_constants.to_vec());
    let filter = padded_compute_filter_circuit(
        builder,
        selector_info.padding_value,
        &selector_info.selector_bits,
        s,
        selector_info.many_selectors,
    );
    vars.remove_prefix(num_selectors); // Maybe vars should be broken up outside this function?
    let my_constraints = gate.0.eval_unfiltered_circuit(builder, vars);
    for (acc, c) in combined_gate_constraints.iter_mut().zip(my_constraints) {
        *acc = builder.mul_add_extension(filter, c, *acc);
    }
}

// Extract some higher order function like compute_padded_product(bit_vector, padding_value, values_vector)
fn padded_compute_filter_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    padding: BoolTarget,
    selector_bits: &[BoolTarget], // pub in
    s: ExtensionTarget<D>,
    many_selectors: BoolTarget,
) -> ExtensionTarget<D> {
    let padding_ext = builder.convert_to_ext(padding.target);
    let unused_value = builder.add_extension(padding_ext, s);
    let mut values = selector_bits
        .iter()
        .enumerate()
        .map(|(i, &b)| {
            let used_value = builder.constant_extension(F::Extension::from_canonical_usize(i));
            let c = builder.select_ext(b, used_value, unused_value);
            builder.sub_extension(c, s)
        })
        .collect::<Vec<_>>();
    let unused_selector_value =
        builder.constant_extension(F::Extension::from_canonical_usize(UNUSED_SELECTOR));
    let unused_selector_value =
        builder.select_ext(many_selectors, unused_selector_value, unused_value);
    values.push(builder.sub_extension(unused_selector_value, s));

    builder.mul_many_extension(values)
}

/// Processes selector data from `instance_common_data` for use in `padded_eval_filtered_circuit`.
pub fn selector_padding<F, const D: usize>(
    global_common_data: &CommonCircuitData<F, D>,
    instance_common_data: &CommonCircuitData<F, D>,
    gate: &GateRef<F, D>,
) -> PaddedSelectorsInfo
where
    F: RichField + Extendable<D>,
{
    let instance_index = instance_common_data
        .gates
        .iter()
        .position(|g| g == gate)
        .unwrap_or(0);
    let selector_index = instance_common_data.selectors_info.selector_indices[instance_index];
    let mut selector_bits = Vec::new();
    if !instance_common_data.gates.contains(gate) {
        // If the instance does not use this gate then all selector bits are 0
        selector_bits.extend((0..global_common_data.gates.len()).map(|_| false));
        PaddedSelectorsInfo {
            padding_value: false,
            selector_bits,
            selector_index,
            num_selectors: instance_common_data.selectors_info.num_selectors() > 1,
        }
    } else {
        let group_range = &instance_common_data.selectors_info.groups[selector_index];
        // Turn on the bits belonging to this range except `instance_index`
        selector_bits.extend(
            (0..global_common_data.gates.len())
                .map(|i| i != instance_index && group_range.contains(&i)),
        );
        // println!("For {:?} computed the selector padding value {selector_index} and the selector bits {selector_bits:#?}", gate.0.id());
        PaddedSelectorsInfo {
            padding_value: true,
            selector_bits,
            selector_index,
            num_selectors: instance_common_data.selectors_info.num_selectors() > 1,
        }
    }
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

/// Sample circuits for experiments
pub mod circuits {
    use super::*;
    use crate::gates::poseidon::PoseidonGate;
    use crate::iop::wire::Wire;
    use crate::plonk::circuit_data::CircuitData;
    use crate::plonk::vanishing_poly::evaluate_gate_constraints_circuit;

    /// Return circuit data for a circuit containing all supported gates. Currently
    /// that means: `ArithmeticGate`, ... `PoseidonGate`,
    /// TODO: Circuit Building and Witness generation are mixed together in here
    pub fn most_complex_circuit<
        F: RichField + Extendable<D>,
        C: GenericConfig<D, F = F>,
        const D: usize,
    >(
        config: &CircuitConfig,
        degree_bits: usize,
    ) -> Result<ProofTuple<F, C, D>> {
        use crate::hash::hashing::SPONGE_WIDTH;

        let mut builder = CircuitBuilder::<F, D>::new(config.clone());
        let mut pw = PartialWitness::new();

        // Arithmetic Gate
        let mult_0 = builder.add_virtual_target();
        let mult_1 = builder.add_virtual_target();
        let addend = builder.add_virtual_target();
        let result = builder.arithmetic(F::ONE, F::ONE, mult_0, mult_1, addend);
        pw.set_target(mult_0, F::from_canonical_u64(2));
        pw.set_target(mult_1, F::from_canonical_u64(3));
        pw.set_target(addend, F::from_canonical_u64(4));
        pw.set_target(result, F::from_canonical_u64(10));

        // Base Sum Gate
        let integer_target = builder.add_virtual_target();
        let num_bits = 3;
        let decomposition_target = builder.split_le(integer_target, num_bits);
        let integer: u64 = (1 << num_bits) - 1; // generalize
        pw.set_target(integer_target, F::from_canonical_u64(integer));
        for i in 0..num_bits {
            pw.set_bool_target(decomposition_target[num_bits - 1 - i], true)
        }

        // Exponentiation : There will need to be a padded version since this explicitly takes `num_power_bits` for the power
        let base = builder.add_virtual_target();
        let exponent = builder.add_virtual_target();
        let num_bits = 2; // Fixed exponent size
        let result = builder.exp(base, exponent, num_bits);
        pw.set_target(base, F::from_canonical_u64(2));
        pw.set_target(exponent, F::from_canonical_u64(3));
        pw.set_target(result, F::from_canonical_u64(8));

        // Poseidon Gate
        let row = builder.add_gate(PoseidonGate::<F, D>::new(), vec![]);
        let permutation_inputs = (0..SPONGE_WIDTH)
            .map(F::from_canonical_usize)
            .collect::<Vec<_>>();

        pw.set_wire(
            Wire {
                row,
                column: PoseidonGate::<F, D>::WIRE_SWAP,
            },
            F::ZERO,
        );
        for i in 0..SPONGE_WIDTH {
            pw.set_wire(
                Wire {
                    row,
                    column: PoseidonGate::<F, D>::wire_input(i),
                },
                permutation_inputs[i],
            );
        }

        // Bump up degree with NoOps
        let min_gates = (1 << (degree_bits - 1)) + 1;
        for _ in builder.num_gates()..min_gates {
            builder.add_gate(NoopGate, vec![]);
        }

        // Need some public inputs
        builder.register_public_inputs(&[mult_0, mult_1, addend, result]);

        // Finalize
        let data = builder.build::<C>();
        let mut timing = TimingTree::new("prove", Level::Debug);
        let proof = prove(&data.prover_only, &data.common, pw, &mut timing)?;
        timing.print();

        data.verify(proof.clone())?;
        Ok(ProofTuple::new(proof, data.verifier_only, data.common))
    }

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

    /// Padded Eval Gate Constraint Circuit Data
    pub fn padded_eval_gate_constraints_circuit<F, C, const D: usize>(
        config: CircuitConfig,
        instance_common_data: &CommonCircuitData<F, D>, // should be independent of this
    ) -> CircuitData<F, C, D>
    where
        F: RichField + Extendable<D>,
        C: GenericConfig<D, F = F>,
    {
        let degree_bits = 10;
        let global_common_data = most_complex_circuit::<F, C, D>(&config, degree_bits)
            .expect("factorial")
            .common_data;

        let mut builder = CircuitBuilder::new(config);

        let proof_with_pis = builder.add_virtual_proof_with_pis::<C>(instance_common_data);
        let public_inputs_hash = builder
            .hash_n_to_hash_no_pad::<<PoseidonGoldilocksConfig as GenericConfig<2>>::Hasher>(
                proof_with_pis.public_inputs.clone(),
            );
        let padded_verifier_data_target = builder.add_virtual_padded_verifier_data(
            instance_common_data.config.fri_config.cap_height,
            global_common_data.gates.len(),
            global_common_data.config.num_routed_wires,
            global_common_data.num_partial_products,
        );
        let vars = EvaluationTargets {
            local_constants: &proof_with_pis.proof.openings.constants,
            local_wires: &proof_with_pis.proof.openings.wires,
            public_inputs_hash: &public_inputs_hash,
        };
        let _padded_gate_constraint_evaluations = padded_evaluate_gate_constraints_circuit::<F, C, D>(
            &mut builder,
            &global_common_data,
            &padded_verifier_data_target,
            instance_common_data.selectors_info.num_selectors(),
            vars,
        );
        println!(
            "Builder has {:?} constraints prior to build()",
            builder.num_gates()
        );
        builder.build()
    }

    /// Unpadded Eval Gate Constraint Circuit Data
    pub fn unpadded_eval_gate_constraints_circuit<F, C, const D: usize>(
        config: CircuitConfig,
        instance_common_data: &CommonCircuitData<F, D>,
    ) -> CircuitData<F, C, D>
    where
        F: RichField + Extendable<D>,
        C: GenericConfig<D, F = F>,
    {
        let mut builder = CircuitBuilder::new(config);
        let proof_with_pis = builder.add_virtual_proof_with_pis::<C>(instance_common_data);
        let public_inputs_hash = builder
            .hash_n_to_hash_no_pad::<<PoseidonGoldilocksConfig as GenericConfig<2>>::Hasher>(
                proof_with_pis.public_inputs.clone(),
            );
        let vars = EvaluationTargets {
            local_constants: &proof_with_pis.proof.openings.constants,
            local_wires: &proof_with_pis.proof.openings.wires,
            public_inputs_hash: &public_inputs_hash,
        };
        let _padded_gate_constraint_evaluations =
            evaluate_gate_constraints_circuit::<F, C, D>(&mut builder, instance_common_data, vars);
        println!(
            "Builder has {:?} constraints prior to build()",
            builder.num_gates()
        );
        builder.build()
    }
}

#[cfg(test)]
mod tests {
    use circuits::{
        dummy_proof, factorial_proof, most_complex_circuit, padded_eval_gate_constraints_circuit,
        unpadded_eval_gate_constraints_circuit,
    };

    use super::*;
    use crate::plonk::vanishing_poly::{
        eval_vanishing_poly_circuit, evaluate_gate_constraints_circuit,
    };
    use crate::plonk::verifier::verify;

    // cargo test --package plonky2 --lib --all-features -- recursion::padding_experiments::tests::eval_vanishing_polynomial_padding_test --exact
    /// Test that checks correctness of `padded_evaluate_gate_constraints`
    #[test]
    fn eval_vanishing_polynomial_padding_test() {
        let config = CircuitConfig::standard_recursion_config();
        // let config = CircuitConfig::wide_ecc_config();
        let global_circuit_degree_bits = 10;
        let instance_circuit_size = 5;
        let global_common_data =
            most_complex_circuit::<GoldilocksField, PoseidonGoldilocksConfig, 2>(
                &config,
                global_circuit_degree_bits,
            )
            .expect("global")
            .common_data;
        let config = CircuitConfig::standard_recursion_config();
        let instance_tuple = factorial_proof::<GoldilocksField, PoseidonGoldilocksConfig, 2>(
            &config,
            instance_circuit_size,
        )
        .expect("instance");

        let mut builder = CircuitBuilder::<GoldilocksField, 2>::new(config);
        let mut pw = PartialWitness::new();

        let proof_with_pis =
            builder.add_virtual_proof_with_pis::<PoseidonGoldilocksConfig>(&instance_tuple.common_data); // change to global common data when pad_proof is working
        pw.set_proof_with_pis_target(
            &proof_with_pis,
            &instance_tuple.proof_with_pis,
            // &pad_proof(&global_common_data, instance_tuple.proof_with_pis.clone()),
        );
        let public_inputs_hash_target = builder
            .hash_n_to_hash_no_pad::<<PoseidonGoldilocksConfig as GenericConfig<2>>::Hasher>(
            proof_with_pis.public_inputs.clone(),
        );

        let padded_verifier_data_target = builder.add_virtual_padded_verifier_data(
            instance_tuple.common_data.config.fri_config.cap_height,
            global_common_data.gates.len(),
            global_common_data.config.num_routed_wires,
            global_common_data.num_partial_products,
        );
        let padded_verifier_data = pad_verifier_data(
            &global_common_data,
            &VerifierCircuitData {
                verifier_only: instance_tuple.clone().verifier_only_data,
                common: instance_tuple.clone().common_data,
            },
        );
        // println!("Computed padded verifier data as {padded_verifier_data:#?}",);
        // // Break it:
        // let _ = padded_verifier_data
        //     .selector_info
        //     .iter_mut()
        //     .map(|selector_info| {
        //         // selector_info.selector_bits[0] = !selector_info.selector_bits[0];
        //         // selector_info.padding_value = true;
        //     })
        //     .collect::<Vec<_>>();
        pw.set_padded_verifier_data_target(&padded_verifier_data_target, &padded_verifier_data);

        let public_inputs_hash = builder
            .hash_n_to_hash_no_pad::<<PoseidonGoldilocksConfig as GenericConfig<2>>::InnerHasher>(
                proof_with_pis.public_inputs.clone(),
            );
        let challenges = proof_with_pis.get_challenges::<_, PoseidonGoldilocksConfig>(
            &mut builder,
            public_inputs_hash,
            padded_verifier_data_target
                .instance_verifier_data
                .circuit_digest,
            &instance_tuple.common_data,
        );
        let proof = proof_with_pis.proof;
        let local_zs = &proof.openings.plonk_zs;
        let next_zs = &proof.openings.plonk_zs_next;
        let s_sigmas = &proof.openings.plonk_sigmas;
        let partial_products = &proof.openings.partial_products;

        let zeta_pow_deg = builder.exp_power_of_2_extension(
            challenges.plonk_zeta,
            instance_tuple.common_data.degree_bits(),
        );

        let vars = EvaluationTargets {
            local_constants: &proof.openings.constants,
            local_wires: &proof.openings.wires,
            public_inputs_hash: &public_inputs_hash_target,
        };

        let padded_vanishing_poly_evaluations =
            padded_eval_vanishing_poly_circuit::<_, PoseidonGoldilocksConfig, 2>(
                &mut builder,
                &global_common_data,
                &padded_verifier_data_target,
                instance_tuple.common_data.selectors_info.num_selectors(),
                instance_tuple.common_data.degree(),
                challenges.plonk_zeta,
                zeta_pow_deg,
                vars,
                local_zs,
                next_zs,
                partial_products,
                s_sigmas,
                &challenges.plonk_betas,
                &challenges.plonk_gammas,
                &challenges.plonk_alphas,
            );
        let original_vanishing_poly_evaluations =
            eval_vanishing_poly_circuit::<_, PoseidonGoldilocksConfig, 2>(
                &mut builder,
                &instance_tuple.common_data,
                challenges.plonk_zeta,
                zeta_pow_deg,
                vars,
                local_zs,
                next_zs,
                partial_products,
                s_sigmas,
                &challenges.plonk_betas,
                &challenges.plonk_gammas,
                &challenges.plonk_alphas,
            );
        // Assert equality of the two methods.
        let _ = padded_vanishing_poly_evaluations
            .iter()
            .zip(original_vanishing_poly_evaluations.iter())
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

    // sanity check
    #[test]
    fn compare_wire_values() {
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<GoldilocksField, 2>::new(config);
        let mut pw = PartialWitness::new();

        let target_1 = builder.add_virtual_target();
        let target_2 = builder.add_virtual_target();
        builder.connect(target_1, target_2);

        // NOTE: Forgetting to set a wire value results in a satisfied proof!
        // pw.set_target(target_1, GoldilocksField::from_canonical_u64(1));
        pw.set_target(target_2, GoldilocksField::from_canonical_u64(2));

        let data = builder.build::<PoseidonGoldilocksConfig>();
        let mut timing = TimingTree::new("prove", Level::Debug);
        let proof = prove(&data.prover_only, &data.common, pw, &mut timing)
            .expect("Proof generation failed");
        verify(proof, &data.verifier_only, &data.common).expect("Proof verification failed");
    }

    // cargo test --package plonky2 --lib --all-features -- recursion::padding_experiments::tests::evaluate_gate_constraints_padding_test --exact --nocapture
    /// Test that checks correctness of `padded_evaluate_gate_constraints`
    #[test]
    fn evaluate_gate_constraints_padding_test() {
        let config = CircuitConfig::standard_recursion_config();
        let instance_circuit_size = 5;
        let global_circuit_degree_bits = 10;
        let global_common_data =
            most_complex_circuit::<GoldilocksField, PoseidonGoldilocksConfig, 2>(
                &config,
                global_circuit_degree_bits,
            )
            .expect("global")
            .common_data;
        let instance_tuple = factorial_proof::<GoldilocksField, PoseidonGoldilocksConfig, 2>(
            &config,
            instance_circuit_size,
        )
        .expect("instance");

        let mut builder = CircuitBuilder::<GoldilocksField, 2>::new(config);
        let mut pw = PartialWitness::new();

        let proof_with_pis = builder
            .add_virtual_proof_with_pis::<PoseidonGoldilocksConfig>(&instance_tuple.common_data);
        pw.set_proof_with_pis_target(&proof_with_pis, &instance_tuple.proof_with_pis);
        let public_inputs_hash_target = builder
            .hash_n_to_hash_no_pad::<<PoseidonGoldilocksConfig as GenericConfig<2>>::Hasher>(
            proof_with_pis.public_inputs.clone(),
        );

        let padded_verifier_data_target = builder.add_virtual_padded_verifier_data(
            instance_tuple.common_data.config.fri_config.cap_height,
            global_common_data.gates.len(),
            global_common_data.config.num_routed_wires,
            global_common_data.num_partial_products,
        );
        let padded_verifier_data = pad_verifier_data(
            &global_common_data,
            &VerifierCircuitData {
                verifier_only: instance_tuple.clone().verifier_only_data,
                common: instance_tuple.clone().common_data,
            },
        );
        // // Break it:
        // let _ = padded_verifier_data
        //     .selector_info
        //     .iter_mut()
        //     .map(|selector_info| {
        //         // selector_info.selector_bits[0] = !selector_info.selector_bits[0];
        //         // selector_info.padding_value = true;
        //     })
        //     .collect::<Vec<_>>();
        pw.set_padded_verifier_data_target(&padded_verifier_data_target, &padded_verifier_data);

        let vars = EvaluationTargets {
            local_constants: &proof_with_pis.proof.openings.constants,
            local_wires: &proof_with_pis.proof.openings.wires,
            public_inputs_hash: &public_inputs_hash_target,
        };

        let padded_gate_constraint_evaluations =
            padded_evaluate_gate_constraints_circuit::<_, PoseidonGoldilocksConfig, 2>(
                &mut builder,
                &global_common_data,
                &padded_verifier_data_target,
                instance_tuple.common_data.selectors_info.num_selectors(),
                vars,
            );
        let original_gate_constraint_evaluations =
            evaluate_gate_constraints_circuit::<_, PoseidonGoldilocksConfig, 2>(
                &mut builder,
                &instance_tuple.common_data,
                vars,
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

    // cargo test --package plonky2 --lib --all-features -- recursion::padding_experiments::tests::compare_padded_eval_gate_constraint_size --exact --nocapture
    #[test]
    fn compare_padded_eval_gate_constraint_size() {
        let config = CircuitConfig::standard_recursion_config();

        let instance_circuit_size = 12;
        let instance_tuple = factorial_proof::<GoldilocksField, PoseidonGoldilocksConfig, 2>(
            &config,
            instance_circuit_size,
        )
        .expect("dummy");
        println!("Comparing for circuit: ");
        display_common_data_info::<GoldilocksField, PoseidonGoldilocksConfig, 2>(
            &instance_tuple.common_data,
            format!("Factorial size {instance_circuit_size}"),
        );

        let padded_data = padded_eval_gate_constraints_circuit::<
            GoldilocksField,
            PoseidonGoldilocksConfig,
            2,
        >(config.clone(), &instance_tuple.common_data);
        display_common_data_info::<GoldilocksField, PoseidonGoldilocksConfig, 2>(
            &padded_data.common,
            "Padded Eval Gate Constraints".to_string(),
        );

        let unpadded_data = unpadded_eval_gate_constraints_circuit::<
            GoldilocksField,
            PoseidonGoldilocksConfig,
            2,
        >(config, &instance_tuple.common_data);
        display_common_data_info::<GoldilocksField, PoseidonGoldilocksConfig, 2>(
            &unpadded_data.common,
            "Unpadded Eval Gate Constraints".to_string(),
        );
    }

    // cargo test --package plonky2 --lib --all-features -- recursion::padding_experiments::tests::most_complex_circuit_info --exact --nocapture
    #[test]
    fn most_complex_circuit_info() {
        let config = CircuitConfig::standard_recursion_config();
        let degree_bits = 10;
        let circuit_name = format!("Most Complex Circuit, degree_bits: {degree_bits}");
        let proof_tuple: GoldilocksProofTuple =
            most_complex_circuit(&config, degree_bits).expect("Unable to form circuit");

        display_circuit_proof_info(&proof_tuple, circuit_name);
    }

    // cargo test --package plonky2 --lib --all-features -- recursion::padding_experiments::tests::factorial_circuit_info --exact --nocapture
    #[test]
    fn factorial_circuit_info() {
        let config = CircuitConfig::standard_recursion_config();
        let log2_size = 5;
        let circuit_name = format!("Factorial_{log2_size}");
        let proof_tuple: GoldilocksProofTuple =
            factorial_proof(&config, log2_size).expect("Unable to form circuit");

        display_circuit_proof_info(&proof_tuple, circuit_name);
    }

    // cargo test --package plonky2 --lib --all-features -- recursion::padding_experiments::tests::dummy_circuit_info --exact --nocapture
    #[test]
    fn dummy_circuit_info() {
        let config = CircuitConfig::standard_recursion_config();
        let log2_size = 3;
        let circuit_name = format!("Dummy_{log2_size}");
        let proof_tuple: GoldilocksProofTuple =
            dummy_proof(&config, log2_size).expect("Unable to form circuit");

        display_circuit_proof_info(&proof_tuple, circuit_name);
    }
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

    display_common_data_info::<F, C, D>(&proof_tuple.common_data, circuit_name.clone());

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
    // println!(
    //     "Length of sigma openings: {}",
    //     proof_tuple.proof_with_pis.proof.openings.plonk_sigmas.len()
    // );
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
    // println!(
    //     "Length of plonk_zs: {}",
    //     proof_tuple.proof_with_pis.proof.openings.plonk_zs.len()
    // );

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
    // println!(
    //     "Number of query rounds: {}",
    //     proof_tuple
    //         .proof_with_pis
    //         .proof
    //         .opening_proof
    //         .query_round_proofs
    //         .len()
    // );
    println!(
        "Number of final poly coefficients: {}",
        proof_tuple
            .proof_with_pis
            .proof
            .opening_proof
            .final_poly
            .len()
    );
    println!(
        "FRI Reduction Strategy: {:?}",
        proof_tuple.common_data.fri_params.reduction_arity_bits
    );
}

/// Custom way to display circuit common data.
pub fn display_common_data_info<F, C, const D: usize>(
    common_data: &CommonCircuitData<F, D>,
    circuit_name: String,
) where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
{
    println!("\nProperties of a {circuit_name} circuit and proof \n");

    // Configuration
    println!("\n{circuit_name} configuration data:");
    println!("Num challenges: {}", common_data.config.num_challenges);

    // FRI Configuration
    println!("\n{circuit_name} FRI config:");
    println!(
        "Cap size: {}",
        common_data.config.fri_config.num_cap_elements()
    );
    println!(
        "Number of query rounds: {}",
        common_data.config.fri_config.num_query_rounds
    );

    // Common Data
    println!("\n{circuit_name} common data:");
    println!("Degree: {}", common_data.degree());
    println!("Num Constants: {}", common_data.num_constants);
    println!("Num Public Inputs: {}", common_data.num_public_inputs);
    println!("Num Partial Products: {}", common_data.num_partial_products);
    println!("Number of sigma polynomials: {}", common_data.k_is.len());
    println!(
        "Degree of quotient polynomial: {}",
        common_data.quotient_degree()
    );
    println!(
        "Gate types: {:#?}",
        common_data
            .gates
            .iter()
            .map(|g| g.0.id())
            .collect::<Vec<_>>()
    );
    println!(
        "Number of selector polynomials: {}",
        common_data.selectors_info.num_selectors()
    );
}
