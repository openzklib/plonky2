use crate::field::extension::Extendable;
use crate::gates::noop::NoopGate;
use crate::hash::hash_types::RichField;
use crate::plonk::circuit_builder::CircuitBuilder;
use crate::plonk::circuit_data::{CircuitConfig, CircuitData, CommonCircuitData};
use crate::plonk::config::{AlgebraicHasher, GenericConfig};

/// Returns the `CircuitData` of a circuit whose builder has the `standard_recursion_config`
/// and no constraints added.
fn base_circuit_data<F, C, const D: usize>() -> CircuitData<F, C, D>
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
{
    let builder = CircuitBuilder::<F, D>::new(CircuitConfig::standard_recursion_config());
    builder.build::<C>()
}

/// Generate a dummy circuit with desired degree from `base_circuit_data`.
pub fn dummy_circuit<F: RichField + Extendable<D>, C: GenericConfig<D, F = F>, const D: usize>(
    degree_bits: usize,
) -> CircuitData<F, C, D> {
    use plonky2_util::ceil_div_usize;

    let common_data = base_circuit_data::<F, C, D>().common;
    let config = common_data.config.clone();
    assert!(
        !common_data.config.zero_knowledge,
        "Degree calculation can be off if zero-knowledge is on."
    );

    // Number of `NoopGate`s to add to get a circuit of size `degree` in the end.
    // Need to account for public input hashing, a `PublicInputGate` and a `ConstantGate`.
    let num_noop_gate = (1 << degree_bits) - ceil_div_usize(common_data.num_public_inputs, 8) - 2;

    let mut builder = CircuitBuilder::<F, D>::new(config);
    for _ in 0..num_noop_gate {
        builder.add_gate(NoopGate, vec![]);
    }
    for gate in &common_data.gates {
        builder.add_gate_to_gate_set(gate.clone());
    }
    for _ in 0..common_data.num_public_inputs {
        builder.add_virtual_public_input();
    }

    let circuit = builder.build::<C>();
    // What goes wrong if we remove this assertion?
    // assert_eq!(&circuit.common, &common_data);
    circuit
}

// Generates `CommonCircuitData` usable for recursion.
pub fn common_data_for_arity_2_circuit_recursion<F, C, const D: usize>(
    degree: usize,
) -> CommonCircuitData<F, D>
where
    C::Hasher: AlgebraicHasher<F>,
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
{
    let data0 = dummy_circuit::<F, C, D>(degree);
    let data1 = dummy_circuit(degree);
    println!("The base circuit common data \n{:?}", data0.common);
    let (data0, data1) = add_arity_2_recursion_layer(data0, data1);
    println!(
        "The common data after 1 arity-2 recursion layer \n{:?}",
        data0.common
    );

    // Repeat
    let (data0, data1) = add_arity_2_recursion_layer(data0, data1);
    println!(
        "The common data after 2 arity-2 recursion layers \n{:?}",
        data0.common
    );

    // Repeat
    let (data0, _data1) = add_arity_2_recursion_layer(data0, data1);
    println!(
        "The common data after 3 arity-2 recursion layers \n{:?}",
        data0.common
    );

    // // Repeat
    // let (data0, data1) = add_arity_2_recursion_layer(data0, data1);
    // println!(
    //     "The common data after 4 arity-2 recursion layers \n{:?}",
    //     data0.common
    // );

    // // Repeat
    // let (data0, data1) = add_arity_2_recursion_layer(data0, data1);
    // println!(
    //     "The common data after 5 arity-2 recursion layers \n{:?}",
    //     data0.common
    // );

    // // Repeat
    // let (data0, data1) = add_arity_2_recursion_layer(data0, data1);
    // println!(
    //     "The common data after 6 arity-2 recursion layers \n{:?}",
    //     data0.common
    // );
    data0.common
}

/// Given the `CircuitData` of two circuits, verify both circuits and return `CircuitData`.
/// It's convenient to make this composable with itself, so we return a clone of the circuit
/// data.
fn _add_arity_2_recursion_layer_old<F, C, const D: usize>(
    data0: CircuitData<F, C, D>,
    data1: CircuitData<F, C, D>,
) -> (CircuitData<F, C, D>, CircuitData<F, C, D>)
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    C::Hasher: AlgebraicHasher<F>,
{
    println!(
        "Starting recursion layer on CommonData with {:?} public inputs",
        data0.common.num_public_inputs
    );
    let mut builder = CircuitBuilder::<F, D>::new(CircuitConfig::standard_recursion_config());

    // Check first proof
    let proof = builder.add_virtual_proof_with_pis::<C>(&data0.common);
    let verifier_data =
        builder.add_virtual_verifier_data(data0.common.config.fri_config.cap_height);
    builder.verify_proof::<C>(&proof, &verifier_data, &data0.common);
    println!(
        "Builder has {:?} gates after first proof check",
        builder.num_gates()
    );

    // Check second proof
    let proof = builder.add_virtual_proof_with_pis::<C>(&data1.common);
    let verifier_data =
        builder.add_virtual_verifier_data(data1.common.config.fri_config.cap_height);
    builder.verify_proof::<C>(&proof, &verifier_data, &data1.common);
    println!(
        "Builder has {:?} gates after second proof check",
        builder.num_gates()
    );
    let return_data0 = builder.build();

    // Repeat
    let mut builder = CircuitBuilder::<F, D>::new(CircuitConfig::standard_recursion_config());

    // Check first proof
    let proof = builder.add_virtual_proof_with_pis::<C>(&data0.common);
    let verifier_data =
        builder.add_virtual_verifier_data(data0.common.config.fri_config.cap_height);
    builder.verify_proof::<C>(&proof, &verifier_data, &data0.common);
    println!(
        "Builder has {:?} gates after first proof check",
        builder.num_gates()
    );

    // Check second proof
    let proof = builder.add_virtual_proof_with_pis::<C>(&data1.common);
    let verifier_data =
        builder.add_virtual_verifier_data(data1.common.config.fri_config.cap_height);
    builder.verify_proof::<C>(&proof, &verifier_data, &data1.common);
    println!(
        "Builder has {:?} gates after second proof check",
        builder.num_gates()
    );
    let return_data1 = builder.build();
    println!(
        "After recursion layer, CommonData has {:?} public inputs",
        return_data0.common.num_public_inputs
    );

    (return_data0, return_data1)
}

fn arity_2_recursion<F, C, const D: usize>(
    data0: &CircuitData<F, C, D>,
    data1: &CircuitData<F, C, D>,
) -> CircuitData<F, C, D>
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    C::Hasher: AlgebraicHasher<F>,
{
    let mut builder = CircuitBuilder::<F, D>::new(CircuitConfig::standard_recursion_config());

    // Allocate proofs
    let proof0 = builder.add_virtual_proof_with_pis::<C>(&data0.common);
    // let verifier_data =
    //     builder.add_virtual_verifier_data(data0.common.config.fri_config.cap_height);
    // builder.verify_proof::<C>(&proof, &verifier_data, &data0.common);
    let proof1 = builder.add_virtual_proof_with_pis::<C>(&data1.common);
    let verifier_data = builder.add_verifier_data_public_inputs(); // Is this going to be the right data for verification?
    builder.verify_proof::<C>(&proof0, &verifier_data, &data0.common);
    builder.verify_proof::<C>(&proof1, &verifier_data, &data1.common);
    builder.build()
}

/// Given the `CircuitData` of two circuits, verify both circuits and return `CircuitData`.
/// It's convenient to make this composable with itself, so we return a clone of the circuit
/// data.
fn add_arity_2_recursion_layer<F, C, const D: usize>(
    data0: CircuitData<F, C, D>,
    data1: CircuitData<F, C, D>,
) -> (CircuitData<F, C, D>, CircuitData<F, C, D>)
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    C::Hasher: AlgebraicHasher<F>,
{
    println!(
        "Starting recursion layer on CommonData with {:?} public inputs",
        data0.common.num_public_inputs
    );
    let return_data0 = arity_2_recursion(&data0, &data1);
    let return_data1 = arity_2_recursion(&data0, &data1);
    println!(
        "After recursion layer, CommonData has {:?} public inputs",
        return_data0.common.num_public_inputs
    );

    (return_data0, return_data1)
}

#[test]
fn explore_recursive_circuit_data_by_degree() {
    use crate::plonk::config::PoseidonGoldilocksConfig;

    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;

    let degree = 10;
    let common_data = common_data_for_arity_2_circuit_recursion::<F, C, D>(degree);
    println!("The common data generated is {common_data:#?}");
    // degree: 5,  stab_degree: 13
    // degree: 10, stab_degree: 13
    // degree: 13, stab_degree: 13
    // degree: 14, stab_degree:
    // degree: 15, stab_degree: 14 ???
    // degree: 20, stab_degree: 14
    // degree: 23, stab_degree: panics
}
