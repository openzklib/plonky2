use std::collections::{HashMap, HashSet};
use std::time::Instant;

use log::info;

use crate::circuit_data::{
    CircuitConfig, CircuitData, CommonCircuitData, ProverCircuitData, ProverOnlyCircuitData,
    VerifierCircuitData, VerifierOnlyCircuitData,
};
use crate::field::cosets::get_unique_coset_shifts;
use crate::field::extension_field::Extendable;
use crate::gates::constant::ConstantGate;
use crate::gates::gate::{GateInstance, GateRef};
use crate::gates::noop::NoopGate;
use crate::generator::{CopyGenerator, RandomValueGenerator, WitnessGenerator};
use crate::hash::hash_n_to_hash;
use crate::permutation_argument::TargetPartitions;
use crate::polynomial::commitment::ListPolynomialCommitment;
use crate::polynomial::polynomial::PolynomialValues;
use crate::target::Target;
use crate::util::{log2_ceil, log2_strict, transpose};
use crate::wire::Wire;

pub struct CircuitBuilder<F: Extendable<D>, const D: usize> {
    pub(crate) config: CircuitConfig,

    /// The types of gates used in this circuit.
    gates: HashSet<GateRef<F, D>>,

    /// The concrete placement of each gate.
    gate_instances: Vec<GateInstance<F, D>>,

    /// The next available index for a public input.
    public_input_index: usize,

    /// The next available index for a VirtualAdviceTarget.
    virtual_target_index: usize,

    copy_constraints: Vec<(Target, Target)>,

    /// Generators used to generate the witness.
    generators: Vec<Box<dyn WitnessGenerator<F>>>,

    constants_to_targets: HashMap<F, Target>,
    targets_to_constants: HashMap<Target, F>,
}

impl<F: Extendable<D>, const D: usize> CircuitBuilder<F, D> {
    pub fn new(config: CircuitConfig) -> Self {
        CircuitBuilder {
            config,
            gates: HashSet::new(),
            gate_instances: Vec::new(),
            public_input_index: 0,
            virtual_target_index: 0,
            copy_constraints: Vec::new(),
            generators: Vec::new(),
            constants_to_targets: HashMap::new(),
            targets_to_constants: HashMap::new(),
        }
    }

    pub fn add_public_input(&mut self) -> Target {
        let index = self.public_input_index;
        self.public_input_index += 1;
        Target::PublicInput { index }
    }

    pub fn add_public_inputs(&mut self, n: usize) -> Vec<Target> {
        (0..n).map(|_i| self.add_public_input()).collect()
    }

    /// Adds a new "virtual" advice target. This is not an actual wire in the witness, but just a
    /// target that help facilitate witness generation. In particular, a generator can assign a
    /// values to a virtual target, which can then be copied to other (virtual or concrete) targets
    /// via `generate_copy`. When we generate the final witness (a grid of wire values), these
    /// virtual targets will go away.
    ///
    /// Since virtual targets are not part of the actual permutation argument, they cannot be used
    /// with `assert_equal`.
    pub fn add_virtual_advice_target(&mut self) -> Target {
        let index = self.virtual_target_index;
        self.virtual_target_index += 1;
        Target::VirtualAdviceTarget { index }
    }

    pub fn add_virtual_advice_targets(&mut self, n: usize) -> Vec<Target> {
        (0..n).map(|_i| self.add_virtual_advice_target()).collect()
    }

    pub fn add_gate_no_constants(&mut self, gate_type: GateRef<F, D>) -> usize {
        self.add_gate(gate_type, Vec::new())
    }

    /// Adds a gate to the circuit, and returns its index.
    pub fn add_gate(&mut self, gate_type: GateRef<F, D>, constants: Vec<F>) -> usize {
        // If we haven't seen a gate of this type before, check that it's compatible with our
        // circuit configuration, then register it.
        if !self.gates.contains(&gate_type) {
            self.check_gate_compatibility(&gate_type);
            self.gates.insert(gate_type.clone());
        }

        let index = self.gate_instances.len();

        self.add_generators(gate_type.0.generators(index, &constants));

        self.gate_instances.push(GateInstance {
            gate_type,
            constants,
        });
        index
    }

    fn check_gate_compatibility(&self, gate: &GateRef<F, D>) {
        assert!(
            gate.0.num_wires() <= self.config.num_wires,
            "{:?} requires {} wires, but our GateConfig has only {}",
            gate.0.id(),
            gate.0.num_wires(),
            self.config.num_wires
        );
    }

    /// Shorthand for `generate_copy` and `assert_equal`.
    /// Both elements must be routable, otherwise this method will panic.
    pub fn route(&mut self, src: Target, dst: Target) {
        self.generate_copy(src, dst);
        self.assert_equal(src, dst);
    }

    /// Adds a generator which will copy `src` to `dst`.
    pub fn generate_copy(&mut self, src: Target, dst: Target) {
        self.add_generator(CopyGenerator { src, dst });
    }

    /// Uses Plonk's permutation argument to require that two elements be equal.
    /// Both elements must be routable, otherwise this method will panic.
    pub fn assert_equal(&mut self, x: Target, y: Target) {
        assert!(
            x.is_routable(&self.config),
            "Tried to route a wire that isn't routable"
        );
        assert!(
            y.is_routable(&self.config),
            "Tried to route a wire that isn't routable"
        );
        self.copy_constraints.push((x, y));
    }

    pub fn add_generators(&mut self, generators: Vec<Box<dyn WitnessGenerator<F>>>) {
        self.generators.extend(generators);
    }

    pub fn add_generator<G: WitnessGenerator<F>>(&mut self, generator: G) {
        self.generators.push(Box::new(generator));
    }

    /// Returns a routable target with a value of 0.
    pub fn zero(&mut self) -> Target {
        self.constant(F::ZERO)
    }

    /// Returns a routable target with a value of 1.
    pub fn one(&mut self) -> Target {
        self.constant(F::ONE)
    }

    /// Returns a routable target with a value of 2.
    pub fn two(&mut self) -> Target {
        self.constant(F::TWO)
    }

    /// Returns a routable target with a value of `ORDER - 1`.
    pub fn neg_one(&mut self) -> Target {
        self.constant(F::NEG_ONE)
    }

    /// Returns a routable target with the given constant value.
    pub fn constant(&mut self, c: F) -> Target {
        if let Some(&target) = self.constants_to_targets.get(&c) {
            // We already have a wire for this constant.
            return target;
        }

        let gate = self.add_gate(ConstantGate::get(), vec![c]);
        let target = Target::Wire(Wire {
            gate,
            input: ConstantGate::WIRE_OUTPUT,
        });
        self.constants_to_targets.insert(c, target);
        self.targets_to_constants.insert(target, c);
        target
    }

    pub fn constants(&mut self, constants: &[F]) -> Vec<Target> {
        constants.iter().map(|&c| self.constant(c)).collect()
    }

    /// If the given target is a constant (i.e. it was created by the `constant(F)` method), returns
    /// its constant value. Otherwise, returns `None`.
    pub fn target_as_constant(&self, target: Target) -> Option<F> {
        self.targets_to_constants.get(&target).cloned()
    }

    /// The number of polynomial values that will be revealed per opening, both for the "regular"
    /// polynomials and for the Z polynomials. Because calculating these values involves a recursive
    /// dependence (the amount of blinding depends on the degree, which depends on the blinding),
    /// this function takes in an estimate of the degree.
    fn num_blinding_gates(&self, degree_estimate: usize) -> (usize, usize) {
        let fri_queries = self.config.fri_config.num_query_rounds;
        let arities: Vec<usize> = self
            .config
            .fri_config
            .reduction_arity_bits
            .iter()
            .map(|x| 1 << x)
            .collect();
        let total_fri_folding_points: usize = arities.iter().map(|x| x - 1).sum::<usize>();
        let final_poly_coeffs: usize = degree_estimate / arities.iter().sum::<usize>();
        let fri_openings = fri_queries * (1 + D * total_fri_folding_points + D * final_poly_coeffs);

        let regular_poly_openings = D + fri_openings;
        let z_openings = 2 * D + fri_openings;

        (regular_poly_openings, z_openings)
    }

    /// The number of polynomial values that will be revealed per opening, both for the "regular"
    /// polynomials (which are opened at only one location) and for the Z polynomials (which are
    /// opened at two).
    fn blinding_counts(&self) -> (usize, usize) {
        let num_gates = self.gates.len();
        let mut degree_estimate = 1 << log2_ceil(num_gates);

        loop {
            let (regular_poly_openings, z_openings) = self.num_blinding_gates(degree_estimate);

            // For most polynomials, we add one random element to offset each opened value.
            // But blinding Z is separate. For that, we add two random elements with a copy
            // constraint between them.
            let total_blinding_count = regular_poly_openings + 2 * z_openings;

            if num_gates + total_blinding_count <= degree_estimate {
                return (regular_poly_openings, z_openings);
            }

            // The blinding gates do not fit within our estimated degree; increase our estimate.
            degree_estimate *= 2;
        }
    }

    fn blind_and_pad(&mut self) {
        let (regular_poly_openings, z_openings) = self.blinding_counts();

        let num_routed_wires = self.config.num_routed_wires;
        let num_wires = self.config.num_wires;

        // For each "regular" blinding factor, we simply add a no-op gate, and insert a random value
        // for each wire.
        for _ in 0..regular_poly_openings {
            let gate = self.add_gate_no_constants(NoopGate::get());
            for w in 0..num_wires {
                self.add_generator(RandomValueGenerator {
                    target: Target::Wire(Wire { gate, input: w }),
                });
            }
        }

        // For each z poly blinding factor, we add two new gates with the same random value, and
        // enforce a copy constraint between them.
        // See https://mirprotocol.org/blog/Adding-zero-knowledge-to-Plonk-Halo
        for _ in 0..z_openings {
            let gate_1 = self.add_gate_no_constants(NoopGate::get());
            let gate_2 = self.add_gate_no_constants(NoopGate::get());

            for w in 0..num_routed_wires {
                self.add_generator(RandomValueGenerator {
                    target: Target::Wire(Wire {
                        gate: gate_1,
                        input: w,
                    }),
                });
                self.add_generator(CopyGenerator {
                    src: Target::Wire(Wire {
                        gate: gate_1,
                        input: w,
                    }),
                    dst: Target::Wire(Wire {
                        gate: gate_2,
                        input: w,
                    }),
                });
            }
        }

        while !self.gate_instances.len().is_power_of_two() {
            self.add_gate_no_constants(NoopGate::get());
        }
    }

    fn constant_polys(&self) -> Vec<PolynomialValues<F>> {
        let num_constants = self
            .gate_instances
            .iter()
            .map(|gate_inst| gate_inst.constants.len())
            .max()
            .unwrap();
        let constants_per_gate = self
            .gate_instances
            .iter()
            .map(|gate_inst| {
                let mut padded_constants = gate_inst.constants.clone();
                for _ in padded_constants.len()..num_constants {
                    padded_constants.push(F::ZERO);
                }
                padded_constants
            })
            .collect::<Vec<_>>();

        transpose(&constants_per_gate)
            .into_iter()
            .map(PolynomialValues::new)
            .collect()
    }

    fn sigma_vecs(&self, k_is: &[F]) -> Vec<PolynomialValues<F>> {
        let degree = self.gate_instances.len();
        let degree_log = log2_strict(degree);
        let mut target_partitions = TargetPartitions::new();

        for gate in 0..degree {
            for input in 0..self.config.num_routed_wires {
                target_partitions.add_partition(Target::Wire(Wire { gate, input }));
            }
        }

        for index in 0..self.public_input_index {
            target_partitions.add_partition(Target::PublicInput { index })
        }

        for &(a, b) in &self.copy_constraints {
            target_partitions.merge(a, b);
        }

        let wire_partitions = target_partitions.to_wire_partitions();
        wire_partitions.get_sigma_polys(degree_log, k_is)
    }

    /// Builds a "full circuit", with both prover and verifier data.
    pub fn build(mut self) -> CircuitData<F, D> {
        let start = Instant::now();
        info!(
            "degree before blinding & padding: {}",
            self.gate_instances.len()
        );
        self.blind_and_pad();
        let degree = self.gate_instances.len();
        info!("degree after blinding & padding: {}", degree);

        let constant_vecs = self.constant_polys();
        let constants_commitment = ListPolynomialCommitment::new(
            constant_vecs.into_iter().map(|v| v.ifft()).collect(),
            self.config.fri_config.rate_bits,
            false,
        );

        let k_is = get_unique_coset_shifts(degree, self.config.num_routed_wires);
        let sigma_vecs = self.sigma_vecs(&k_is);
        let sigmas_commitment = ListPolynomialCommitment::new(
            sigma_vecs.into_iter().map(|v| v.ifft()).collect(),
            self.config.fri_config.rate_bits,
            false,
        );

        let constants_root = constants_commitment.merkle_tree.root;
        let sigmas_root = sigmas_commitment.merkle_tree.root;
        let verifier_only = VerifierOnlyCircuitData {
            constants_root,
            sigmas_root,
        };

        let generators = self.generators;
        let prover_only = ProverOnlyCircuitData {
            generators,
            constants_commitment,
            sigmas_commitment,
        };

        // The HashSet of gates will have a non-deterministic order. When converting to a Vec, we
        // sort by ID to make the ordering deterministic.
        let mut gates = self.gates.iter().cloned().collect::<Vec<_>>();
        gates.sort_unstable_by_key(|gate| gate.0.id());

        let num_gate_constraints = gates
            .iter()
            .map(|gate| gate.0.num_constraints())
            .max()
            .expect("No gates?");

        let degree_bits = log2_strict(degree);

        // TODO: This should also include an encoding of gate constraints.
        let circuit_digest_parts = [constants_root.elements, sigmas_root.elements];
        let circuit_digest = hash_n_to_hash(circuit_digest_parts.concat(), false);

        let common = CommonCircuitData {
            config: self.config,
            degree_bits,
            gates,
            num_gate_constraints,
            k_is,
            circuit_digest,
        };

        info!("Building circuit took {}s", start.elapsed().as_secs_f32());
        CircuitData {
            prover_only,
            verifier_only,
            common,
        }
    }

    /// Builds a "prover circuit", with data needed to generate proofs but not verify them.
    pub fn build_prover(self) -> ProverCircuitData<F, D> {
        // TODO: Can skip parts of this.
        let CircuitData {
            prover_only,
            common,
            ..
        } = self.build();
        ProverCircuitData {
            prover_only,
            common,
        }
    }

    /// Builds a "verifier circuit", with data needed to verify proofs but not generate them.
    pub fn build_verifier(self) -> VerifierCircuitData<F, D> {
        // TODO: Can skip parts of this.
        let CircuitData {
            verifier_only,
            common,
            ..
        } = self.build();
        VerifierCircuitData {
            verifier_only,
            common,
        }
    }
}
