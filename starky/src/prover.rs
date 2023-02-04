use alloc::vec::Vec;
use core::iter::once;

use anyhow::{ensure, Result};
use maybe_rayon::*;
use plonky2::field::extension::Extendable;
use plonky2::field::packable::Packable;
use plonky2::field::packed::PackedField;
use plonky2::field::polynomial::{PolynomialCoeffs, PolynomialValues};
use plonky2::field::types::Field;
use plonky2::field::zero_poly_coset::ZeroPolyOnCoset;
use plonky2::fri::oracle::PolynomialBatch;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::challenger::Challenger;
use plonky2::plonk::config::GenericConfig;
use plonky2::timed;
use plonky2::util::timing::TimingTree;
use plonky2::util::{log2_ceil, log2_strict, transpose};

use crate::config::StarkConfig;
use crate::consumer::basic::ConstraintConsumer;
use crate::cross_table_lookup::{CtlTableData, CtlCheckVars, CtlLinearCombChallenge, CtlChallenge, CtlColSet};
use crate::ir::Registers;
use crate::permutation::{
    compute_permutation_z_polys, get_n_permutation_challenge_sets, PermutationChallengeSet,
    PermutationCheckVars,
};
use crate::proof::{StarkOpeningSet, StarkProof, StarkProofWithPublicInputs};
use crate::stark::Stark;
use crate::vanishing_poly::eval_vanishing_poly;

// Compute all STARK trace commitments.
fn compute_trace_commitments<F, C, const D: usize>(
    config: &StarkConfig,
    trace_poly_values: &[Vec<PolynomialValues<F>>],
    timing: &mut TimingTree,
) -> Result<Vec<PolynomialBatch<F, C, D>>>
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
{
    let rate_bits = config.fri_config.rate_bits;
    let cap_height = config.fri_config.cap_height;

    Ok(timed!(
        timing,
        "compute trace commitments",
        trace_poly_values
            .par_iter()
            .cloned()
            .map(|trace| {
                let mut timing = TimingTree::default();
                PolynomialBatch::<F, C, D>::from_values(
                    // TODO: Cloning this isn't great; consider having `from_values` accept a reference,
                    // or having `compute_permutation_z_polys` read trace values from the `PolynomialBatch`.
                    trace,
                    rate_bits,
                    false,
                    cap_height,
                    &mut timing,
                    None,
                )
            })
            .collect::<Vec<_>>()
    ))
}

/// Make a new challenger, compute all STARK trace commitments and observe them in the challenger
pub fn start_multi_table_prover<F, C, const D: usize>(
    config: &StarkConfig,
    trace_poly_values: &[Vec<PolynomialValues<F>>],
    timing: &mut TimingTree,
) -> Result<(Vec<PolynomialBatch<F, C, D>>, Challenger<F, C::Hasher>)>
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
{
    let trace_commitments = compute_trace_commitments(config, trace_poly_values, timing)?;
    let mut challenger = Challenger::<F, C::Hasher>::new();
    for cap in trace_commitments.iter().map(|c| &c.merkle_tree.cap) {
        challenger.observe_cap(cap);
    }

    Ok((trace_commitments, challenger))
}

pub fn prove_no_ctl<F, C, S, const D: usize>(
    stark: &S,
    config: &StarkConfig,
    trace_poly_values: &[PolynomialValues<F>],
    public_inputs: Vec<F>,
    timing: &mut TimingTree,
) -> Result<StarkProofWithPublicInputs<F, C, D>>
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    S: Stark<F, ConstraintConsumer<F>>
        + Stark<<F as Packable>::Packing, ConstraintConsumer<<F as Packable>::Packing>>
        + Sync,
{
    let degree = trace_poly_values[0].len();
    let degree_bits = log2_strict(degree);
    let fri_params = config.fri_params(degree_bits);
    let rate_bits = config.fri_config.rate_bits;
    let cap_height = config.fri_config.cap_height;
    assert!(
        fri_params.total_arities() <= degree_bits + rate_bits - cap_height,
        "FRI total reduction arity is too large.",
    );

    let trace_commitment = timed!(
        timing,
        "compute trace commitment",
        PolynomialBatch::<F, C, D>::from_values(
            // TODO: Cloning this isn't great; consider having `from_values` accept a reference,
            // or having `compute_permutation_z_polys` read trace values from the `PolynomialBatch`.
            trace_poly_values.to_vec(),
            rate_bits,
            false,
            cap_height,
            timing,
            None,
        )
    );

    let trace_cap = trace_commitment.merkle_tree.cap.clone();
    let mut challenger = Challenger::new();
    challenger.observe_cap(&trace_cap);

    prove_single_table(
        stark,
        config,
        &trace_poly_values,
        &trace_commitment,
        None,
        &public_inputs,
        &mut challenger,
        timing,
    )
}

pub fn prove_single_table<F, C, S, const D: usize>(
    stark: &S,
    config: &StarkConfig,
    trace_poly_values: &[PolynomialValues<F>],
    trace_commitment: &PolynomialBatch<F, C, D>,
    ctl_data: Option<&CtlTableData<F>>,
    public_inputs: &[F],
    challenger: &mut Challenger<F, C::Hasher>,
    timing: &mut TimingTree,
) -> Result<StarkProofWithPublicInputs<F, C, D>>
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    S: Stark<F, ConstraintConsumer<F>>
        + Stark<<F as Packable>::Packing, ConstraintConsumer<<F as Packable>::Packing>>
        + Sync,
{

    let degree = trace_poly_values[0].len();
    let degree_bits = log2_strict(degree);
    let fri_params = config.fri_params(degree_bits);
    let rate_bits = config.fri_config.rate_bits;
    let cap_height = config.fri_config.cap_height;
    assert!(
        fri_params.total_arities() <= degree_bits + rate_bits - cap_height,
        "FRI total reduction arity is too large.",
    );

    // Permutation arguments.
    let permutation_zs_commitment_challenges =
        stark.metadata().uses_permutation_args().then(|| {
            let permutation_challenge_sets = get_n_permutation_challenge_sets(
                challenger,
                config.num_challenges,
                stark.metadata().permutation_batch_size(),
            );
            let permutation_z_polys = compute_permutation_z_polys::<F, C, S, D>(
                &stark,
                config,
                &trace_poly_values,
                &permutation_challenge_sets,
            );
            let permutation_zs_commitment = timed!(
                timing,
                "compute permutation Z commitments",
                PolynomialBatch::from_values(
                    permutation_z_polys,
                    rate_bits,
                    false,
                    config.fri_config.cap_height,
                    timing,
                    None,
                )
            );
            (permutation_zs_commitment, permutation_challenge_sets)
        });
    let permutation_zs_commitment = permutation_zs_commitment_challenges
        .as_ref()
        .map(|(comm, _)| comm);
    let permutation_zs_cap = permutation_zs_commitment
        .as_ref()
        .map(|commit| commit.merkle_tree.cap.clone());
    if let Some(cap) = &permutation_zs_cap {
        challenger.observe_cap(cap);
    }

    let ctl_zs_commitment_challenges_cols = ctl_data.map(|ctl_data| {
        let zs = ctl_data.zs();
        let commitment = timed!(
            timing,
            "compute CTL Z commitments",
            PolynomialBatch::<F, C, D>::from_values(
                zs,
                rate_bits,
                false,
                config.fri_config.cap_height,
                timing,
                None
            )
        );
        let challenges = ctl_data.challenges();
        let cols = ctl_data.cols();
        (commitment, challenges, cols)
    });

    let ctl_zs_commitment = ctl_zs_commitment_challenges_cols
        .as_ref()
        .map(|(comm, _, _)| comm);
    let ctl_zs_cap = ctl_zs_commitment
        .as_ref()
        .map(|c| c.merkle_tree.cap.clone());
    if let Some(cap) = &ctl_zs_cap {
        challenger.observe_cap(cap);
    }

    let alphas = challenger.get_n_challenges(config.num_challenges);
    let quotient_polys = compute_quotient_polys::<F, <F as Packable>::Packing, C, S, D>(
        &stark,
        &trace_commitment,
        &permutation_zs_commitment_challenges,
        &ctl_zs_commitment_challenges_cols,
        &public_inputs,
        alphas,
        degree_bits,
        config,
    );
    let all_quotient_chunks = quotient_polys
        .into_par_iter()
        .flat_map(|mut quotient_poly| {
            quotient_poly
                .trim_to_len(degree * stark.metadata().quotient_degree_factor())
                .expect("Quotient has failed, the vanishing polynomial is not divisible by Z_H");
            // Split quotient into degree-n chunks.
            quotient_poly.chunks(degree)
        })
        .collect();
    let quotient_commitment = timed!(
        timing,
        "compute quotient commitment",
        PolynomialBatch::from_coeffs(
            all_quotient_chunks,
            rate_bits,
            false,
            config.fri_config.cap_height,
            timing,
            None,
        )
    );
    let quotient_polys_cap = quotient_commitment.merkle_tree.cap.clone();
    challenger.observe_cap(&quotient_polys_cap);

    let zeta = challenger.get_extension_challenge::<D>();
    // To avoid leaking witness data, we want to ensure that our opening locations, `zeta` and
    // `g * zeta`, are not in our subgroup `H`. It suffices to check `zeta` only, since
    // `(g * zeta)^n = zeta^n`, where `n` is the order of `g`.
    let g = F::primitive_root_of_unity(degree_bits);
    ensure!(
        zeta.exp_power_of_2(degree_bits) != F::Extension::ONE,
        "Opening point is in the subgroup."
    );
    let openings = StarkOpeningSet::new(
        zeta,
        g,
        &trace_commitment,
        permutation_zs_commitment,
        ctl_zs_commitment,
        &quotient_commitment,
        degree_bits,
    );
    challenger.observe_openings(&openings.to_fri_openings());

    let initial_merkle_trees = once(trace_commitment)
        .chain(permutation_zs_commitment)
        .chain(ctl_zs_commitment)
        .chain(once(&quotient_commitment))
        .collect::<Vec<_>>();

    let opening_proof = timed!(
        timing,
        "compute openings proof",
        PolynomialBatch::prove_openings(
            &stark.metadata().fri_instance(
                zeta,
                g,
                config,
                ctl_data.map(|data| data.num_zs()).unwrap_or(0),
                degree_bits
            ),
            &initial_merkle_trees,
            challenger,
            &fri_params,
            timing,
        )
    );
    let proof = StarkProof {
        trace_cap: trace_commitment.merkle_tree.cap.clone(),
        permutation_zs_cap,
        ctl_zs_cap,
        quotient_polys_cap,
        openings,
        opening_proof,
    };

    Ok(StarkProofWithPublicInputs {
        proof,
        public_inputs: public_inputs.to_vec(),
    })
}

/// Computes the quotient polynomials `(sum alpha^i C_i(x)) / Z_H(x)` for `alpha` in `alphas`,
/// where the `C_i`s are the Stark constraints.
#[allow(clippy::type_complexity)] // FIXME: refactor `permutation_zs_commitment_challenges`
fn compute_quotient_polys<'a, F, P, C, S, const D: usize>(
    stark: &S,
    trace_commitment: &'a PolynomialBatch<F, C, D>,
    permutation_zs_commitment_challenges: &'a Option<(
        PolynomialBatch<F, C, D>,
        Vec<PermutationChallengeSet<F>>,
    )>,
    ctl_zs_commitment_challenges_cols: &'a Option<(
        PolynomialBatch<F, C, D>,
        (Vec<CtlLinearCombChallenge<F>>, Vec<CtlChallenge<F>>),
        Vec<CtlColSet>,
    )>,
    public_inputs: &[F],
    alphas: Vec<F>,
    degree_bits: usize,
    config: &StarkConfig,
) -> Vec<PolynomialCoeffs<F>>
where
    F: RichField + Extendable<D>,
    P: PackedField<Scalar = F>,
    C: GenericConfig<D, F = F>,
    S: Stark<P, ConstraintConsumer<P>> + Sync,
{
    let degree = 1 << degree_bits;
    let rate_bits = config.fri_config.rate_bits;

    let quotient_degree_bits = log2_ceil(stark.metadata().quotient_degree_factor());
    assert!(
        quotient_degree_bits <= rate_bits,
        "Having constraints of degree higher than the rate is not supported yet."
    );
    let step = 1 << (rate_bits - quotient_degree_bits);
    // When opening the `Z`s polys at the "next" point, need to look at the point `next_step` steps away.
    let next_step = 1 << quotient_degree_bits;

    // Evaluation of the first Lagrange polynomial on the LDE domain.
    let lagrange_first = PolynomialValues::selector(degree, 0).lde_onto_coset(quotient_degree_bits);
    // Evaluation of the last Lagrange polynomial on the LDE domain.
    let lagrange_last =
        PolynomialValues::selector(degree, degree - 1).lde_onto_coset(quotient_degree_bits);

    let z_h_on_coset = ZeroPolyOnCoset::<F>::new(degree_bits, quotient_degree_bits);

    // Retrieve the LDE values at index `i`.
    let get_trace_values_packed = |i_start| trace_commitment.get_lde_values_packed(i_start, step);

    // Last element of the subgroup.
    let last = F::primitive_root_of_unity(degree_bits).inverse();
    let size = degree << quotient_degree_bits;
    let coset = F::cyclic_subgroup_coset_known_order(
        F::primitive_root_of_unity(degree_bits + quotient_degree_bits),
        F::coset_shift(),
        size,
    );

    let ctl_zs_first_last = ctl_zs_commitment_challenges_cols.as_ref().map(|(c, _, _)| {
        let mut ctl_zs_first = Vec::with_capacity(c.polynomials.len());
        let mut ctl_zs_last = Vec::with_capacity(c.polynomials.len());
        c.polynomials
            .par_iter()
            .map(|p| {
                (
                    p.eval(F::ONE),
                    p.eval(F::primitive_root_of_unity(degree_bits).inverse()),
                )
            })
            .unzip_into_vecs(&mut ctl_zs_first, &mut ctl_zs_last);

        (ctl_zs_first, ctl_zs_last)
    });

    // We will step by `P::WIDTH`, and in each iteration, evaluate the quotient polynomial at
    // a batch of `P::WIDTH` points.
    let quotient_values = (0..size)
        .into_par_iter()
        .step_by(P::WIDTH)
        .flat_map_iter(|i_start| {
            let i_next_start = (i_start + next_step) % size;
            let i_range = i_start..i_start + P::WIDTH;

            let x = *P::from_slice(&coset[i_range.clone()]);
            let z_last = x - last;
            let lagrange_basis_first = *P::from_slice(&lagrange_first.values[i_range.clone()]);
            let lagrange_basis_last = *P::from_slice(&lagrange_last.values[i_range]);

            let mut consumer = ConstraintConsumer::new(
                P::ZEROS,
                alphas.clone(),
                z_last,
                lagrange_basis_first,
                lagrange_basis_last,
            );
            let vars = Registers {
                local_values: &get_trace_values_packed(i_start),
                next_values: &get_trace_values_packed(i_next_start),
                public_inputs: &public_inputs
                    .iter()
                    .map(|pi| (*pi).into())
                    .collect::<Vec<_>>(),
            };
            let permutation_check_data = permutation_zs_commitment_challenges.as_ref().map(
                |(permutation_zs_commitment, permutation_challenge_sets)| PermutationCheckVars {
                    local_zs: permutation_zs_commitment.get_lde_values_packed(i_start, step),
                    next_zs: permutation_zs_commitment.get_lde_values_packed(i_next_start, step),
                    permutation_challenge_sets: permutation_challenge_sets.to_vec(),
                },
            );

            let ctl_vars =
            ctl_zs_commitment_challenges_cols
                .as_ref()
                .map(|(commitment, challenges, cols)| {
                    let local_zs = commitment.get_lde_values_packed(i_start, step);
                    let next_zs = commitment.get_lde_values_packed(i_next_start, step);
                    let (linear_comb_challenges, challenges) = challenges.clone();
                    let cols = cols.clone();
                    let (first_zs, last_zs) = ctl_zs_first_last.clone().unwrap();

                    CtlCheckVars {
                        local_zs,
                        next_zs,
                        first_zs,
                        last_zs,
                        linear_comb_challenges,
                        challenges,
                        cols,
                    }
                });

            eval_vanishing_poly::<F, F, P, C, S, D, 1>(
                stark,
                config,
                vars,
                permutation_check_data,
                ctl_vars.as_ref(),
                &mut consumer,
            );

            let mut constraints_evals = consumer.into_accumulators();
            // We divide the constraints evaluations by `Z_H(x)`.
            let denominator_inv: P = z_h_on_coset.eval_inverse_packed(i_start);

            for eval in &mut constraints_evals {
                *eval *= denominator_inv;
            }

            let num_challenges = alphas.len();

            (0..P::WIDTH).map(move |i| {
                (0..num_challenges)
                    .map(|j| constraints_evals[j].as_slice()[i])
                    .collect()
            })
        })
        .collect::<Vec<_>>();

    transpose(&quotient_values)
        .into_par_iter()
        .map(PolynomialValues::new)
        .map(|values| values.coset_ifft(F::coset_shift()))
        .collect()
}
