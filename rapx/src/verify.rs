//! The staged verification pipeline and crate-level verification driver.
//!
//! Contract-based, path-sensitive verification of safety properties: collect
//! targets and contracts, extract SCC-aware paths, slice them backward, execute
//! the relevant MIR symbolically, and discharge each property with Z3.

mod api_classify;
mod auto_trait;
mod call_summary;
mod checkpoint;
pub(crate) mod config;
mod contract;
mod debug_contracts;
mod display;
mod function_verifier;
mod loop_handling;
mod marker_trait;
mod path;
mod proof_cache;
mod property_checker;
mod report;
mod slicer;
mod target;
mod trait_ensurance;
mod type_invariants;
mod vm;

pub(crate) use self::{
    call_summary::{effects::has_registered_effect, function_var::supports_result as supports_function_var_result},
    slicer::RelevantItem,
    target::PrepareTargets,
    vm::{VmState, state::{AllocId, SafeDropEvent, SafeDropEventKind}},
};

use std::{sync::Arc, time::Instant};

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

use crate::analysis::Analysis;
use crate::compat::{FxHashMap, FxHashSet};
use crate::helpers::{
    fn_info::{get_cons, get_mutated_fields, get_muts},
    mir_utils,
    name::short_fn_name,
};

use self::{
    contract::{
        ContractExpr, ContractPlace, ContractProjection, PlaceBase, Property, PropertyArg,
        compound::register_compound_properties,
        ensures::get_trait_method_ensures,
    },
    display::{
        dedup_compound_props, emit_results_and_verdict, emit_verify_summary, fmt_contract_expanded,
        fmt_fn_path_with_bounds,
    },
    function_verifier::FunctionVerifier,
    config::{PostfixRepeat, VerifyConfig},
    loop_handling::LoopSensitivityAnalyzer,
    marker_trait::MarkerTraitVerifier,
    proof_cache::{VmCache, new_z3_context},
    report::{CheckResult, PropertyCheckResult},
    target::{FunctionTarget, VerifyTargetCollector, get_contract_from_annotation},
    trait_ensurance::TraitEnsuranceKind,
};

/// Collects verification targets, schedules checks, and emits their summaries.
pub(crate) struct VerifyDriver<'tcx> {
    /// Compiler context for target collection and verification.
    tcx: TyCtxt<'tcx>,
    /// Verification options shared with target preparation and call handling.
    config: Arc<VerifyConfig>,
}

impl<'tcx> VerifyDriver<'tcx> {
    /// Create a verification pass with the selected options.
    pub(crate) fn new(tcx: TyCtxt<'tcx>, config: Arc<VerifyConfig>) -> Self {
        Self { tcx, config }
    }

    fn repeat_rounds_for_target(&self, target: &FunctionTarget<'tcx>) -> (usize, Vec<usize>) {
        match &self.config.postfix_repeat {
            PostfixRepeat::Fixed(n) => (*n, (0..=*n).collect()),
            PostfixRepeat::Auto => {
                let repeat = LoopSensitivityAnalyzer::new(self.tcx).analyze(target);
                (repeat, (0..=repeat).collect())
            }
        }
    }

    /// With `--no-invariant-target`, generate verification sequences for each read method
    /// that chain through constructors and mutators.
    ///
    /// Produces sequences like:
    /// - `constructor → method`
    /// - `constructor → mutator → method`
    ///
    /// Each sequence propagates the constructor's `#[rapx::requires]` through
    /// the mutator chain to serve as entry assumptions for the read method.
    fn run_invless_sequences(&self, targets: &[FunctionTarget<'tcx>]) {
        for target in targets {
            let read_def_id = target.def_id;
            let cons = get_cons(self.tcx, read_def_id);
            if cons.is_empty() {
                continue;
            }
            let muts = get_muts(self.tcx, read_def_id);

            for &con_id in &cons {
                let con_target = self.build_virtual_target(target, read_def_id, con_id, &[]);
                self.verify_and_emit_sequence(read_def_id, &con_target, con_id, &[]);

                for &mut_id in &muts {
                    let con_target = self.build_virtual_target(target, read_def_id, con_id, &[mut_id]);
                    self.verify_and_emit_sequence(read_def_id, &con_target, con_id, &[mut_id]);
                }
            }
        }
    }

    fn build_virtual_target(
        &self,
        read_target: &FunctionTarget<'tcx>,
        read_def_id: DefId,
        con_id: DefId,
        mut_ids: &[DefId],
    ) -> FunctionTarget<'tcx> {
        let mut accumulated_requires: Vec<Property<'tcx>> = Vec::new();

        // Start with the constructor's requires, remapped to refer to struct
        // fields (self.field) instead of constructor parameters.
        let con_contracts: Vec<Property<'tcx>> = get_contract_from_annotation(self.tcx, con_id)
            .into_iter()
            .map(|c| remap_constructor_contract(c))
            .collect();
        accumulated_requires.extend(con_contracts);

        let mutated_fields: FxHashSet<_> = mut_ids
            .iter()
            .flat_map(|&mut_id| get_mutated_fields(self.tcx, mut_id))
            .collect();
        if !mutated_fields.is_empty() {
            accumulated_requires.retain(|prop| {
                let prop_fields = property_field_indices(prop);
                !prop_fields.iter().any(|f| mutated_fields.contains(f))
            });
        }

        // Also include the read method's own caller requires (which already
        // contains struct invariants merged by build_function_target).
        // This is broader than just `get_contract_from_annotation` because
        // it propagates struct-level properties even when the method has no
        // explicit `#[rapx::requires]`.
        accumulated_requires.extend(read_target.caller_requires.clone());

        FunctionTarget {
            def_id: read_def_id,
            body: read_target.body,
            callee_bodies: read_target.callee_bodies.clone(),
            owner_struct_def_id: read_target.owner_struct_def_id,
            checkpoints: read_target.checkpoints.clone(),
            callee_requires: read_target.callee_requires.clone(),
            caller_requires: accumulated_requires,
            struct_invariants: Vec::new(),
            type_invariants: Vec::new(),
            raw_ptr_deref_checks: read_target.raw_ptr_deref_checks.clone(),
            static_mut_checks: read_target.static_mut_checks.clone(),
        }
    }

    /// Run `verify_checkpoints` across `repeat_rounds`, collecting results and
    /// returning the crash message (if any round panicked).
    fn run_repeat_rounds(
        &self,
        target: &FunctionTarget<'tcx>,
        repeat_rounds: &[usize],
        skip_label: &str,
        all_results: &mut Vec<PropertyCheckResult<'tcx>>,
        trait_impl_limited: &mut bool,
    ) -> Option<String> {
        let z3_ctx = new_z3_context();
        let mut cache = VmCache::new(&z3_ctx, Arc::clone(&self.config));
        for &repeat in repeat_rounds {
            let verification_started = Instant::now();
            match mir_utils::catch_panic(|| FunctionVerifier::verify_checkpoints(self.tcx, target, repeat, Arc::clone(&self.config), &mut cache)) {
                Ok((report, limited)) => {
                    *trait_impl_limited |= limited;
                    rap_debug!(
                        "checked checkpoint paths for {} repeat {} in {:?}",
                        skip_label,
                        repeat,
                        verification_started.elapsed()
                    );
                    rap_debug!("{}", report.describe());
                    all_results.extend(report.results);
                }
                Err(msg) => {
                    rap_warn!("Skipping {} (repeat {}): {msg}", skip_label, repeat);
                    all_results.clear();
                    return Some(format!("repeat {repeat}: {msg}"));
                }
            }
        }
        None
    }

    fn verify_and_emit_sequence(
        &self,
        read_def_id: DefId,
        con_target: &FunctionTarget<'tcx>,
        con_id: DefId,
        mut_ids: &[DefId],
    ) {
        let mut all_results: Vec<PropertyCheckResult<'_>> = Vec::new();
        let mut trait_impl_limited = false;

        let (_, repeat_rounds) = self.repeat_rounds_for_target(con_target);
        let crashed = self.run_repeat_rounds(
            con_target,
            &repeat_rounds,
            &format!("constructor {}", self.tcx.def_path_str(con_id)),
            &mut all_results,
            &mut trait_impl_limited,
        );

        let read_name = short_fn_name(self.tcx, read_def_id);
        let con_name = short_fn_name(self.tcx, con_id);
        let mut chain_parts: Vec<String> = vec![con_name];
        for &mut_id in mut_ids {
            chain_parts.push(short_fn_name(self.tcx, mut_id));
        }
        chain_parts.push(read_name);
        let chain_label = chain_parts.join(" -> ");

        rap_info!("============================================================");
        rap_info!("[rapx::verify] sequence: {chain_label}");
        rap_info!("============================================================");

        if let Some(msg) = &crashed {
            rap_warn!("  result: UNKNOWN (verifier crashed: {msg})");
        } else if all_results.is_empty() {
            rap_info!("  result: SOUND (no unsafe checkpoints)");
        } else {
            emit_results_and_verdict(self.tcx, &all_results, trait_impl_limited);
        }
        rap_info!("");
    }
}

impl<'tcx> Analysis for VerifyDriver<'tcx> {
    /// Collect targets, run each function verifier, and emit a compact summary.
    ///
    /// For each target, extracts paths with increasing `postfix-repeat`
    /// levels from 0 to the configured maximum, running verification at each
    /// level. Earlier rounds use fewer loop unrollings; later rounds incrementally
    /// add deeper paths.
    fn run(&mut self) {
        register_compound_properties(self.tcx);

        let collection_started = Instant::now();
        rap_debug!("collecting verification targets");
        let mut collector = VerifyTargetCollector::collect_all(self.tcx, Arc::clone(&self.config));
        rap_debug!(
            "collected {} function targets and {} trait targets in {:?}",
            collector.function_targets.len(),
            collector.trait_targets.len(),
            collection_started.elapsed()
        );

        if self.config.debug_contracts {
            self.print_contracts_debug(&collector.function_targets, &collector.trait_targets);
            return;
        }

        // Verify every target, then merge results per function so that a
        // generic function's monomorphized instances are reported once.
        let mut by_fn: FxHashMap<
            DefId,
            (Vec<PropertyCheckResult<'tcx>>, Option<String>, bool, bool),
        > = FxHashMap::default();
        // Keep struct-invariant verdicts for later marker-trait obligations.
        let mut struct_invariant_results: FxHashMap<DefId, CheckResult> = FxHashMap::default();

        for target in &collector.function_targets {
            let target_path = fmt_fn_path_with_bounds(self.tcx, target.def_id);
            let target_started = Instant::now();
            rap_debug!("verifying target {target_path}");
            let mut all_results: Vec<PropertyCheckResult<'_>> = Vec::new();
            let mut fn_crashed: Option<String>;
            let mut trait_impl_limited = false;

            let (planned_repeat, repeat_rounds) = self.repeat_rounds_for_target(target);

            fn_crashed = self.run_repeat_rounds(
                target,
                &repeat_rounds,
                &format!("function {}", target_path),
                &mut all_results,
                &mut trait_impl_limited,
            );
            rap_debug!(
                "verified function paths for {target_path} in {:?}",
                target_started.elapsed()
            );

            if !target.struct_invariants.is_empty() && !self.config.skip_invariant {
                let verifier = FunctionVerifier::new_with_repeat(self.tcx, target, planned_repeat, Arc::clone(&self.config));
                trait_impl_limited |= verifier.is_trait_impl_limited();
                match mir_utils::catch_panic(|| verifier.verify_struct_invariants()) {
                    Ok(struct_report) => {
                        rap_debug!("{}", struct_report.describe());
                        if let Some(struct_id) = target.owner_struct_def_id {
                            let verdict = struct_report
                                .results
                                .iter()
                                .fold(CheckResult::ProvedByRule, |acc, r| {
                                    acc.and(r.result.clone())
                                });
                            struct_invariant_results
                                .entry(struct_id)
                                .and_modify(|v| *v = v.clone().and(verdict.clone()))
                                .or_insert(verdict);
                        }
                        all_results.extend(struct_report.results);
                    }
                    Err(msg) => {
                        rap_warn!("Skipping struct invariants for {} : {msg}", target_path);
                        all_results.clear();
                        fn_crashed = Some(format!("struct-invariant: {msg}"));
                    }
                }
            }

            if !target.type_invariants.is_empty() && !self.config.skip_invariant {
                let verifier = FunctionVerifier::new_with_repeat(self.tcx, target, planned_repeat, Arc::clone(&self.config));
                trait_impl_limited |= verifier.is_trait_impl_limited();
                match mir_utils::catch_panic(|| verifier.verify_type_invariants()) {
                    Ok(type_report) => {
                        rap_debug!("{}", type_report.describe());
                        all_results.extend(type_report.results);
                    }
                    Err(msg) => {
                        rap_warn!("Skipping type invariants for {} : {msg}", target_path);
                        all_results.clear();
                        fn_crashed = Some(format!("type-invariant: {msg}"));
                    }
                }
            }

            let all_callees_skipped = !target.checkpoints.is_empty()
                && target.checkpoints.iter().all(|ckpt| {
                    ckpt.callee.is_some_and(|callee| {
                        target
                            .callee_requires
                            .get(&callee)
                            .is_none_or(|c| c.is_empty())
                    })
                });
            let no_checkpoints = all_results.is_empty()
                && (target.checkpoints.is_empty() || all_callees_skipped)
                && target.raw_ptr_deref_checks.is_empty()
                && target.static_mut_checks.is_empty()
                && target.struct_invariants.is_empty()
                && (target.type_invariants.is_empty() || !target.has_checkable_checkpoint());

            let entry = by_fn
                .entry(target.def_id)
                .or_insert_with(|| (Vec::new(), None, false, false));
            entry.0.extend(all_results);
            if fn_crashed.is_some() {
                entry.1 = fn_crashed;
            }
            entry.2 |= no_checkpoints;
            entry.3 |= target.body.is_some() || trait_impl_limited;
        }

        let mut ordered: Vec<DefId> = by_fn.keys().copied().collect();
        ordered.sort_by_key(|d| self.tcx.def_path_str(*d));
        for def_id in ordered {
            let (all_results, fn_crashed, no_checkpoints, mono_limited) = by_fn.remove(&def_id).unwrap();
            let target_path = fmt_fn_path_with_bounds(self.tcx, def_id);

            if let Some(msg) = &fn_crashed {
                rap_info!("============================================================");
                rap_info!("[rapx::verify] function: {target_path}");
                rap_info!("============================================================");
                rap_warn!("  result: UNKNOWN (verifier crashed: {msg})");
                rap_info!("");
                continue;
            }

            if all_results.is_empty() {
                if no_checkpoints {
                    rap_info!("============================================================");
                    rap_info!("[rapx::verify] function: {target_path}");
                    rap_info!("============================================================");
                    if self.config.skip_invariant {
                        let cons = get_cons(self.tcx, def_id);
                        for con in &cons {
                            rap_info!("  + constructor: {}", self.tcx.def_path_str(*con));
                        }
                    }
                    rap_info!("  --- unsafe checkpoints ---");
                    rap_info!("      <none>");
                    rap_info!("        <none>");
                    rap_info!("  result: SOUND (no unsafe checkpoints)");
                    rap_info!("");
                }
                continue;
            }

            // When --no-invariant-target is set, skip standalone emission for methods that
            // have constructors — sequences will generate dedicated entries.
            if self.config.skip_invariant && !get_cons(self.tcx, def_id).is_empty() {
                continue;
            }

            emit_verify_summary(
                self.tcx,
                &target_path,
                def_id,
                &all_results,
                self.config.skip_invariant,
                mono_limited,
            );
        }

        let mut unsafe_traits: Vec<_> = collector
            .trait_targets
            .iter()
            .filter(|t| matches!(&t.kind, TraitEnsuranceKind::Unsafe(_)))
            .cloned()
            .collect();
        unsafe_traits.sort_by_key(|t| self.tcx.def_path_str(t.def_id));
        for trait_target in unsafe_traits {
            let TraitEnsuranceKind::Unsafe(ensures) = &trait_target.kind else {
                continue;
            };
            rap_info!("============================================================");
            rap_info!(
                "[rapx::verify] unsafe trait impl: {}",
                self.tcx.def_path_str(trait_target.def_id)
            );
            rap_info!("============================================================");
            if let Some(self_ty) = trait_target.self_ty_def_id {
                rap_info!("  impl for: {}", self.tcx.def_path_str(self_ty));
            } else {
                rap_info!(
                    "  impl: {}",
                    self.tcx.def_path_str(trait_target.impl_def_id)
                );
            }
            if ensures.is_empty() {
                rap_info!("  ensures: <none>");
            } else {
                rap_info!("  ensures (implementor must satisfy):");
                let mut checked_methods = FxHashSet::default();
                for item in self.tcx.associated_items(trait_target.impl_def_id).in_definition_order() {
                    let Some(trait_method) = item.trait_item_def_id() else {
                        continue;
                    };
                    if !ensures
                        .iter()
                        .any(|(name, _)| *name == self.tcx.def_path_str(trait_method))
                    {
                        continue;
                    }
                    checked_methods.insert(self.tcx.def_path_str(trait_method));
                    let postconditions = get_trait_method_ensures(self.tcx, item.def_id);
                    rap_info!("    fn {}:", item.name());
                    for property in dedup_compound_props(postconditions.iter()) {
                        let (call, _) = fmt_contract_expanded(
                            self.tcx,
                            property,
                            trait_target.self_ty_def_id,
                            Some(item.def_id),
                        );
                        rap_info!("      - {call}");
                    }
                    if postconditions.is_empty() || !self.tcx.is_mir_available(item.def_id) {
                        rap_warn!("      result: UNKNOWN (contract or MIR unavailable)");
                        continue;
                    }
                    let target = collector.build_function_target(item.def_id, None);
                    let (_, repeats) = self.repeat_rounds_for_target(&target);
                    let mut results = Vec::new();
                    let mut crashed = None;
                    for repeat in repeats {
                        let verifier = FunctionVerifier::new_with_repeat(self.tcx, &target, repeat, Arc::clone(&self.config));
                        match mir_utils::catch_panic(|| verifier.verify_postconditions(&postconditions)) {
                            Ok(report) => results.extend(report.results),
                            Err(message) => {
                                crashed = Some(message);
                                break;
                            }
                        }
                    }
                    if let Some(message) = crashed {
                        rap_warn!("      result: UNKNOWN (verifier crashed: {message})");
                    } else {
                        emit_results_and_verdict(self.tcx, &results, false);
                    }
                }
                for (method_name, contracts) in ensures {
                    if checked_methods.contains(method_name) {
                        continue;
                    }
                    rap_info!("    fn {method_name}:");
                    for property in dedup_compound_props(contracts.iter()) {
                        let (call, _) = fmt_contract_expanded(
                            self.tcx,
                            property,
                            trait_target.self_ty_def_id,
                            None,
                        );
                        rap_info!("      - {call}");
                    }
                    rap_warn!("      result: UNKNOWN (default method body not checked)");
                }
            }
            rap_info!("");
        }

        // Verify marker-trait (`Send`/`Sync`) impls structurally.
        let marker_targets: Vec<_> = collector
            .trait_targets
            .iter()
            .filter(|t| matches!(&t.kind, TraitEnsuranceKind::Marker(..)))
            .collect();
        if !marker_targets.is_empty() {
            MarkerTraitVerifier::new(self.tcx, &struct_invariant_results).emit(&marker_targets);
        }

        if self.config.skip_invariant {
            self.run_invless_sequences(&collector.function_targets);
        }
    }
}

/// Collect struct field indices referenced by a property's contract places.
///
/// Used to determine which invariants are invalidated when a mutator writes
/// to specific struct fields.
fn property_field_indices(property: &Property<'_>) -> Vec<usize> {
    let mut indices = Vec::new();
    for arg in property.args() {
        let place = match arg {
            PropertyArg::Expr(ContractExpr::Place(p)) => Some(p),
            _ => None,
        };
        if let Some(place) = place {
            for proj in &place.projections {
                match proj {
                    ContractProjection::Field { index, .. } => {
                        let idx = *index;
                        if !indices.contains(&idx) {
                            indices.push(idx);
                        }
                    }
                    ContractProjection::Downcast { .. } => {}
                    ContractProjection::ForEach => {}
                }
            }
        }
    }
    indices
}

/// Remap constructor parameter references in an atomic contract to fields of `self`.
fn remap_constructor_contract<'tcx>(property: Property<'tcx>) -> Property<'tcx> {
    fn remap_place_arg<'tcx>(arg: &PropertyArg<'tcx>) -> PropertyArg<'tcx> {
        let place = match arg {
            PropertyArg::Expr(ContractExpr::Place(p)) => p,
            _ => return arg.clone(),
        };
        let PlaceBase::Arg(field_idx) = place.base else {
            return arg.clone();
        };
        let projection = ContractProjection::Field {
            index: field_idx,
            ty: None,
        };
        let mut new_place = ContractPlace {
            base: PlaceBase::Arg(0),
            projections: vec![projection],
        };
        new_place.projections.extend(place.projections.iter().cloned());
        PropertyArg::Expr(ContractExpr::Place(new_place))
    }

    match property {
        Property::Atom(mut atom) => {
            atom.args = atom.args.iter().map(remap_place_arg).collect();
            Property::Atom(atom)
        }
        Property::And(and) => Property::And(and),
        Property::Or(or) => Property::Or(or),
    }
}
