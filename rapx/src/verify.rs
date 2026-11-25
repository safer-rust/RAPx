//! The staged verification pipeline and crate-level verification driver.
//!
//! Contract-based, path-sensitive verification of safety properties: collect
//! targets and contracts, extract SCC-aware paths, slice them backward, execute
//! the relevant MIR symbolically, and discharge each property with Z3.

mod alias;
mod auto_trait;
mod checkpoint;
pub(crate) mod config;
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
mod vm;

pub(crate) use crate::analysis::dataflow::call_summary;
pub(crate) use self::target::PrepareTargets;

use std::rc::Rc;

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

use crate::analysis::Analysis;
use crate::compat::{FxHashMap, FxHashSet};
use crate::util::{
    fn_info::{get_cons, get_mutated_fields, get_muts},
    name::short_fn_name,
};
use crate::contract::{
    ContractExpr, ContractPlace, ContractProjection, PlaceBase, Property, PropertyArg,
    annotation::get_contract_from_annotation, compound::register_compound_properties,
    ensures::get_trait_method_ensures,
};
use self::{
    config::{PostfixRepeat, VerifyConfig},
    display::{
        dedup_compound_props, emit_results_and_verdict, emit_verify_summary, fmt_contract_expanded,
        fmt_fn_path_with_bounds, print_contracts_debug,
    },
    function_verifier::FunctionVerifier,
    loop_handling::LoopSensitivityAnalyzer,
    marker_trait::MarkerTraitVerifier,
    proof_cache::{VmCache, new_z3_context},
    report::{PropertyCheckResult, VerificationLimits},
    target::{FunctionTarget, VerifyTargetCollector},
    trait_ensurance::TraitEnsuranceKind,
};

/// Collects verification targets, schedules checks, and emits their summaries.
pub(crate) struct VerifyDriver<'tcx> {
    /// Compiler context for target collection and verification.
    tcx: TyCtxt<'tcx>,
    /// Verification options shared with target preparation and call handling.
    config: Rc<VerifyConfig>,
}

#[derive(Default)]
struct FunctionVerdicts<'tcx> {
    results: Vec<PropertyCheckResult<'tcx>>,
    has_obligations: bool,
    limits: VerificationLimits,
}

impl<'tcx> VerifyDriver<'tcx> {
    /// Create a verification pass with the selected options.
    pub(crate) fn new(tcx: TyCtxt<'tcx>, config: Rc<VerifyConfig>) -> Self {
        Self { tcx, config }
    }

    fn max_repeat_for_target(&self, target: &FunctionTarget<'tcx>) -> usize {
        match &self.config.postfix_repeat {
            PostfixRepeat::Fixed(n) => *n,
            PostfixRepeat::Auto => LoopSensitivityAnalyzer::new(self.tcx).analyze(target),
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
    /// TODO: This sequence analysis is incomplete; it currently considers at most one mutator.
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

        let mutated_fields: FxHashSet<_> = mut_ids.iter().flat_map(|&id| get_mutated_fields(self.tcx, id)).collect();
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
            array_length_limited: read_target.array_length_limited,
            callee_bodies: read_target.callee_bodies.clone(),
            owner_struct_def_id: read_target.owner_struct_def_id,
            checkpoints: read_target.checkpoints.clone(),
            callee_requires: read_target.callee_requires.clone(),
            caller_requires: accumulated_requires,
            invariants: Vec::new(),
            raw_ptr_deref_checks: read_target.raw_ptr_deref_checks.clone(),
            static_mut_checks: read_target.static_mut_checks.clone(),
        }
    }

    /// Run `verify_checkpoints` at every repeat depth up to `max_repeat`.
    fn run_repeat_rounds(
        &self,
        target: &FunctionTarget<'tcx>,
        max_repeat: usize,
        all_results: &mut Vec<PropertyCheckResult<'tcx>>,
        limits: &mut VerificationLimits,
    ) {
        let z3_ctx = new_z3_context();
        let mut cache = VmCache::new(&z3_ctx, self.config.constructor_mir_mode());
        for repeat in 0..=max_repeat {
            let (results, round_limits) = FunctionVerifier::verify_checkpoints(self.tcx, target, repeat, Rc::clone(&self.config), &mut cache);
            limits.merge(round_limits);
            all_results.extend(results);
        }
    }

    fn verify_and_emit_sequence(
        &self,
        read_def_id: DefId,
        con_target: &FunctionTarget<'tcx>,
        con_id: DefId,
        mut_ids: &[DefId],
    ) {
        let mut all_results: Vec<PropertyCheckResult<'_>> = Vec::new();
        let mut limits = VerificationLimits::default();
        let max_repeat = self.max_repeat_for_target(con_target);
        self.run_repeat_rounds(con_target, max_repeat, &mut all_results, &mut limits);

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

        if all_results.is_empty() && !limits.path_limited {
            rap_info!("  result: SOUND (no unsafe checkpoints)");
        } else {
            emit_results_and_verdict(&all_results, limits);
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
        let mut collector = VerifyTargetCollector::collect_all(self.tcx, Rc::clone(&self.config));
        if self.config.debug_contracts {
            print_contracts_debug(self.tcx, &collector.function_targets, &collector.trait_targets);
            return;
        }

        // Merge target results per function so monomorphized instances are reported once.
        let mut function_verdicts: FxHashMap<DefId, FunctionVerdicts<'tcx>> = FxHashMap::default();
        for target in &collector.function_targets {
            let mut all_results: Vec<PropertyCheckResult<'_>> = Vec::new();
            let mut limits = VerificationLimits::default();
            let max_repeat = self.max_repeat_for_target(target);
            // Check each repeat depth, collecting checkpoint results and coverage limits.
            self.run_repeat_rounds(target, max_repeat, &mut all_results, &mut limits);

            // Recheck collected invariants at function exits after checkpoint verification.
            if !target.invariants.is_empty() && !self.config.skip_invariant {
                let verifier = FunctionVerifier::new(self.tcx, target, max_repeat, None, Rc::clone(&self.config));
                limits.merge(verifier.limits());
                all_results.extend(verifier.verify_invariants());
            }

            let no_obligations = all_results.is_empty()
                && target.checkpoints.iter().all(|ckpt| ckpt.callee.is_some() && target.properties_for_callsite(ckpt).is_empty())
                && target.raw_ptr_deref_checks.is_empty()
                && target.static_mut_checks.is_empty()
                && target.invariants.is_empty();

            limits.mono_limited |= target.body.is_some() && !target.array_length_limited;
            limits.array_length_limited |= target.array_length_limited;
            let entry = function_verdicts.entry(target.def_id).or_default();
            entry.results.extend(all_results);
            entry.has_obligations |= !no_obligations;
            entry.limits.merge(limits);
        }

        let mut ordered: Vec<DefId> = function_verdicts.keys().copied().collect();
        ordered.sort_by_key(|d| self.tcx.def_path_str(*d));
        for def_id in ordered {
            let FunctionVerdicts { results: all_results, has_obligations, limits } =
                function_verdicts.remove(&def_id).unwrap();
            let target_path = fmt_fn_path_with_bounds(self.tcx, def_id);

            if all_results.is_empty() && !limits.path_limited {
                if !has_obligations {
                    rap_info!("============================================================");
                    rap_info!("[rapx::verify] function: {target_path}");
                    rap_info!("============================================================");
                    if self.config.skip_invariant {
                        let cons = get_cons(self.tcx, def_id);
                        for con in &cons {
                            rap_info!("  + constructor: {}", self.tcx.def_path_str(*con));
                        }
                    }
                    rap_info!("  result: SOUND (no properties to check)");
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
                limits,
            );
        }

        let marker_verifier = MarkerTraitVerifier::new(self.tcx);
        for trait_target in std::mem::take(&mut collector.trait_targets) {
            let TraitEnsuranceKind::Unsafe(ensures) = &trait_target.kind else {
                marker_verifier.emit(&[&trait_target]);
                continue;
            };
            rap_info!("============================================================");
            rap_info!("[rapx::verify] unsafe trait impl: {}", self.tcx.def_path_str(trait_target.def_id));
            rap_info!("============================================================");
            if let Some(self_ty) = trait_target.self_ty_def_id {
                rap_info!("  impl for: {}", self.tcx.def_path_str(self_ty));
            } else {
                rap_info!("  impl: {}", self.tcx.def_path_str(trait_target.impl_def_id));
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
                    if !ensures.iter().any(|(name, _)| *name == self.tcx.def_path_str(trait_method)) {
                        continue;
                    }
                    checked_methods.insert(self.tcx.def_path_str(trait_method));
                    let postconditions = get_trait_method_ensures(self.tcx, item.def_id);
                    rap_info!("    fn {}:", item.name());
                    for property in dedup_compound_props(postconditions.iter()) {
                        let (call, _) = fmt_contract_expanded(
                            self.tcx, property, trait_target.self_ty_def_id, Some(item.def_id),
                        );
                        rap_info!("      - {call}");
                    }
                    if postconditions.is_empty() || !self.tcx.is_mir_available(item.def_id) {
                        rap_warn!("      result: UNKNOWN (contract or MIR unavailable)");
                        continue;
                    }
                    let target = collector.build_function_target(item.def_id, None);
                    let max_repeat = self.max_repeat_for_target(&target);
                    let mut results = Vec::new();
                    let mut limits = VerificationLimits::default();
                    for repeat in 0..=max_repeat {
                        let verifier = FunctionVerifier::new(self.tcx, &target, repeat, None, Rc::clone(&self.config));
                        limits.merge(verifier.limits());
                        results.extend(verifier.verify_postconditions(&postconditions));
                    }
                    emit_results_and_verdict(&results, limits);
                }
                for (method_name, contracts) in ensures {
                    if checked_methods.contains(method_name) {
                        continue;
                    }
                    rap_info!("    fn {method_name}:");
                    for property in dedup_compound_props(contracts.iter()) {
                        let (call, _) = fmt_contract_expanded(self.tcx, property, trait_target.self_ty_def_id, None);
                        rap_info!("      - {call}");
                    }
                    rap_warn!("      result: UNKNOWN (default method body not checked)");
                }
            }
            rap_info!("");
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
            PropertyArg::Expr(ContractExpr::Place(p)) | PropertyArg::ForEach(ContractExpr::Place(p)) => Some(p),
            _ => None,
        };
        if let Some(place) = place {
            for proj in &place.projections {
                match proj {
                    ContractProjection::Field { index } => {
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
            PropertyArg::Expr(ContractExpr::Place(p)) | PropertyArg::ForEach(ContractExpr::Place(p)) => p,
            _ => return arg.clone(),
        };
        let PlaceBase::Arg(field_idx) = place.base else {
            return arg.clone();
        };
        let projection = ContractProjection::Field { index: field_idx };
        let mut new_place = ContractPlace { base: PlaceBase::Arg(0), projections: vec![projection] };
        new_place.projections.extend(place.projections.iter().cloned());
        match arg {
            PropertyArg::ForEach(_) => PropertyArg::ForEach(ContractExpr::Place(new_place)),
            _ => PropertyArg::Expr(ContractExpr::Place(new_place)),
        }
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
