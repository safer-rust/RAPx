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
use crate::contract::{
    compound::register_compound_properties, ensures::get_trait_method_ensures,
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

    /// Run `verify_checkpoints` at every repeat depth up to `max_repeat`.
    fn run_repeat_rounds(
        &self,
        target: &FunctionTarget<'tcx>,
        max_repeat: usize,
        all_results: &mut Vec<PropertyCheckResult<'tcx>>,
        limits: &mut VerificationLimits,
    ) {
        let z3_ctx = new_z3_context();
        let mut cache = VmCache::new(&z3_ctx);
        for repeat in 0..=max_repeat {
            let (results, round_limits) = FunctionVerifier::verify_checkpoints(self.tcx, target, repeat, Rc::clone(&self.config), &mut cache);
            limits.merge(round_limits);
            all_results.extend(results);
        }
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
            if !target.invariants.is_empty() {
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
                    rap_info!("  result: SOUND (no properties to check)");
                    rap_info!("");
                }
                continue;
            }

            emit_verify_summary(&target_path, &all_results, limits);
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
    }
}
