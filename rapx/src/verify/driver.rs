//! Crate-level target scheduling and verification reporting.
//!
//! `VerifyDriver` collects targets and runs [`FunctionVerifier`] for each
//! function and path expansion depth.

use std::time::Instant;

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

use crate::analysis::Analysis;
use crate::cli::VerifyMode;
use crate::compat::{FxHashMap, FxHashSet};
use crate::helpers::{
    fn_info::{get_cons, get_mutated_fields, get_muts},
    mir_utils,
    name::short_fn_name,
};

use super::{
    contract::{
        ContractExpr, ContractPlace, ContractProjection, PlaceBase, Property, PropertyArg,
        PropertyKind, compound::register_compound_properties,
        ensures::get_trait_method_ensures,
    },
    display::{
        dedup_compound_props, emit_results_and_verdict, emit_verify_summary, fmt_contract_expanded,
        fmt_fn_path_with_bounds, fmt_fn_path_with_generics, fmt_fn_with_params,
    },
    function_verifier::FunctionVerifier,
    loop_handling::{LoopSensitivityAnalyzer, RepeatStrategy},
    marker_trait::MarkerTraitVerifier,
    proof_cache::{VmCache, new_z3_context},
    report::{CheckResult, PropertyCheckResult},
    target::{
        FunctionTarget, VerifyTargetCollector, get_contract_from_annotation,
    },
    trait_ensurance::{MarkerTraitKind, TraitEnsurance, TraitEnsuranceKind},
};

/// Crate-level analysis pass that schedules targets and emits their summaries.
pub(crate) struct VerifyDriver<'tcx> {
    tcx: TyCtxt<'tcx>,
    repeat_strategy: RepeatStrategy,
    mode: VerifyMode,
    skip_invariant: bool,
    crate_filter: Option<String>,
    module_filter: Option<String>,
    debug_contracts: bool,
    /// Per-struct verdict of the struct-invariant verification, consumed by the
    /// type-level `Allocated`/`Owning` checks to discharge the field invariants.
    struct_invariant_results: FxHashMap<DefId, CheckResult>,
}

impl<'tcx> VerifyDriver<'tcx> {
    /// Create the default verify pass for the current compiler type context.
    pub(crate) fn new(
        tcx: TyCtxt<'tcx>,
        repeat_strategy: RepeatStrategy,
        mode: VerifyMode,
        skip_invariant: bool,
        crate_filter: Option<String>,
        module_filter: Option<String>,
        debug_contracts: bool,
    ) -> Self {
        Self {
            tcx,
            repeat_strategy,
            mode,
            skip_invariant,
            crate_filter,
            module_filter,
            debug_contracts,
            struct_invariant_results: FxHashMap::default(),
        }
    }

    fn repeat_rounds_for_target(&self, target: &FunctionTarget<'tcx>) -> (usize, Vec<usize>) {
        match self.repeat_strategy {
            RepeatStrategy::Fixed(n) => (n, (0..=n).collect()),
            RepeatStrategy::Auto => {
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
                    let con_target =
                        self.build_virtual_target(target, read_def_id, con_id, &[mut_id]);
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
        let mut cache = VmCache::new(&z3_ctx);
        for &repeat in repeat_rounds {
            let verification_started = Instant::now();
            match mir_utils::catch_panic(|| FunctionVerifier::verify_checkpoints(self.tcx, target, repeat, &mut cache)) {
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
        let mut collector = VerifyTargetCollector::collect_all(
            self.tcx,
            self.mode,
            self.skip_invariant,
            self.crate_filter.clone(),
            self.module_filter.clone(),
        );
        rap_debug!(
            "collected {} function targets and {} trait targets in {:?}",
            collector.function_targets.len(),
            collector.trait_targets.len(),
            collection_started.elapsed()
        );

        if self.debug_contracts {
            self.print_contracts_debug(&collector.function_targets, &collector.trait_targets);
            return;
        }

        // Verify every target, then merge results per function so that a
        // generic function's monomorphized instances are reported once.
        let mut by_fn: FxHashMap<
            DefId,
            (Vec<PropertyCheckResult<'tcx>>, Option<String>, bool, bool),
        > = FxHashMap::default();

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

            if !target.struct_invariants.is_empty() && !self.skip_invariant {
                let verifier = FunctionVerifier::new_with_repeat(
                    self.tcx,
                    target,
                    planned_repeat,
                );
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
                            self.struct_invariant_results
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

            if !target.type_invariants.is_empty() && !self.skip_invariant {
                let verifier = FunctionVerifier::new_with_repeat(
                    self.tcx,
                    target,
                    planned_repeat,
                );
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
            let (all_results, fn_crashed, no_checkpoints, mono_limited) =
                by_fn.remove(&def_id).unwrap();
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
                    if self.skip_invariant {
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
            if self.skip_invariant && !get_cons(self.tcx, def_id).is_empty() {
                continue;
            }

            emit_verify_summary(
                self.tcx,
                &target_path,
                def_id,
                &all_results,
                self.skip_invariant,
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
                for item in self
                    .tcx
                    .associated_items(trait_target.impl_def_id)
                    .in_definition_order()
                {
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
                        let verifier = FunctionVerifier::new_with_repeat(
                            self.tcx,
                            &target,
                            repeat,
                        );
                        match mir_utils::catch_panic(|| {
                            verifier.verify_postconditions(&postconditions)
                        }) {
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
            MarkerTraitVerifier::new(self.tcx, &self.struct_invariant_results).emit(&marker_targets);
        }

        if self.skip_invariant {
            self.run_invless_sequences(&collector.function_targets);
        }
    }
}

impl<'tcx> VerifyDriver<'tcx> {
    fn print_contracts_debug(
        &self,
        targets: &[FunctionTarget<'tcx>],
        trait_targets: &[TraitEnsurance<'tcx>],
    ) {
        rap_info!("{:=<1$}", "", 76);
        rap_info!("[rapx::debug-contracts] Expanded Contract Assertions");
        rap_info!("{:=<1$}", "", 76);
        rap_info!("");

        let mut struct_groups: FxHashMap<DefId, Vec<&FunctionTarget<'tcx>>> =
            FxHashMap::default();
        let mut free_targets: Vec<&FunctionTarget<'tcx>> = Vec::new();

        for target in targets {
            if let Some(sid) = target.owner_struct_def_id {
                struct_groups.entry(sid).or_default().push(target);
            } else {
                free_targets.push(target);
            }
        }

        let mut struct_ids: Vec<_> = struct_groups.keys().copied().collect();
        struct_ids.sort_by_key(|did| self.tcx.def_path_str(*did));

        for struct_def_id in struct_ids {
            let methods = &struct_groups[&struct_def_id];
            let struct_name = self.tcx.def_path_str(struct_def_id);

            let inv_target = methods.iter().find(|t| !t.struct_invariants.is_empty());
            let have_invariants = inv_target.is_some();

            if have_invariants || methods.iter().any(|t| self.has_printable_contracts(t)) {
                rap_info!("{:=<1$}", "", 76);
                rap_info!("[rapx::debug-contracts] struct: {struct_name}");
                rap_info!("{:=<1$}", "", 76);
            }

            if let Some(tgt) = inv_target {
                rap_info!("  [Struct Invariants]:");
                let invariants = dedup_compound_props(tgt.struct_invariants.iter());
                let inv_count = invariants.len();
                for (ii, property) in invariants.iter().enumerate() {
                    let ibranch = if ii + 1 == inv_count { "`-" } else { "|-" };
                    let (call, meaning) = fmt_contract_expanded(
                        self.tcx,
                        property,
                        tgt.owner_struct_def_id,
                        Some(tgt.def_id),
                    );
                    self.print_contract_lines("  ", ibranch, &call, &meaning);
                }
                rap_info!("");
            }

            let mut printed = false;
            for (mi, target) in methods.iter().enumerate() {
                let is_last_method = mi + 1 == methods.len();
                let branch = if is_last_method { "`-" } else { "|-" };
                let cont = if is_last_method { "  " } else { "| " };
                if self.print_target_contracts(target, branch, cont) {
                    printed = true;
                }
            }
            if printed {
                rap_info!("{:=<1$}", "", 76);
                rap_info!("");
            }
        }

        for target in &free_targets {
            self.print_target_contracts(target, "- ", "  ");
        }

        let mut traits = trait_targets.iter().collect::<Vec<_>>();
        traits.sort_by_key(|t| self.tcx.def_path_str(t.def_id));
        for trait_target in traits {
            match &trait_target.kind {
                TraitEnsuranceKind::Unsafe(ensures) => {
                    let trait_path = self.tcx.def_path_str(trait_target.def_id);
                    rap_info!("{:=<1$}", "", 76);
                    rap_info!("[rapx::debug-contracts] unsafe trait: {trait_path}");
                    rap_info!("{:=<1$}", "", 76);
                    if let Some(self_ty) = trait_target.self_ty_def_id {
                        rap_info!("  impl for: {}", self.tcx.def_path_str(self_ty));
                    }
                    if ensures.is_empty() {
                        rap_info!("  ensures: <none>");
                    } else {
                        for (method_name, contracts) in ensures {
                            rap_info!("  fn {method_name}:");
                            for property in dedup_compound_props(contracts.iter()) {
                                let (call, meaning) = fmt_contract_expanded(
                                    self.tcx,
                                    property,
                                    trait_target.self_ty_def_id,
                                    Some(trait_target.def_id),
                                );
                                self.print_contract_lines("  ", "|-", &call, &meaning);
                            }
                        }
                    }
                    rap_info!("");
                }
                TraitEnsuranceKind::Marker(kind, obligations) => {
                    let name = match kind {
                        MarkerTraitKind::Send => "Send",
                        MarkerTraitKind::Sync => "Sync",
                    };
                    rap_info!("{:=<1$}", "", 76);
                    rap_info!("[rapx::debug-contracts] marker trait: {name}");
                    rap_info!("{:=<1$}", "", 76);
                    if let Some(self_ty) = trait_target.self_ty_def_id {
                        rap_info!("  impl for: {}", self.tcx.def_path_str(self_ty));
                    }
                    if obligations.is_empty() {
                        rap_info!("  obligations: <none>");
                    } else {
                        for property in obligations {
                            let (call, meaning) = fmt_contract_expanded(
                                self.tcx,
                                property,
                                trait_target.self_ty_def_id,
                                None,
                            );
                            self.print_contract_lines("  ", "|-", &call, &meaning);
                        }
                    }
                    rap_info!("");
                }
            }
        }
    }

    fn is_unsafe_fn(&self, def_id: DefId) -> bool {
        self.tcx.fn_sig(def_id).skip_binder().safety() == rustc_hir::Safety::Unsafe
    }

    fn has_caller_contracts(&self, target: &FunctionTarget<'tcx>, is_unsafe_fn: bool) -> bool {
        is_unsafe_fn
            && target
                .caller_requires
                .iter()
                .any(|p| p.kind() != Some(PropertyKind::Unknown))
    }

    fn has_printable_contracts(&self, target: &FunctionTarget<'tcx>) -> bool {
        let is_unsafe_fn = self.is_unsafe_fn(target.def_id);
        self.has_caller_contracts(target, is_unsafe_fn)
            || target
                .callee_requires
                .values()
                .any(|c| c.iter().any(|p| p.kind() != Some(PropertyKind::Unknown)))
    }

    fn print_contract_lines(&self, prefix: &str, branch: &str, call: &str, meaning: &str) {
        rap_info!("{prefix}{branch} {call}");
        let cont = if branch == "`-" { "  " } else { "| " };
        for line in meaning.lines() {
            rap_info!("{prefix}{cont} {line}");
        }
    }

    fn print_target_contracts(
        &self,
        target: &FunctionTarget<'tcx>,
        branch: &str,
        cont: &str,
    ) -> bool {
        let (arg_names_typed, ret_ty) = self.resolve_arg_names_with_types(target.def_id);
        let is_unsafe_fn = self.is_unsafe_fn(target.def_id);

        let target_path = fmt_fn_path_with_generics(self.tcx, target.def_id);
        let short_name = short_fn_name(self.tcx, target.def_id);

        let has_caller = self.has_caller_contracts(target, is_unsafe_fn);
        let mut callee_ids: Vec<_> = target.callee_requires.keys().copied().collect();
        callee_ids.retain(|did| {
            target
                .callee_requires
                .get(did)
                .is_some_and(|c| c.iter().any(|p| p.kind() != Some(PropertyKind::Unknown)))
        });
        callee_ids.sort_by_key(|did| self.tcx.def_path_str(*did));
        let has_callees = !callee_ids.is_empty();

        if !has_caller && !has_callees {
            return false;
        }

        let fn_display = fmt_fn_with_params(&target_path, &arg_names_typed, ret_ty.as_deref());
        let header = format!("--- method: {short_name}");
        let dashes = 72usize.saturating_sub(header.len());
        rap_info!("{branch} {header} {}", "-".repeat(dashes));
        rap_info!("{cont}  {fn_display}");

        // Caller Contracts (only for unsafe functions)
        if has_caller {
            rap_info!("{cont}  [Caller Contracts]:");
            let caller_props = dedup_compound_props(
                target
                    .caller_requires
                    .iter()
                    .filter(|p| p.kind() != Some(PropertyKind::Unknown)),
            );
            for (pi, property) in caller_props.iter().enumerate() {
                let is_last = pi + 1 == caller_props.len();
                let pbranch = if is_last { "`-" } else { "|-" };
                let (call, meaning) = fmt_contract_expanded(
                    self.tcx,
                    property,
                    target.owner_struct_def_id,
                    Some(target.def_id),
                );
                self.print_contract_lines(&format!("{cont}  "), pbranch, &call, &meaning);
            }
            if !has_callees {
                rap_info!("");
            }
        }

        // Callee Contracts (for each unsafe callee)
        if has_callees {
            rap_info!("{cont}  [Unsafe Callees]:");
            for (ci, &callee_id) in callee_ids.iter().enumerate() {
                let is_last_callee = ci + 1 == callee_ids.len();
                let cbranch = if is_last_callee { "`-" } else { "|-" };
                let ccont = if is_last_callee { "  " } else { "| " };
                let contracts = target.callee_requires.get(&callee_id).unwrap();
                let (callee_typed, callee_ret) = self.resolve_arg_names_with_types(callee_id);
                let callee_path = fmt_fn_path_with_generics(self.tcx, callee_id);
                rap_info!(
                    "{cont}  {cbranch} {}",
                    fmt_fn_with_params(&callee_path, &callee_typed, callee_ret.as_deref())
                );
                let props = dedup_compound_props(
                    contracts
                        .iter()
                        .filter(|p| p.kind() != Some(PropertyKind::Unknown)),
                );
                for (pi, property) in props.iter().enumerate() {
                    let is_last_prop = pi + 1 == props.len();
                    let pbranch = if is_last_prop { "`-" } else { "|-" };
                    let (call, meaning) =
                        fmt_contract_expanded(self.tcx, property, None, Some(callee_id));
                    self.print_contract_lines(
                        &format!("{cont}  {ccont}"),
                        pbranch,
                        &call,
                        &meaning,
                    );
                }
            }
        }

        rap_info!("");
        true
    }

    fn resolve_arg_names_with_types(
        &self,
        def_id: DefId,
    ) -> (Vec<String>, Option<String>) {
        if !self.tcx.is_mir_available(def_id) {
            return (Vec::new(), None);
        }
        let body = self.tcx.optimized_mir(def_id);
        let args: Vec<String> = body
            .local_decls
            .iter()
            .enumerate()
            .skip(1)
            .take(body.arg_count)
            .map(|(i, decl)| {
                let name = {
                    let span = decl.source_info.span;
                    self.tcx
                        .sess
                        .source_map()
                        .span_to_snippet(span)
                        .unwrap_or_else(|_| format!("_{}", i))
                };
                let ty = decl.ty.to_string();
                format!("{name}: {ty}")
            })
            .collect();
        let ret_ty = self.tcx.fn_sig(def_id).skip_binder().output().skip_binder();
        let ret_ty = if ret_ty.is_unit() {
            None
        } else {
            Some(ret_ty.to_string())
        };
        (args, ret_ty)
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

/// Whether an invariant targets the function's return value (as opposed to a
/// parameter / the receiver).  Only `Atom` invariants carry a first-argument
/// place; `And`/`Or` invariants have no `target_place`, so they are never
/// treated as return-value invariants.
fn remap_constructor_contract<'tcx>(
    property: Property<'tcx>,
) -> Property<'tcx> {

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
        new_place
            .projections
            .extend(place.projections.iter().cloned());
        PropertyArg::Expr(ContractExpr::Place(new_place))
    }

    let new_args: Vec<PropertyArg<'tcx>> = property
        .args()
        .iter()
        .map(|arg| remap_place_arg(arg))
        .collect();

    match property {
        Property::Atom(mut atom) => {
            atom.args = new_args;
            Property::Atom(atom)
        }
        Property::And(and) => Property::And(and),
        Property::Or(or) => Property::Or(or),
    }
}
