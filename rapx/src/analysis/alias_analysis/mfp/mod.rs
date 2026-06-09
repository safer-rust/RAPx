pub mod interproc;
pub mod intraproc;
pub mod transfer;

use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def_id::DefId;
use rustc_middle::mir::{Operand, TerminatorKind};
use rustc_middle::ty::{self, TyCtxt};
use rustc_mir_dataflow::Analysis;
use std::cell::RefCell;
use std::rc::Rc;

use super::{AliasAnalysis, FnAliasMap, FnAliasPairs};
use crate::analysis::Analysis as RapxAnalysis;
use intraproc::FnAliasAnalyzer;

/// MFP-based alias analyzer
pub struct MfpAliasAnalyzer<'tcx> {
    tcx: TyCtxt<'tcx>,
    /// Function summaries (alias relationships between arguments and return values)
    fn_map: FxHashMap<DefId, FnAliasPairs>,
}

impl<'tcx> MfpAliasAnalyzer<'tcx> {
    /// Create a new MFP alias analyzer
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        MfpAliasAnalyzer {
            tcx,
            fn_map: FxHashMap::default(),
        }
    }

    /// Get argument count for a function (returns None if MIR not available)
    fn get_arg_count(&self, def_id: DefId) -> Option<usize> {
        if !self.tcx.is_mir_available(def_id) {
            return None;
        }
        // Skip const contexts (only applicable to local functions)
        if let Some(local_def_id) = def_id.as_local() {
            if self.tcx.hir_body_const_context(local_def_id).is_some() {
                return None;
            }
        }
        let body = self.tcx.optimized_mir(def_id);
        Some(body.arg_count)
    }

    /// Analyze a single function
    fn analyze_function(
        &mut self,
        def_id: DefId,
        fn_summaries: &Rc<RefCell<FxHashMap<DefId, FnAliasPairs>>>,
    ) {
        let fn_name = self.tcx.def_path_str(def_id);

        // Skip functions without MIR
        if !self.tcx.is_mir_available(def_id) {
            return;
        }

        // Skip const contexts (only applicable to local functions)
        if let Some(local_def_id) = def_id.as_local() {
            if self.tcx.hir_body_const_context(local_def_id).is_some() {
                return;
            }
        }

        // Skip dummy functions
        if fn_name.contains("__raw_ptr_deref_dummy") {
            return;
        }

        // Get the optimized MIR
        let body = self.tcx.optimized_mir(def_id);

        // Create the intraprocedural analyzer
        let analyzer = FnAliasAnalyzer::new(self.tcx, def_id, body, fn_summaries.clone());

        // Run the dataflow analysis
        let mut results = analyzer
            .iterate_to_fixpoint(self.tcx, body, None)
            .into_results_cursor(body);

        // (Debug)
        let iter_cnt = *results.analysis().bb_iter_cnt.borrow();
        let bb_cnt = body.basic_blocks.iter().len();
        rap_debug!(
            "[Alias-mfp] {fn_name} {iter_cnt}/{bb_cnt}, analysis ratio: {:.2}",
            (iter_cnt as f32) / (bb_cnt as f32)
        );

        // Extract the function summary from this analysis
        let new_summary = interproc::extract_summary(&mut results, body, def_id);

        // Join with existing summary to maintain monotonicity
        // This ensures we never lose alias relationships discovered in previous iterations
        if let Some(old_summary) = self.fn_map.get_mut(&def_id) {
            for alias in new_summary.aliases() {
                old_summary.add_alias(alias.clone());
            }
        } else {
            self.fn_map.insert(def_id, new_summary);
        }
    }

    /// Recursively collect all reachable functions with available MIR
    fn collect_reachable_functions(&self, def_id: DefId, reachable: &mut FxHashSet<DefId>) {
        // Prevent infinite recursion
        if reachable.contains(&def_id) {
            return;
        }

        // Check if MIR is available
        if self.get_arg_count(def_id).is_none() {
            return;
        }

        // Mark as visited
        reachable.insert(def_id);

        // Traverse all basic blocks in the MIR body
        let body = self.tcx.optimized_mir(def_id);
        for bb_data in body.basic_blocks.iter() {
            if let Some(terminator) = &bb_data.terminator {
                if let TerminatorKind::Call { func, .. } = &terminator.kind {
                    if let Operand::Constant(c) = func {
                        if let ty::FnDef(callee_def_id, _) = c.ty().kind() {
                            // Recursively collect called functions
                            self.collect_reachable_functions(*callee_def_id, reachable);
                        }
                    }
                }
            }
        }
    }
}

impl<'tcx> RapxAnalysis for MfpAliasAnalyzer<'tcx> {
    fn name(&self) -> &'static str {
        "Alias Analysis (MFP)"
    }

    fn run(&mut self) {
        // Get all functions to analyze
        let mir_keys = self.tcx.mir_keys(());

        // Shared function summaries for interprocedural analysis
        let fn_summaries = Rc::new(RefCell::new(FxHashMap::default()));

        // Step 1: Collect all reachable functions with available MIR
        let mut reachable_functions = FxHashSet::default();

        // Start from mir_keys and recursively collect
        for local_def_id in mir_keys.iter() {
            self.collect_reachable_functions(local_def_id.to_def_id(), &mut reachable_functions);
        }

        // Step 2: Initialize function summaries to ⊥ (empty) for all reachable functions
        for def_id in reachable_functions.iter() {
            if let Some(arg_count) = self.get_arg_count(*def_id) {
                self.fn_map.insert(*def_id, FnAliasPairs::new(arg_count));
            }
        }

        // Convert to Vec for iteration
        let reachable_vec: Vec<DefId> = reachable_functions.iter().copied().collect();

        // Step 3: Fixpoint iteration
        const MAX_ITERATIONS: usize = 10;
        let mut iteration = 0;

        loop {
            iteration += 1;
            let mut changed = false;

            // Sync current summaries to fn_summaries (critical for interprocedural analysis)
            {
                let mut summaries = fn_summaries.borrow_mut();
                summaries.clear();
                for (def_id, summary) in &self.fn_map {
                    summaries.insert(*def_id, summary.clone());
                }
            }

            // Analyze each function with current summaries
            for def_id in reachable_vec.iter() {
                // Skip if not analyzable
                if !self.fn_map.contains_key(def_id) {
                    continue;
                }

                // Save old summary for comparison
                let old_summary = self.fn_map.get(def_id).cloned().unwrap();

                // Re-analyze the function
                self.analyze_function(*def_id, &fn_summaries);

                // Check if summary changed
                if let Some(new_summary) = self.fn_map.get(def_id) {
                    // Compare by checking if alias sets are equal
                    let old_aliases: std::collections::HashSet<_> =
                        old_summary.aliases().iter().cloned().collect();
                    let new_aliases: std::collections::HashSet<_> =
                        new_summary.aliases().iter().cloned().collect();

                    if old_aliases != new_aliases {
                        changed = true;
                        rap_trace!(
                            "Summary changed for {:?}: {} -> {}",
                            self.tcx.def_path_str(def_id),
                            old_summary.len(),
                            new_summary.len()
                        );
                    }
                }
            }

            // Check convergence
            if !changed {
                rap_trace!(
                    "Interprocedural analysis converged after {} iterations",
                    iteration
                );
                break;
            }

            if iteration >= MAX_ITERATIONS {
                rap_warn!("Reached maximum iterations ({}), stopping", MAX_ITERATIONS);
                break;
            }
        }

        // Step 3: Sort and display results
        for (fn_id, fn_alias) in &mut self.fn_map {
            let fn_name = self.tcx.def_path_str(fn_id);
            fn_alias.sort_alias_index();
            if fn_alias.len() > 0 {
                rap_trace!("Alias found in {:?}: {}", fn_name, fn_alias);
            }
        }
    }

    fn reset(&mut self) {
        self.fn_map.clear();
    }
}

impl<'tcx> AliasAnalysis for MfpAliasAnalyzer<'tcx> {
    fn get_fn_alias(&self, def_id: DefId) -> Option<FnAliasPairs> {
        self.fn_map.get(&def_id).cloned()
    }

    fn get_all_fn_alias(&self) -> FnAliasMap {
        self.fn_map.clone()
    }
}
