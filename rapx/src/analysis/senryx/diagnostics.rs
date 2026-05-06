//! Diagnostic and result-recording helpers for Senryx contract checks.
//!
//! The verifier records passed and failed safety properties per unsafe callsite
//! so the top-level driver can summarize whether a target function discharged
//! its unsafe API obligations.

use std::collections::HashSet;

use crate::analysis::{
    senryx::visitor::{BodyVisitor, CheckResult},
    utils::fn_info::{display_hashmap, get_cleaned_def_path_name},
};
use rustc_span::Span;

impl<'tcx> BodyVisitor<'tcx> {
    /// Record one property-checking result for the current unsafe callsite.
    pub fn insert_checking_result(
        &mut self,
        sp: &str,
        is_passed: bool,
        func_name: String,
        fn_span: Span,
        idx: usize,
    ) {
        if sp == "Unknown" {
            return;
        }
        if is_passed {
            self.insert_successful_check_result(func_name.clone(), fn_span, idx + 1, sp);
        } else {
            self.insert_failed_check_result(func_name.clone(), fn_span, idx + 1, sp);
        }
    }

    /// Record one failed safety-property check for an unsafe callsite.
    pub fn insert_failed_check_result(
        &mut self,
        func_name: String,
        fn_span: Span,
        idx: usize,
        sp: &str,
    ) {
        if let Some(existing) = self
            .check_results
            .iter_mut()
            .find(|result| result.func_name == func_name && result.func_span == fn_span)
        {
            if let Some(passed_set) = existing.passed_contracts.get_mut(&idx) {
                passed_set.remove(sp);
                if passed_set.is_empty() {
                    existing.passed_contracts.remove(&idx);
                }
            }
            existing
                .failed_contracts
                .entry(idx)
                .and_modify(|set| {
                    set.insert(sp.to_string());
                })
                .or_insert_with(|| {
                    let mut new_set = HashSet::new();
                    new_set.insert(sp.to_string());
                    new_set
                });
        } else {
            let mut new_result = CheckResult::new(&func_name, fn_span);
            new_result
                .failed_contracts
                .insert(idx, HashSet::from([sp.to_string()]));
            self.check_results.push(new_result);
        }
    }

    /// Record one successful safety-property check for an unsafe callsite.
    pub fn insert_successful_check_result(
        &mut self,
        func_name: String,
        fn_span: Span,
        idx: usize,
        sp: &str,
    ) {
        if let Some(existing) = self
            .check_results
            .iter_mut()
            .find(|result| result.func_name == func_name && result.func_span == fn_span)
        {
            if let Some(failed_set) = existing.failed_contracts.get_mut(&idx) {
                if failed_set.contains(sp) {
                    return;
                }
            }

            existing
                .passed_contracts
                .entry(idx)
                .and_modify(|set| {
                    set.insert(sp.to_string());
                })
                .or_insert_with(|| HashSet::from([sp.to_string()]));
        } else {
            let mut new_result = CheckResult::new(&func_name, fn_span);
            new_result
                .passed_contracts
                .insert(idx, HashSet::from([sp.to_string()]));
            self.check_results.push(new_result);
        }
    }

    /// Print graph context when a checker cannot locate a requested node.
    pub fn show_error_info(&self, arg: usize) {
        rap_warn!(
            "In func {:?}, visitor checker error! Can't get {arg} in chain!",
            get_cleaned_def_path_name(self.tcx, self.def_id)
        );
        display_hashmap(&self.chains.variables, 1);
    }
}
