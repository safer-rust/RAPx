use super::chain::*;
use super::{
    SafetyFlowAnalysis, safetyflow_graph::SafetyFlowGraph, safetyflow_unit::BasicUnitCounts,
};
use crate::helpers::{draw_dot::render_dot_graphs, fn_info::*, show_mir::display_mir};
use rustc_hir::{Safety, def::DefKind, def_id::DefId};
use rustc_middle::ty::Visibility;
use rustc_span::Symbol;
use std::collections::HashSet;

impl<'tcx> SafetyFlowAnalysis<'tcx> {
    pub fn audit_std_unsafe(&mut self) {
        let all_std_fn_def = get_all_std_fns_by_rustc_public(self.tcx);
        // Specific task for vec;
        let symbol = Symbol::intern("Vec");
        let vec_def_id = self.tcx.get_diagnostic_item(symbol).unwrap();
        for &def_id in &all_std_fn_def {
            let adt_def = get_adt_def_id_by_adt_method(self.tcx, def_id);
            if adt_def.is_some() && adt_def.unwrap() == vec_def_id {
                self.insert_upg(def_id);
            }
        }
        if self.draw {
            self.render_dot();
        }
    }

    pub fn render_dot(&mut self) {
        let mut dot_strs = Vec::new();
        for upg in &self.units {
            let dot_str = SafetyFlowGraph::generate_dot_from_unit(self.tcx, upg);
            let caller_name = get_cleaned_def_path_name(self.tcx, upg.caller.def_id);
            dot_strs.push((caller_name, dot_str));
        }
        render_dot_graphs(dot_strs);
    }

    pub fn get_chains(&mut self) {
        let v_fn_def = self.tcx.mir_keys(());

        for local_def_id in v_fn_def {
            let def_id = local_def_id.to_def_id();
            if !check_visibility(self.tcx, def_id) {
                continue;
            }
            if get_cleaned_def_path_name(self.tcx, def_id) == "std::boxed::Box::<T>::from_raw" {
                let body = self.tcx.mir_built(local_def_id).steal();
                display_mir(def_id, &body);
            }
            let chains = get_all_std_unsafe_chains(self.tcx, def_id);
            let valid_chains: Vec<Vec<String>> = chains
                .into_iter()
                .filter(|chain| {
                    if chain.len() > 1 {
                        return true;
                    }
                    if chain.len() == 1 {
                        if check_safety(self.tcx, def_id) == Safety::Unsafe {
                            return true;
                        }
                    }
                    false
                })
                .collect();

            print_unsafe_chains(&valid_chains);
        }
    }

    pub fn get_units_data(&mut self) {
        let mut counts = BasicUnitCounts::default();
        let def_id_sets = self.tcx.mir_keys(());
        for local_def_id in def_id_sets {
            let def_id = local_def_id.to_def_id();
            if self.tcx.def_kind(def_id) == DefKind::Fn || self.tcx.def_kind(def_id) == DefKind::AssocFn {
                self.insert_upg(def_id);
            }
        }
        for upg in &self.units {
            upg.count_basic_units(&mut counts);
        }
    }

    pub fn process_def_id(
        &mut self,
        def_id: DefId,
        visited: &mut HashSet<DefId>,
        unsafe_fn: &mut HashSet<DefId>,
    ) {
        if !visited.insert(def_id) {
            return;
        }
        match self.tcx.def_kind(def_id) {
            DefKind::Fn | DefKind::AssocFn => {
                if check_safety(self.tcx, def_id) == Safety::Unsafe
                    && self.tcx.visibility(def_id) == Visibility::Public
                {
                    unsafe_fn.insert(def_id);
                    self.insert_upg(def_id);
                }
            }
            DefKind::Mod => {
                for child in self.tcx.module_children(def_id) {
                    if let Some(child_def_id) = child.res.opt_def_id() {
                        self.process_def_id(child_def_id, visited, unsafe_fn);
                    }
                }
            }
            DefKind::Impl { of_trait: _ } => {
                for item in self.tcx.associated_item_def_ids(def_id) {
                    self.process_def_id(*item, visited, unsafe_fn);
                }
            }
            DefKind::Struct => {
                let impls = self.tcx.inherent_impls(def_id);
                for impl_def_id in impls {
                    self.process_def_id(*impl_def_id, visited, unsafe_fn);
                }
            }
            DefKind::Ctor(_of, _kind) => {
                if self.tcx.is_mir_available(def_id) {
                    let _mir = self.tcx.optimized_mir(def_id);
                }
            }
            _ => {
                // println!("{:?}",tcx.def_kind(def_id));
            }
        }
    }
}
