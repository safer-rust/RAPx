/*
 * This module generates the unsafety propagation graph for each Rust module in the target crate.
 */
pub mod fn_collector;
pub mod hir_visitor;
pub mod std_upg;
pub mod upg_graph;
pub mod upg_unit;

use crate::{
    analysis::utils::{
        draw_dot::{DotGraph, render_dot_graphs, render_dot_graphs_html},
        fn_info::*,
    },
    utils::{
        log::{span_to_filename, span_to_line_number},
        source::{get_fn_name_byid, get_module_name, get_span},
    },
};
use fn_collector::FnCollector;
use hir_visitor::ContainsUnsafe;
use rustc_hir::{Safety, def_id::DefId};
use rustc_middle::{mir::Local, ty::TyCtxt};
use std::collections::{HashMap, HashSet};
use upg_graph::{UPGEdge, UPGraph};
use upg_unit::UPGUnit;

#[derive(PartialEq)]
pub enum TargetCrate {
    Std,
    Other,
}

pub struct UPGAnalysis<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub upgs: Vec<UPGUnit>,
}

impl<'tcx> UPGAnalysis<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            upgs: Vec::new(),
        }
    }

    pub fn start(&mut self, ins: TargetCrate) {
        match ins {
            TargetCrate::Std => {
                self.audit_std_unsafe();
                return;
            }
            _ => {
                /* Type of collected data: FxHashMap<Option<HirId>, Vec<(BodyId, Span)>>;
                 * For a function, the Vec contains only one entry;
                 * For implementations of structs and traits, the Vec contains all associated
                 * function entries.
                 */
                let fns = FnCollector::collect(self.tcx);
                for vec in fns.values() {
                    for (body_id, _span) in vec {
                        // each function or associated function in
                        // structs and traits
                        let (fn_unsafe, block_unsafe) =
                            ContainsUnsafe::contains_unsafe(self.tcx, *body_id);
                        // map the function body_id back to its def_id;
                        let def_id = self.tcx.hir_body_owner_def_id(*body_id).to_def_id();
                        if fn_unsafe | block_unsafe {
                            self.insert_upg(def_id);
                        }
                    }
                }
                self.generate_graph_dots();
            }
        }
    }

    pub fn insert_upg(&mut self, def_id: DefId) {
        let callees = get_unsafe_callees(self.tcx, def_id);
        let raw_ptrs = get_rawptr_deref(self.tcx, def_id);
        let global_locals = collect_global_local_pairs(self.tcx, def_id);
        let static_muts: HashSet<DefId> = global_locals.keys().copied().collect();

        /*Static mutable access is in nature via raw ptr; We have to prune the duplication.*/
        let global_locals_set: HashSet<Local> = global_locals.values().flatten().copied().collect();
        let raw_ptrs_filtered: HashSet<Local> =
            raw_ptrs.difference(&global_locals_set).copied().collect();

        let constructors = get_cons(self.tcx, def_id);
        let caller_typed = append_fn_with_types(self.tcx, def_id);
        let mut callees_typed = HashSet::new();
        for callee in &callees {
            callees_typed.insert(append_fn_with_types(self.tcx, *callee));
        }
        let mut cons_typed = HashSet::new();
        for con in &constructors {
            cons_typed.insert(append_fn_with_types(self.tcx, *con));
        }

        // Skip processing if the caller is the dummy raw pointer dereference function
        let caller_name = get_fn_name_byid(&def_id);
        if let Some(_) = caller_name.find("__raw_ptr_deref_dummy") {
            return;
        }

        // If the function is entirely safe (no unsafe code, no unsafe callees, no raw pointer dereferences, and no static mutable accesses), skip further analysis
        if check_safety(self.tcx, def_id) == Safety::Safe
            && callees.is_empty()
            && raw_ptrs.is_empty()
            && static_muts.is_empty()
        {
            return;
        }
        let mut_methods_set = get_all_mutable_methods(self.tcx, def_id);
        let mut_methods = mut_methods_set.keys().copied().collect();
        let upg = UPGUnit::new(
            caller_typed,
            callees_typed,
            raw_ptrs_filtered,
            static_muts,
            cons_typed,
            mut_methods,
        );
        self.upgs.push(upg);
    }

    /// Main function to aggregate data and render DOT graphs per module.
    pub fn generate_graph_dots(&self) {
        let mut modules_data: HashMap<String, UPGraph> = HashMap::new();

        let mut collect_unit = |unit: &UPGUnit| {
            let caller_id = unit.caller.def_id;
            let module_name = get_module_name(self.tcx, caller_id);
            rap_info!("module name: {:?}", module_name);

            let module_data = modules_data.entry(module_name).or_insert_with(UPGraph::new);

            module_data.add_node(self.tcx, unit.caller, None);

            if let Some(adt) = get_adt_via_method(self.tcx, caller_id) {
                if adt.literal_cons_enabled {
                    let adt_node_type = FnInfo::new(adt.def_id, Safety::Safe, FnKind::Constructor);
                    let label = format!("Literal Constructor: {}", self.tcx.item_name(adt.def_id));
                    module_data.add_node(self.tcx, adt_node_type, Some(label));
                    if unit.caller.fn_kind == FnKind::Method {
                        module_data.add_edge(adt.def_id, caller_id, UPGEdge::ConsToMethod);
                    }
                } else {
                    let adt_node_type = FnInfo::new(adt.def_id, Safety::Safe, FnKind::Method);
                    let label = format!(
                        "MutMethod Introduced by PubFields: {}",
                        self.tcx.item_name(adt.def_id)
                    );
                    module_data.add_node(self.tcx, adt_node_type, Some(label));
                    if unit.caller.fn_kind == FnKind::Method {
                        module_data.add_edge(adt.def_id, caller_id, UPGEdge::MutToCaller);
                    }
                }
            }

            // Edge from associated item (constructor) to the method.
            for cons in &unit.caller_cons {
                module_data.add_node(self.tcx, *cons, None);
                module_data.add_edge(cons.def_id, unit.caller.def_id, UPGEdge::ConsToMethod);
            }

            // Edge from mutable access to the caller.
            for mut_method_id in &unit.mut_methods {
                let node_type = get_type(self.tcx, *mut_method_id);
                let fn_safety = check_safety(self.tcx, *mut_method_id);
                let node = FnInfo::new(*mut_method_id, fn_safety, node_type);

                module_data.add_node(self.tcx, node, None);
                module_data.add_edge(*mut_method_id, unit.caller.def_id, UPGEdge::MutToCaller);
            }

            // Edge representing a call from caller to callee.
            for callee in &unit.callees {
                module_data.add_node(self.tcx, *callee, None);
                module_data.add_edge(unit.caller.def_id, callee.def_id, UPGEdge::CallerToCallee);
            }

            rap_debug!("raw ptrs: {:?}", unit.raw_ptrs);
            if !unit.raw_ptrs.is_empty() {
                let all_raw_ptrs = unit
                    .raw_ptrs
                    .iter()
                    .map(|p| format!("{:?}", p))
                    .collect::<Vec<_>>()
                    .join(", ");

                match get_ptr_deref_dummy_def_id(self.tcx) {
                    Some(dummy_fn_def_id) => {
                        let rawptr_deref_fn =
                            FnInfo::new(dummy_fn_def_id, Safety::Unsafe, FnKind::Intrinsic);
                        module_data.add_node(
                            self.tcx,
                            rawptr_deref_fn,
                            Some(format!("Raw ptr deref: {}", all_raw_ptrs)),
                        );
                        module_data.add_edge(
                            unit.caller.def_id,
                            dummy_fn_def_id,
                            UPGEdge::CallerToCallee,
                        );
                    }
                    None => {
                        rap_info!("fail to find the dummy ptr deref id.");
                    }
                }
            }

            rap_debug!("static muts: {:?}", unit.static_muts);
            for def_id in &unit.static_muts {
                let node = FnInfo::new(*def_id, Safety::Unsafe, FnKind::Intrinsic);
                module_data.add_node(self.tcx, node, None);
                module_data.add_edge(unit.caller.def_id, *def_id, UPGEdge::CallerToCallee);
            }
        };

        // Aggregate all Units
        for upg in &self.upgs {
            collect_unit(upg);
        }

        // Generate string of dot
        let mut final_dots = Vec::new();
        for (mod_name, data) in modules_data {
            let dot = data.upg_unit_string(&mod_name);
            let url_map = data
                .nodes_def_ids()
                .iter()
                .filter_map(|def_id| {
                    get_span(self.tcx, *def_id).map(|span| {
                        let label = format!("{:?}", *def_id);
                        let mut filename = span_to_filename(span);
                        filename = filename
                            .strip_prefix("src/")
                            .unwrap_or(&filename)
                            .to_string();
                        let line_number = span_to_line_number(span);
                        let url = format!("{}.html#{}", filename, line_number);
                        (label, url)
                    })
                })
                .collect();
            final_dots.push(DotGraph::new_with_url_map(mod_name, dot, url_map));
        }
        rap_info!("{:?}", final_dots); // Output required for tests; do not change.
        render_dot_graphs(&final_dots);
        render_dot_graphs_html(&final_dots);
    }
}
