/*
 * This module generates the unsafety propagation graph for each Rust module in the target crate.
 */
pub mod chain;
pub mod fn_collector;
pub mod hir_visitor;
pub mod root;
pub mod safetyflow_graph;
pub mod safetyflow_unit;
pub mod std_analysis;

use crate::{
    helpers::{draw_dot::render_dot_graphs, fn_info::*},
    utils::source::{get_fn_name_byid, get_module_name},
};
use fn_collector::FnCollector;
use root::hir_contains_unsafe;
use rustc_hir::{Safety, def_id::DefId};
use rustc_middle::ty::TyCtxt;
use safetyflow_graph::{SafetyFlowEdge, SafetyFlowGraph};
use safetyflow_unit::SafetyFlowUnit;
use std::collections::{HashMap, HashSet};

#[derive(PartialEq)]
pub enum TargetCrate {
    Std,
    Other,
}

pub struct SafetyFlowAnalysis<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub units: Vec<SafetyFlowUnit>,
    pub draw: bool,
}

impl<'tcx> SafetyFlowAnalysis<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            units: Vec::new(),
            draw: false,
        }
    }

    pub fn with_draw(mut self, draw: bool) -> Self {
        self.draw = draw;
        self
    }

    pub fn start(&mut self, ins: TargetCrate) {
        // SafetyFlowAnalysis does not implement Analysis directly because
        // std analysis has a different pipeline. This method is called from lib.rs.
        match ins {
            TargetCrate::Std => {
                self.audit_std_unsafe();
                return;
            }
            _ => {
                let fns = FnCollector::collect(self.tcx);
                for vec in fns.values() {
                    for (body_id, _span) in vec {
                        let def_id = self.tcx.hir_body_owner_def_id(*body_id).to_def_id();
                        if hir_contains_unsafe(self.tcx, *body_id) {
                            self.insert_upg(def_id);
                        }
                    }
                }
                self.display_summary();
                if self.draw {
                    let final_dots = self.collect_dots();
                    rap_info!("{:?}", final_dots);
                    render_dot_graphs(final_dots);
                }
            }
        }
    }

    pub fn insert_upg(&mut self, def_id: DefId) {
        let Some(root) = root::scan_mir(self.tcx, def_id) else {
            return;
        };

        // If the function is entirely safe (no unsafe code, no unsafe callees,
        // no raw pointer dereferences, and no static mutable accesses), skip.
        if check_safety(self.tcx, def_id) == Safety::Safe
            && root.unsafe_callees.is_empty()
            && root.raw_ptr_locals.is_empty()
            && root.static_muts.is_empty()
        {
            return;
        }

        let constructors = get_cons(self.tcx, def_id);
        let caller_typed = append_fn_with_types(self.tcx, def_id);
        let mut callees_typed = HashSet::new();
        for callee in &root.unsafe_callees {
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

        let mut_methods_set = get_all_mutable_methods(self.tcx, def_id);
        let mut_methods: HashSet<_> = mut_methods_set.keys().copied().collect();
        let unit = SafetyFlowUnit::new(
            caller_typed,
            callees_typed,
            root.raw_ptr_locals,
            root.static_muts,
            cons_typed,
            mut_methods,
        );
        self.units.push(unit);
    }

    /// Print a human-readable text summary of all safety flow units,
    /// grouped by module, similar to callgraph's output format.
    pub fn display_summary(&self) {
        if self.units.is_empty() {
            rap_info!("SafetyFlow: no unsafe operations detected.");
            return;
        }

        // Group units by module
        let mut modules: HashMap<String, Vec<&SafetyFlowUnit>> = HashMap::new();
        for unit in &self.units {
            let mod_name = get_module_name(self.tcx, unit.caller.def_id);
            modules.entry(mod_name).or_default().push(unit);
        }
        let mut mod_names: Vec<String> = modules.keys().cloned().collect();
        mod_names.sort();

        let mut total_callers = 0usize;
        let mut total_callees = 0usize;
        let mut total_rawptrs = 0usize;
        let mut total_staticmuts = 0usize;

        for mod_name in &mod_names {
            let units = &modules[mod_name];
            rap_info!("");
            rap_info!("SafetyFlow: {} ({} function(s))", mod_name, units.len());

            for unit in units {
                let caller_name = self.tcx.def_path_str(unit.caller.def_id);
                let safety = if unit.caller.fn_safety == Safety::Unsafe { "[Unsafe]" } else { "[Safe]" };
                rap_info!("  {} {}", caller_name, safety);
                total_callers += 1;

                for callee in &unit.callees {
                    let name = self.tcx.def_path_str(callee.def_id);
                    rap_info!("    -> {}", name);
                    total_callees += 1;
                }

                if !unit.raw_ptrs.is_empty() {
                    let locals: Vec<String> = unit.raw_ptrs.iter().map(|l| format!("{:?}", l)).collect();
                    rap_info!("    *raw* ptr deref: {}", locals.join(", "));
                    total_rawptrs += 1;
                }

                for def_id in &unit.static_muts {
                    let name = self.tcx.def_path_str(*def_id);
                    rap_info!("    !static! mut: {}", name);
                    total_staticmuts += 1;
                }

                for cons in &unit.caller_cons {
                    let name = self.tcx.def_path_str(cons.def_id);
                    rap_info!("    + constructor: {}", name);
                }

                for m in &unit.mut_methods {
                    let name = self.tcx.def_path_str(*m);
                    rap_info!("    ~ mut_self: {}", name);
                }
            }
        }

        rap_info!("");
        rap_info!("============================================================");
        rap_info!(
            "SafetyFlow summary: {} function(s), {} call edge(s), {} raw ptr deref(s), {} static mut access(es)",
            total_callers, total_callees, total_rawptrs, total_staticmuts
        );
        rap_info!("============================================================");
    }

    /// Aggregate units into per-module DOT graphs and return them.
    pub fn collect_dots(&self) -> Vec<(String, String)> {
        let mut modules_data: HashMap<String, SafetyFlowGraph> = HashMap::new();

        let mut collect_unit = |unit: &SafetyFlowUnit| {
            let caller_id = unit.caller.def_id;
            let module_name = get_module_name(self.tcx, caller_id);
            rap_info!("module name: {:?}", module_name);

            let module_data = modules_data
                .entry(module_name)
                .or_insert_with(SafetyFlowGraph::new);

            module_data.add_node(self.tcx, unit.caller, None);

            if let Some(adt) = get_adt_via_method(self.tcx, caller_id) {
                if adt.literal_cons_enabled {
                    let adt_node_type = FnInfo::new(adt.def_id, Safety::Safe, FnKind::Constructor);
                    let label = format!("Literal Constructor: {}", self.tcx.item_name(adt.def_id));
                    module_data.add_node(self.tcx, adt_node_type, Some(label));
                    if unit.caller.fn_kind == FnKind::Method {
                        module_data.add_edge(adt.def_id, caller_id, SafetyFlowEdge::ConsToMethod);
                    }
                } else {
                    let adt_node_type = FnInfo::new(adt.def_id, Safety::Safe, FnKind::Method);
                    let label = format!(
                        "MutMethod Introduced by PubFields: {}",
                        self.tcx.item_name(adt.def_id)
                    );
                    module_data.add_node(self.tcx, adt_node_type, Some(label));
                    if unit.caller.fn_kind == FnKind::Method {
                        module_data.add_edge(adt.def_id, caller_id, SafetyFlowEdge::MutToCaller);
                    }
                }
            }

            // Edge from associated item (constructor) to the method.
            for cons in &unit.caller_cons {
                module_data.add_node(self.tcx, *cons, None);
                module_data.add_edge(
                    cons.def_id,
                    unit.caller.def_id,
                    SafetyFlowEdge::ConsToMethod,
                );
            }

            // Edge from mutable access to the caller.
            for mut_method_id in &unit.mut_methods {
                let node_type = get_type(self.tcx, *mut_method_id);
                let fn_safety = check_safety(self.tcx, *mut_method_id);
                let node = FnInfo::new(*mut_method_id, fn_safety, node_type);

                module_data.add_node(self.tcx, node, None);
                module_data.add_edge(
                    *mut_method_id,
                    unit.caller.def_id,
                    SafetyFlowEdge::MutToCaller,
                );
            }

            // Edge representing a call from caller to callee.
            for callee in &unit.callees {
                module_data.add_node(self.tcx, *callee, None);
                module_data.add_edge(
                    unit.caller.def_id,
                    callee.def_id,
                    SafetyFlowEdge::CallerToCallee,
                );
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
                            SafetyFlowEdge::CallerToCallee,
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
                module_data.add_edge(unit.caller.def_id, *def_id, SafetyFlowEdge::CallerToCallee);
            }
        };

        // Aggregate all Units
        for upg in &self.units {
            collect_unit(upg);
        }

        // Generate string of dot
        let mut final_dots = Vec::new();
        for (mod_name, data) in modules_data {
            let dot = data.to_dot(&mod_name);
            final_dots.push((mod_name, dot));
        }
        final_dots
    }
}
