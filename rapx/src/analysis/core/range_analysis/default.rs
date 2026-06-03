#![allow(unused_imports)]

use crate::{
    analysis::{
        Analysis,
        core::{
            // Graph used for path-sensitive CFG traversal
            alias_analysis::default::graph::MopGraph,
            callgraph::{default::CallGraph, visitor::CallGraphVisitor},
            range_analysis::{
                Range, RangeAnalysis,
                domain::{
                    ConstraintGraph::ConstraintGraph,
                    domain::{ConstConvert, IntervalArithmetic, VarNodes},
                },
            },

            // SSA / ESSA transformation passes
            ssa_transform::*,
        },
    },
    rap_debug, rap_info,
    graphs::scc::Scc,
};

use rustc_data_structures::fx::FxHashMap;
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::{
    mir::{Body, Place},
    ty::TyCtxt,
};
use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    fmt::Debug,
    fs::{self, File},
    io::Write,
    path::PathBuf,
    rc::Rc,
};

use super::{PathConstraint, PathConstraintMap, RAResult, RAResultMap, RAVecResultMap};

/// RangeAnalyzer performs MIR-based interprocedural range analysis.
/// It builds SSA/ESSA, constraint graphs, propagates intervals,
/// and optionally extracts path constraints.
pub struct RangeAnalyzer<'tcx, T: IntervalArithmetic + ConstConvert + Debug> {
    pub tcx: TyCtxt<'tcx>, // Compiler type context
    pub debug: bool,       // Enable debug output

    pub ssa_def_id: Option<DefId>,  // SSA marker function DefId
    pub essa_def_id: Option<DefId>, // ESSA marker function DefId

    pub final_vars: RAResultMap<'tcx, T>, // Final merged interval results

    // Mapping from original places to SSA-renamed places
    pub ssa_places_mapping: FxHashMap<DefId, HashMap<Place<'tcx>, HashSet<Place<'tcx>>>>,

    pub fn_constraintgraph_mapping: FxHashMap<DefId, ConstraintGraph<'tcx, T>>,
    pub callgraph: CallGraph<'tcx>,
    pub body_map: FxHashMap<DefId, Body<'tcx>>,
    pub cg_map: FxHashMap<DefId, Rc<RefCell<ConstraintGraph<'tcx, T>>>>,

    // Variable nodes collected per function (per call context)
    pub vars_map: FxHashMap<DefId, Vec<RefCell<VarNodes<'tcx, T>>>>,

    pub final_vars_vec: RAVecResultMap<'tcx, T>, // Interval results per call

    pub path_constraints: PathConstraintMap<'tcx>, // Path-sensitive constraints
}

impl<'tcx, T: IntervalArithmetic + ConstConvert + Debug> Analysis for RangeAnalyzer<'tcx, T>
where
    T: IntervalArithmetic + ConstConvert + Debug,
{
    fn name(&self) -> &'static str {
        "Range Analysis"
    }

    /// Entry point of the analysis
    fn run(&mut self) {
        // self.start();
        self.only_caller_range_analysis();
        self.start_path_constraints_analysis();
    }

    fn reset(&mut self) {
        self.final_vars.clear();
        self.ssa_places_mapping.clear();
    }
}

impl<'tcx, T: IntervalArithmetic + ConstConvert + Debug> RangeAnalysis<'tcx, T>
    for RangeAnalyzer<'tcx, T>
where
    T: IntervalArithmetic + ConstConvert + Debug,
{
    fn get_fn_range(&self, def_id: DefId) -> Option<RAResult<'tcx, T>> {
        self.final_vars.get(&def_id).cloned()
    }

    fn get_fn_ranges_percall(&self, def_id: DefId) -> Option<Vec<RAResult<'tcx, T>>> {
        self.final_vars_vec.get(&def_id).cloned()
    }

    fn get_all_fn_ranges(&self) -> RAResultMap<'tcx, T> {
        // Return a cloned map of all final ranges
        self.final_vars.clone()
    }

    fn get_all_fn_ranges_percall(&self) -> RAVecResultMap<'tcx, T> {
        self.final_vars_vec.clone()
    }

    /// Query the range of a specific local variable
    fn get_fn_local_range(&self, def_id: DefId, place: Place<'tcx>) -> Option<Range<T>> {
        self.final_vars
            .get(&def_id)
            .and_then(|vars| vars.get(&place).cloned())
    }

    fn get_fn_path_constraints(&self, def_id: DefId) -> Option<PathConstraint<'tcx>> {
        self.path_constraints.get(&def_id).cloned()
    }

    fn get_all_path_constraints(&self) -> PathConstraintMap<'tcx> {
        self.path_constraints.clone()
    }
}

impl<'tcx, T> RangeAnalyzer<'tcx, T>
where
    T: IntervalArithmetic + ConstConvert + Debug,
{
    pub fn new(tcx: TyCtxt<'tcx>, debug: bool) -> Self {
        let mut ssa_id = None;
        let mut essa_id = None;

        if let Some(ssa_def_id) = tcx.hir_crate_items(()).free_items().find(|id| {
            let hir_id = id.hir_id();
            if let Some(ident_name) = tcx.hir_opt_name(hir_id) {
                ident_name.to_string() == "SSAstmt"
            } else {
                false
            }
        }) {
            ssa_id = Some(ssa_def_id.owner_id.to_def_id());
            if let Some(essa_def_id) = tcx.hir_crate_items(()).free_items().find(|id| {
                let hir_id = id.hir_id();
                if let Some(ident_name) = tcx.hir_opt_name(hir_id) {
                    ident_name.to_string() == "ESSAstmt"
                } else {
                    false
                }
            }) {
                essa_id = Some(essa_def_id.owner_id.to_def_id());
            }
        }
        Self {
            tcx: tcx,
            debug,
            ssa_def_id: ssa_id,
            essa_def_id: essa_id,
            final_vars: FxHashMap::default(),
            ssa_places_mapping: FxHashMap::default(),
            fn_constraintgraph_mapping: FxHashMap::default(),
            callgraph: CallGraph::new(tcx),
            body_map: FxHashMap::default(),
            cg_map: FxHashMap::default(),
            vars_map: FxHashMap::default(),
            final_vars_vec: FxHashMap::default(),
            path_constraints: FxHashMap::default(),
        }
    }

    fn build_constraintgraph(&mut self, body_mut_ref: &'tcx Body<'tcx>, def_id: DefId) {
        rap_debug!(
            "Building ConstraintGraph for function: {}",
            self.tcx.def_path_str(def_id)
        );
        let ssa_def_id = self.ssa_def_id.expect("SSA definition ID is not set");
        let essa_def_id = self.essa_def_id.expect("ESSA definition ID is not set");
        let mut cg: ConstraintGraph<'tcx, T> =
            ConstraintGraph::new(body_mut_ref, self.tcx, def_id, essa_def_id, ssa_def_id);
        cg.build_graph(body_mut_ref);
        cg.build_nuutila(false);
        // cg.rap_print_vars();
        // cg.rap_print_final_vars();
        let dot_output = cg.to_dot();
        let vars_map = cg.get_vars().clone();

        self.cg_map.insert(def_id, Rc::new(RefCell::new(cg)));
        let mut vec = Vec::new();
        vec.push(RefCell::new(vars_map));
        self.vars_map.insert(def_id, vec);
        let function_name = self.tcx.def_path_str(def_id);

        let dir_path = PathBuf::from("cg_dot");
        fs::create_dir_all(dir_path.clone()).unwrap();
        let safe_filename = format!("{}_cg.dot", function_name);
        let output_path = dir_path.join(format!("{}", safe_filename));

        let mut file = File::create(&output_path).expect("cannot create file");
        file.write_all(dot_output.as_bytes())
            .expect("Could not write to file");

        rap_trace!("Successfully generated graph.dot");
    }

    fn only_caller_range_analysis(&mut self) {
        let ssa_def_id = self.ssa_def_id.expect("SSA definition ID is not set");
        let essa_def_id = self.essa_def_id.expect("ESSA definition ID is not set");
        // ====================================================================
        // PHASE 1: Build all ConstraintGraphs and the complete CallGraph first.
        // ====================================================================
        rap_debug!("PHASE 1: Building all ConstraintGraphs and the CallGraph...");
        for local_def_id in self.tcx.iter_local_def_id() {
            if matches!(self.tcx.def_kind(local_def_id), DefKind::Fn) {
                let def_id = local_def_id.to_def_id();

                if self.tcx.is_mir_available(def_id) {
                    rap_info!("Processing function: {}", self.tcx.def_path_str(def_id));
                    let mut body = self.tcx.optimized_mir(def_id).clone();
                    let body_mut_ref = unsafe { &mut *(&mut body as *mut Body<'tcx>) };
                    // Run SSA/ESSA passes
                    let mut passrunner = PassRunner::new(self.tcx);
                    passrunner.run_pass(body_mut_ref, ssa_def_id, essa_def_id);
                    self.body_map.insert(def_id, body);
                    // Print the MIR after SSA/ESSA passes
                    if self.debug {
                        print_diff(self.tcx, body_mut_ref, def_id.into());
                        print_mir_graph(self.tcx, body_mut_ref, def_id.into());
                    }

                    self.ssa_places_mapping
                        .insert(def_id, passrunner.places_map.clone());
                    // rap_debug!("ssa_places_mapping: {:?}", self.ssa_places_mapping);
                    // Build and store the constraint graph
                    self.build_constraintgraph(body_mut_ref, def_id);
                    // Visit for call graph construction
                    let mut call_graph_visitor =
                        CallGraphVisitor::new(self.tcx, def_id, body_mut_ref, &mut self.callgraph);
                    call_graph_visitor.visit();
                }
            }
        }
        rap_debug!("PHASE 1 Complete. ConstraintGraphs & CallGraphs built.");
        // self.callgraph.print_call_graph(); // Optional: for debugging

        // ====================================================================
        // PHASE 2: Analyze only the call chain start functions.
        // ====================================================================
        rap_debug!("PHASE 2: Finding and analyzing call chain start functions...");

        let mut call_chain_starts: Vec<DefId> = Vec::new();

        let callers_by_callee_id = self.callgraph.get_callers_map();

        for &def_id in &self.callgraph.functions {
            if !callers_by_callee_id.contains_key(&def_id) && self.cg_map.contains_key(&def_id) {
                call_chain_starts.push(def_id);
            }
        }

        call_chain_starts.sort_by_key(|d| self.tcx.def_path_str(*d));

        rap_debug!(
            "Found call chain starts ({} functions): {:?}",
            call_chain_starts.len(),
            call_chain_starts
                .iter()
                .map(|d| self.tcx.def_path_str(*d))
                .collect::<Vec<_>>()
        );

        for def_id in call_chain_starts {
            rap_debug!(
                "Analyzing function (call chain start): {}",
                self.tcx.def_path_str(def_id)
            );
            if let Some(cg_cell) = self.cg_map.get(&def_id) {
                let mut cg = cg_cell.borrow_mut();
                cg.find_intervals(&self.cg_map, &mut self.vars_map);
            } else {
                rap_debug!(
                    "Warning: No ConstraintGraph found for DefId {:?} during analysis of call chain starts.",
                    def_id
                );
            }
        }

        let analysis_order = self.callgraph.get_reverse_post_order();
        for def_id in analysis_order {
            if let Some(cg_cell) = self.cg_map.get(&def_id) {
                let mut cg = cg_cell.borrow_mut();
                let (final_vars_for_fn, _) = cg.build_final_vars(&self.ssa_places_mapping[&def_id]);
                let mut ranges_for_fn = HashMap::new();
                for (&place, varnode) in final_vars_for_fn {
                    ranges_for_fn.insert(place, varnode.get_range().clone());
                }
                let Some(varnodes_vec) = self.vars_map.get_mut(&def_id) else {
                    rap_debug!(
                        "Warning: No VarNodes found for DefId {:?} during analysis of call chain starts.",
                        def_id
                    );
                    continue;
                };
                for varnodes in varnodes_vec.iter_mut() {
                    let ranges_for_fn_recursive = ConstraintGraph::filter_final_vars(
                        &varnodes.borrow(),
                        &self.ssa_places_mapping[&def_id],
                    );
                    self.final_vars_vec
                        .entry(def_id)
                        .or_default()
                        .push(ranges_for_fn_recursive);
                }

                self.final_vars.insert(def_id, ranges_for_fn);
            }
        }

        rap_debug!("PHASE 2 Complete. Interval analysis finished for call chain start functions.");
    }
    pub fn start_path_constraints_analysis_for_defid(
        &mut self,
        def_id: DefId,
    ) -> Option<PathConstraint<'tcx>> {
        if self.tcx.is_mir_available(def_id) {
            let mut body = self.tcx.optimized_mir(def_id).clone();
            let body_mut_ref = unsafe { &mut *(&mut body as *mut Body<'tcx>) };

            let mut cg: ConstraintGraph<'tcx, T> =
                ConstraintGraph::new_without_ssa(body_mut_ref, self.tcx, def_id);
            let mut graph = MopGraph::new(self.tcx, def_id);
            graph.find_scc();
            let paths: Vec<Vec<usize>> = graph.get_all_branch_sub_blocks_paths();
            let result = cg.start_analyze_path_constraints(body_mut_ref, &paths);
            rap_debug!(
                "Paths for function {}: {:?}",
                self.tcx.def_path_str(def_id),
                paths
            );
            let switchbbs = cg.switchbbs.clone();
            rap_debug!(
                "Switch basicblocks for function {}: {:?}",
                self.tcx.def_path_str(def_id),
                switchbbs
            );
            rap_debug!(
                "Path Constraints Analysis Result for function {}: {:?}",
                self.tcx.def_path_str(def_id),
                result
            );
            self.path_constraints.insert(def_id, result.clone());
            Some(result)
        } else {
            None
        }
    }
    pub fn start_path_constraints_analysis(&mut self) {
        for local_def_id in self.tcx.iter_local_def_id() {
            if matches!(self.tcx.def_kind(local_def_id), DefKind::Fn) {
                let def_id = local_def_id.to_def_id();

                if self.tcx.is_mir_available(def_id) {
                    let mut body = self.tcx.optimized_mir(def_id).clone();
                    let body_mut_ref = unsafe { &mut *(&mut body as *mut Body<'tcx>) };

                    let mut cg: ConstraintGraph<'tcx, T> =
                        ConstraintGraph::new_without_ssa(body_mut_ref, self.tcx, def_id);
                    let mut graph = MopGraph::new(self.tcx, def_id);
                    graph.find_scc();
                    let paths: Vec<Vec<usize>> = graph.get_all_branch_sub_blocks_paths();
                    let result = cg.start_analyze_path_constraints(body_mut_ref, &paths);
                    rap_debug!(
                        "Paths for function {}: {:?}",
                        self.tcx.def_path_str(def_id),
                        paths
                    );
                    let switchbbs = cg.switchbbs.clone();
                    rap_debug!(
                        "Switch basicblocks for function {}: {:?}",
                        self.tcx.def_path_str(def_id),
                        switchbbs
                    );
                    rap_debug!(
                        "Path Constraints Analysis Result for function {}: {:?}",
                        self.tcx.def_path_str(def_id),
                        result
                    );
                    self.path_constraints.insert(def_id, result);
                }
            }
        }
    }
}
