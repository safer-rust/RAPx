use crate::analysis::{
    Analysis,
    path_analysis::graph::{PathEnumerator, PathGraph},
};
use crate::compat::FxHashMap;
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::ty::TyCtxt;

use super::PathTree;

/// PathAnalyzer is responsible only for extracting path-sensitive CFG paths.
/// Downstream analyses can reuse these paths without depending on alias logic.
pub struct PathAnalyzer<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub debug: bool,
    pub paths: FxHashMap<DefId, PathTree>,
    pub graphs: FxHashMap<DefId, PathGraph<'tcx>>,
}

impl<'tcx> PathAnalyzer<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, debug: bool) -> Self {
        Self {
            tcx,
            debug,
            paths: FxHashMap::default(),
            graphs: FxHashMap::default(),
        }
    }

    pub fn start_path_analysis_for_defid(&mut self, def_id: DefId) -> Option<PathTree> {
        self.start_path_analysis_for_defid_with_repeat(def_id, 0)
    }

    pub fn start_path_analysis_for_defid_with_repeat(
        &mut self,
        def_id: DefId,
        postfix_repeat: usize,
    ) -> Option<PathTree> {
        if let Some(paths) = self.paths.get(&def_id) {
            return Some(paths.clone());
        }

        if !self.tcx.is_mir_available(def_id) {
            return None;
        }

        let mut graph = PathGraph::new(self.tcx, def_id);
        graph.find_scc();
        let mut enumerator = PathEnumerator::new(&graph);
        let paths = enumerator.enumerate_paths_repeat(postfix_repeat);
        let fn_name = self.tcx.def_path_str(def_id);

        rap_info!("Function: {}", fn_name);
        for (idx, path) in paths.iter().enumerate() {
            rap_info!("  path {}: {:?}", idx, path);
        }

        self.graphs.insert(def_id, graph);
        self.paths.insert(def_id, paths.clone());
        Some(paths)
    }

    pub fn get_fn_paths(&self, def_id: DefId) -> Option<PathTree> {
        self.paths.get(&def_id).cloned()
    }

    pub fn get_all_paths(&self) -> FxHashMap<DefId, PathTree> {
        self.paths.clone()
    }

    pub fn start_path_analysis(&mut self) {
        self.start_path_analysis_with_repeat(0);
    }

    pub fn start_path_analysis_with_repeat(&mut self, postfix_repeat: usize) {
        for local_def_id in self.tcx.iter_local_def_id() {
            if matches!(self.tcx.def_kind(local_def_id), DefKind::Fn) {
                let def_id = local_def_id.to_def_id();
                let _ = self.start_path_analysis_for_defid_with_repeat(def_id, postfix_repeat);
            }
        }
    }

    pub fn run_with_repeat(&mut self, postfix_repeat: usize) {
        self.start_path_analysis_with_repeat(postfix_repeat);
    }

    /// Verify whether a given path is reachable for the specified function.
    ///
    /// The path is a sequence of MIR block indices (can include loops).
    /// Uses discriminant/constant-based filtering to reject infeasible paths.
    pub fn check_path_reachability(&self, def_id: DefId, path: &[usize]) -> bool {
        if let Some(graph) = self.graphs.get(&def_id) {
            return graph.is_path_reachable(path);
        }
        let graph = PathGraph::new(self.tcx, def_id);
        graph.is_path_reachable(path)
    }
}

impl<'tcx> Analysis for PathAnalyzer<'tcx> {
    fn name(&self) -> &'static str {
        "Path Analysis"
    }

    fn run(&mut self) {
        self.start_path_analysis();
    }

    fn reset(&mut self) {
        self.paths.clear();
        self.graphs.clear();
    }
}
