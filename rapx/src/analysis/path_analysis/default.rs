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

    /// Analyze a single function, returning all whole-CFG paths for it.
    /// Results are cached — subsequent calls for the same `def_id` return
    /// the cached tree.
    pub fn analyze(&mut self, def_id: DefId) -> Option<PathTree> {
        self.analyze_repeat(def_id, 0)
    }

    /// Analyze a single function allowing each SCC postfix segment to
    /// repeat up to `postfix_repeat` additional times.
    pub fn analyze_repeat(&mut self, def_id: DefId, postfix_repeat: usize) -> Option<PathTree> {
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

    /// Analyze all functions in the local crate.
    pub fn analyze_all(&mut self) {
        self.analyze_all_repeat(0);
    }

    /// Analyze all functions with the given postfix-repeat count.
    pub fn analyze_all_repeat(&mut self, postfix_repeat: usize) {
        for local_def_id in self.tcx.iter_local_def_id() {
            if matches!(self.tcx.def_kind(local_def_id), DefKind::Fn) {
                let def_id = local_def_id.to_def_id();
                let _ = self.analyze_repeat(def_id, postfix_repeat);
            }
        }
    }

    pub fn run_with_repeat(&mut self, postfix_repeat: usize) {
        self.analyze_all_repeat(postfix_repeat);
    }
}

impl<'tcx> Analysis for PathAnalyzer<'tcx> {
    fn run(&mut self) {
        self.analyze_all();
    }

}
