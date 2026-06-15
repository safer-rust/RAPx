use crate::analysis::{Analysis, path_analysis::graph::PathGraph};
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::ty::TyCtxt;

use super::{PathMap, PathSet};

/// PathAnalyzer is responsible only for extracting path-sensitive CFG paths.
/// Downstream analyses can reuse these paths without depending on alias logic.
pub struct PathAnalyzer<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub debug: bool,
    pub paths: PathMap,
}

impl<'tcx> PathAnalyzer<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, debug: bool) -> Self {
        Self {
            tcx,
            debug,
            paths: FxHashMap::default(),
        }
    }

    fn compute_paths_for_defid(&self, def_id: DefId) -> Option<PathSet> {
        if !self.tcx.is_mir_available(def_id) {
            return None;
        }

        let mut graph = PathGraph::new(self.tcx, def_id);
        graph.find_scc();
        let paths = graph.enumerate_paths();
        let fn_name = self.tcx.def_path_str(def_id);

        rap_info!("Function: {}", fn_name);
        for (idx, path) in paths.iter().enumerate() {
            let reachable = graph.is_path_reachable(path);
            rap_info!("  path {}: {:?} | reachable: {}", idx, path, reachable);
        }

        Some(paths)
    }

    pub fn start_path_analysis_for_defid(&mut self, def_id: DefId) -> Option<PathSet> {
        if let Some(paths) = self.paths.get(&def_id) {
            return Some(paths.clone());
        }

        let paths = self.compute_paths_for_defid(def_id)?;
        self.paths.insert(def_id, paths.clone());
        Some(paths)
    }

    pub fn get_fn_paths(&self, def_id: DefId) -> Option<PathSet> {
        self.paths.get(&def_id).cloned()
    }

    pub fn get_all_paths(&self) -> PathMap {
        self.paths.clone()
    }

    pub fn start_path_analysis(&mut self) {
        for local_def_id in self.tcx.iter_local_def_id() {
            if matches!(self.tcx.def_kind(local_def_id), DefKind::Fn) {
                let def_id = local_def_id.to_def_id();
                let _ = self.start_path_analysis_for_defid(def_id);
            }
        }
    }

    /// Verify whether a given path is reachable for the specified function.
    ///
    /// The path is a sequence of MIR block indices (can include loops).
    /// Uses discriminant/constant-based filtering to reject infeasible paths.
    pub fn check_path_reachability(&self, def_id: DefId, path: &[usize]) -> bool {
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
    }
}
