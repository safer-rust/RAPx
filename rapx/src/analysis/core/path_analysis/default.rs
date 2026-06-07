use crate::analysis::{Analysis, core::path_analysis::graph::PathGraph};
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
        let paths = graph.get_path_sensitive_paths();

        if self.debug {
            rap_debug!(
                "Extracted paths for function {}: {:?}",
                self.tcx.def_path_str(def_id),
                paths
            );
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
