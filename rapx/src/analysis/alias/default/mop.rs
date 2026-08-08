use rustc_hir::def_id::DefId;

use std::collections::HashSet;

use crate::analysis::alias::observer::NoopAliasObserver;
use crate::analysis::path::{PathNode, PathTree};

use super::alias::ensure_fn_aliases_cached;
use super::{graph::*, *};

impl<'tcx> AliasGraph<'tcx> {
    pub fn process_function_paths(
        &mut self,
        fn_map: &mut MopFnAliasMap,
        recursion_set: &mut HashSet<DefId>,
    ) {
        self.process_function_paths_opt(None, fn_map, recursion_set)
    }

    pub fn process_function_paths_opt(
        &mut self,
        precomputed_paths: Option<PathTree>,
        fn_map: &mut MopFnAliasMap,
        recursion_set: &mut HashSet<DefId>,
    ) {
        self.init_pts_graph();

        let paths = precomputed_paths.unwrap_or_else(|| self.enumerate_paths());
        let Some(root) = paths.root() else {
            return;
        };

        let mut path = Vec::new();
        let _ = self.dfs_mop(root, &mut path, fn_map, recursion_set);
    }

    fn dfs_mop(
        &mut self,
        node: &PathNode,
        path: &mut Vec<usize>,
        fn_map: &mut MopFnAliasMap,
        rec_set: &mut HashSet<DefId>,
    ) -> Result<(), ()> {
        path.push(node.block);
        let mut obs = NoopAliasObserver;

        self.alias_bb(node.block, &mut obs);
        if let Some(target_id) = self.call_target_of(node.block) {
            ensure_fn_aliases_cached(self.tcx(), target_id, fn_map, rec_set);
        }
        self.alias_bbcall(node.block, fn_map, &mut obs);

        let saved_pts_graph = self.pts_graph.clone();
        let saved_rec = rec_set.clone();

        if node.is_path_end {
            self.increment_visit_times();
            if self.visit_times() > VISIT_LIMIT {
                path.pop();
                return Err(());
            }
            self.merge_results_pts();
        }

        for child in &node.children {
            self.pts_graph = saved_pts_graph.clone();
            *rec_set = saved_rec.clone();
            self.dfs_mop(child, path, fn_map, rec_set)?;
        }

        path.pop();
        Ok(())
    }
}
