use rustc_hir::def_id::DefId;

use std::collections::HashSet;

use crate::analysis::path_analysis::PathNode;
use crate::compat::{FxHashMap, FxHashSet};

use super::value::Value;
use super::{graph::*, *};

#[derive(Clone)]
struct MopStateSnapshot {
    values: Vec<Value>,
    constants: FxHashMap<usize, usize>,
    alias_sets: Vec<FxHashSet<usize>>,
}

impl<'tcx> AliasGraph<'tcx> {
    fn snapshot_state(&self) -> MopStateSnapshot {
        MopStateSnapshot {
            values: self.values.clone(),
            constants: self.constants.clone(),
            alias_sets: self.alias_sets.clone(),
        }
    }

    fn restore_state(&mut self, snapshot: &MopStateSnapshot) {
        self.values = snapshot.values.clone();
        self.constants = snapshot.constants.clone();
        self.alias_sets = snapshot.alias_sets.clone();
    }

    /// Process pre-enumerated whole-function paths via DFS on the path tree.
    ///
    /// Shared prefixes are processed once. State is saved at branch points
    /// and restored before processing sibling subtrees, avoiding redundant
    /// re-analysis of common path prefixes.
    pub fn process_function_paths(
        &mut self,
        fn_map: &mut MopFnAliasMap,
        recursion_set: &mut HashSet<DefId>,
    ) {
        rap_debug!(
            "process_function_paths: def_id={:?} blocks={}",
            self.def_id(),
            self.path_graph.cfg.blocks.len()
        );
        let paths = self.enumerate_paths();
        rap_debug!(
            "process_function_paths: def_id={:?} paths_enumerated={}",
            self.def_id(),
            paths.len()
        );

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
        recursion_set: &mut HashSet<DefId>,
    ) -> Result<(), ()> {
        path.push(node.block);
        self.alias_bb(node.block);
        self.alias_bbcall(node.block, fn_map, recursion_set);

        let saved_state = self.snapshot_state();
        let saved_recursion = recursion_set.clone();

        if node.is_path_end {
            self.increment_visit_times();
            if self.visit_times() > VISIT_LIMIT {
                path.pop();
                return Err(());
            }
            self.merge_results();
        }

        for child in &node.children {
            self.restore_state(&saved_state);
            *recursion_set = saved_recursion.clone();
            self.dfs_mop(child, path, fn_map, recursion_set)?;
        }

        path.pop();
        Ok(())
    }
}
