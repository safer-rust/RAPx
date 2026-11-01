//! Path extraction for verification targets.
//!
//! This module builds finite paths from a function CFG to each unsafe checkpoint.
//!
//! # Path reachability
//!
//! Each function's path is checked against its own SCC-aware `PathGraph`.
//! The symbolic VM checks reachability after caller and callee paths are composed.
//!
//! # Path limit
//!
//! Path enumeration and composition are bounded by [`crate::limit::path_limit`].
//! The tree is marked truncated when the budget is exhausted.

mod call_index;

pub(crate) use call_index::EntryBodies;

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{BasicBlock, TerminatorKind},
    ty::TyCtxt,
};

use self::call_index::CallSiteIndex;
use super::target::CalleeBodies;
use crate::analysis::path::{
    PathTree,
    graph::{PathEnumerator, PathGraph},
};
use crate::compat::{FxHashMap, FxHashSet};
use std::collections::VecDeque;
use std::rc::Rc;

use crate::verify::checkpoint::CheckpointLocation;

/// Enumerates finite, acyclic verification paths from function entry to each
/// unsafe checkpoint in one function body.
///
/// `run` enumerates each function independently, then composes selected callee
/// paths at callsites. Checkpoints and struct invariants slice prefixes from
/// the resulting [`PathTree`] via `walk_prefixes`/`subtree_to`.
///
/// Enumeration is capped at [`crate::limit::path_limit`] to avoid exponential
/// blow-up.
pub(crate) struct PathExtractor<'tcx> {
    /// Compiler type context used for MIR access and name resolution.
    tcx: TyCtxt<'tcx>,
    /// The function whose MIR body is being analyzed.
    def_id: DefId,
    /// Number of extra SCC postfix repetitions allowed (default 0).
    allow_repeat: usize,
    /// Instantiated caller MIR, shared with the slicer and VM when available.
    body: Option<&'tcx rustc_middle::mir::Body<'tcx>>,
    callee_bodies: CalleeBodies<'tcx>,
    coverage_targets: FxHashSet<usize>,
}
impl<'tcx> PathExtractor<'tcx> {
    /// Create a path extractor that verifies `def_id`, optionally against a
    /// monomorphized body.
    ///
    /// Path extraction (SCC detection, enumeration, filtering) is deferred
    /// until [`run`] is called.
    ///
    /// `allow_repeat` controls how many times a repeated SCC postfix segment
    /// is allowed beyond the first occurrence. Default is 0 (no extra repeats).
    pub(crate) fn new_with_body(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        allow_repeat: usize,
        body: Option<&'tcx rustc_middle::mir::Body<'tcx>>,
    ) -> Self {
        Self {
            tcx,
            def_id,
            allow_repeat,
            body,
            callee_bodies: CalleeBodies::default(),
            coverage_targets: FxHashSet::default(),
        }
    }

    pub(crate) fn with_callee_bodies(mut self, bodies: CalleeBodies<'tcx>) -> Self {
        self.callee_bodies = bodies;
        self
    }

    pub(crate) fn with_checkpoints(mut self, checkpoints: &[CheckpointLocation]) -> Self {
        self.coverage_targets
            .extend(checkpoints.iter().filter_map(|location| {
                (location.caller == self.def_id).then_some(location.block.as_usize())
            }));
        self
    }

    /// Run path extraction, consuming the extractor.
    ///
    /// Returns a composed [`PathTree`] with block-function metadata attached.
    pub(crate) fn run(self) -> PathTree {
        self.run_with_bodies().0
    }

    pub(crate) fn run_with_bodies(
        self,
    ) -> (PathTree, CalleeBodies<'tcx>, EntryBodies<'tcx>) {
        let mut caller_graph = match self.body {
            Some(body) => PathGraph::new_with_body(self.tcx, self.def_id, body),
            None => PathGraph::new(self.tcx, self.def_id),
        };
        caller_graph.find_scc();
        let caller_paths = PathEnumerator::new(&caller_graph)
            .with_coverage_targets(self.coverage_targets)
            .enumerate_paths_repeat(self.allow_repeat);
        let mut call_index = CallSiteIndex::new(
            self.tcx,
            self.def_id,
            self.body.cloned(),
            self.callee_bodies,
        );
        call_index.collect();
        let bodies = call_index.unambiguous_bodies();
        let entry_bodies = call_index.entry_bodies();
        let mut tree = PathComposer::new(&call_index, self.allow_repeat).compose(&caller_paths);
        tree.mark_structural();
        call_index.attach_metadata(&mut tree);
        (tree, bodies, entry_bodies)
    }
}

struct PathComposer<'g, 'tcx> {
    call_index: &'g CallSiteIndex<'tcx>,
    allow_repeat: usize,
    limit: usize,
    cache: FxHashMap<usize, Rc<Vec<Vec<usize>>>>,
    truncated: bool,
}

impl<'g, 'tcx> PathComposer<'g, 'tcx> {
    fn new(call_index: &'g CallSiteIndex<'tcx>, allow_repeat: usize) -> Self {
        Self {
            call_index,
            allow_repeat,
            limit: crate::limit::path_limit(),
            cache: FxHashMap::default(),
            truncated: false,
        }
    }

    fn compose(mut self, caller_paths: &PathTree) -> PathTree {
        if self.call_index.entries.is_empty() {
            return caller_paths.clone();
        }
        let mut root_paths = caller_paths.to_vecs();
        root_paths.sort_by_key(Vec::len);
        let mut ordered = Vec::with_capacity(root_paths.len());
        let mut root_paths = VecDeque::from(root_paths);
        while let Some(shortest) = root_paths.pop_front() {
            ordered.push(shortest);
            if let Some(longest) = root_paths.pop_back() {
                ordered.push(longest);
            }
        }
        let mut pending: VecDeque<VecDeque<Vec<usize>>> = ordered
            .into_iter()
            .map(|path| VecDeque::from(self.expand(&path)))
            .collect();
        let mut result = PathTree::new();
        while result.len() < self.limit {
            let mut progress = false;
            for paths in &mut pending {
                if let Some(path) = paths.pop_front() {
                    result.insert(&path);
                    progress = true;
                }
                if result.len() >= self.limit {
                    break;
                }
            }
            if !progress {
                break;
            }
        }
        if self.truncated
            || caller_paths.is_truncated()
            || pending.iter().any(|paths| !paths.is_empty())
        {
            result.mark_truncated();
        }
        result
    }

    fn expand(&mut self, path: &[usize]) -> Vec<Vec<usize>> {
        let mut paths = vec![Vec::new()];
        for (position, &block) in path.iter().enumerate() {
            for prefix in &mut paths {
                prefix.push(block);
            }
            let Some(entries) = self.call_index.entries.get(&block).cloned() else {
                continue;
            };
            if path.get(position + 1).copied() != self.call_index.normal_successor(block) {
                continue;
            }
            let choices = entries
                .into_iter()
                .map(|entry| self.callee_paths(entry))
                .collect::<Vec<_>>();
            let mut next_paths = Vec::new();
            for prefix in &paths {
                for group in &choices {
                    for choice in group.iter() {
                        if next_paths.len() >= self.limit {
                            self.truncated = true;
                            break;
                        }
                        let mut full = prefix.clone();
                        full.extend(choice);
                        next_paths.push(full);
                    }
                }
            }
            paths = next_paths;
            if paths.is_empty() {
                break;
            }
        }
        paths
    }

    fn callee_paths(&mut self, entry: usize) -> Rc<Vec<Vec<usize>>> {
        if let Some(paths) = self.cache.get(&entry) {
            return Rc::clone(paths);
        }
        let callee = self.call_index.blocks()[entry].0;
        let body = self.call_index.body(entry);
        let mut local_graph = if self.call_index.has_body_override(entry) {
            PathGraph::new_with_body(self.call_index.tcx(), callee, body)
        } else {
            PathGraph::new(self.call_index.tcx(), callee)
        };
        local_graph.find_scc();
        let local_paths =
            PathEnumerator::new(&local_graph).enumerate_paths_repeat(self.allow_repeat);
        self.truncated |= local_paths.is_truncated();
        let mut result = Vec::new();
        for path in local_paths.to_vecs() {
            let Some(&last) = path.last() else { continue };
            if !matches!(
                body.basic_blocks[BasicBlock::from(last)].terminator().kind,
                TerminatorKind::Return | TerminatorKind::TailCall { .. }
            ) {
                continue;
            }
            result.extend(self.expand(&path.iter().map(|block| entry + block).collect::<Vec<_>>()));
            if result.len() > self.limit {
                result.truncate(self.limit);
                self.truncated = true;
                break;
            }
        }
        let result = Rc::new(result);
        self.cache.insert(entry, Rc::clone(&result));
        result
    }
}

/// One finite, acyclic execution trace from function entry to a checkpoint,
/// represented as an ordered sequence of MIR basic blocks.
///
/// Built by the [`BackwardSlicer`](super::slicer::BackwardSlicer) from the
/// [`PathTree`] produced by [`PathExtractor`].
///
/// The VM checks whether each composed path is reachable.
#[derive(Clone, Debug)]
pub(crate) struct Path {
    /// The [`CheckpointLocation`] (function + basic block) reached by this path.
    pub target: CheckpointLocation,
    /// Ordered global block numbers from function entry to `target`.
    pub blocks: Vec<usize>,
}

impl Path {
    /// Render only the caller's local blocks, excluding inlined callee blocks.
    pub(crate) fn describe_caller_indices(&self, tree: &PathTree) -> String {
        format!(
            "{:?}",
            caller_blocks(tree, self.target.caller, self.blocks.iter().copied())
        )
    }
}

/// Map composed-tree block numbers back to local blocks of `caller`.
pub(crate) fn caller_blocks(
    tree: &PathTree,
    caller: DefId,
    blocks: impl IntoIterator<Item = usize>,
) -> Vec<usize> {
    blocks
        .into_iter()
        .filter_map(|global| {
            let (def_id, local) = tree.block_fn_of(global).unwrap_or((caller, global));
            (def_id == caller).then_some(local)
        })
        .collect()
}
