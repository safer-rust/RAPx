//! Shared SCC-tree and SCC-path utilities.
//!
//! These helpers are graph-only building blocks: they do not encode
//! alias-analysis- or verification-specific state semantics.

use rustc_data_structures::fx::{FxHashMap, FxHashSet};

use super::scc::{Scc, SccInfo, SccTree};

/// Stable key for deduplicating path + path-constraint combinations.
#[derive(Clone, Hash, PartialEq, Eq)]
pub struct PathKey {
    pub path: Vec<usize>,
    pub constraints: Vec<(usize, usize)>,
}

/// Collect all SCC components from a successor graph.
///
/// Each node is represented by its `usize` index and each edge by an index in
/// the corresponding successor list.
pub fn collect_scc_components(successors: &[Vec<usize>]) -> Vec<Vec<usize>> {
    let mut collector = SccComponentCollector::new(successors.to_vec());
    collector.find_scc();
    collector.components
}

/// Build an SCC tree rooted at `scc` by repeatedly querying per-node SCC info.
///
/// `node_to_scc` should return the **most specific/direct SCC owner** for `node`
/// under the current nesting model.
///
/// In other words, for a node that belongs to nested SCCs, return the SCC metadata
/// of the innermost SCC that currently contains that node. This allows this helper
/// to reconstruct nested SCC trees by repeatedly mapping each node to its direct
/// child SCC owner and recursing.
pub fn build_scc_tree<F>(scc: &SccInfo, mut node_to_scc: F) -> SccTree
where
    F: FnMut(usize) -> Option<SccInfo>,
{
    build_scc_tree_inner(scc, &mut node_to_scc)
}

fn build_scc_tree_inner<F>(scc: &SccInfo, node_to_scc: &mut F) -> SccTree
where
    F: FnMut(usize) -> Option<SccInfo>,
{
    let mut child_sccs: FxHashMap<usize, SccInfo> = FxHashMap::default();

    for &node in scc.nodes.iter() {
        let Some(node_scc) = node_to_scc(node) else {
            continue;
        };

        if node_scc.enter != scc.enter && !node_scc.nodes.is_empty() {
            child_sccs.entry(node_scc.enter).or_insert(node_scc);
        }
    }

    let children = child_sccs
        .into_values()
        .map(|child_scc| build_scc_tree_inner(&child_scc, node_to_scc))
        .collect();

    SccTree {
        scc: scc.clone(),
        children,
    }
}

/// Convert unordered path constraints into a stable, hashable key.
pub fn constraints_key(constraints: &FxHashMap<usize, usize>) -> Vec<(usize, usize)> {
    let mut sorted_constraints: Vec<(usize, usize)> =
        constraints.iter().map(|(k, val)| (*k, *val)).collect();
    sorted_constraints.sort_unstable();
    sorted_constraints
}

/// Build a dedup key from a path and its associated constraints.
pub fn make_path_key(path: &[usize], constraints: &FxHashMap<usize, usize>) -> PathKey {
    PathKey {
        path: path.to_vec(),
        constraints: constraints_key(constraints),
    }
}

/// Insert `(path, constraints)` into `out` only if this combination is new.
pub fn record_unique_path(
    path: &[usize],
    constraints: &FxHashMap<usize, usize>,
    out: &mut Vec<(Vec<usize>, FxHashMap<usize, usize>)>,
    seen_paths: &mut FxHashSet<PathKey>,
) {
    let key = make_path_key(path, constraints);
    if seen_paths.insert(key) {
        out.push((path.to_vec(), constraints.clone()));
    }
}

/// Return true when `node` belongs to the SCC currently being enumerated.
pub fn node_is_in_current_scc(start: usize, scc: &SccInfo, node: usize) -> bool {
    node == start || scc.nodes.contains(&node)
}

/// Rebuild the per-segment recursion stack from the suffix after the latest
/// dominator (`start`) occurrence in `path`.
pub fn rebuild_segment_stack(path: &[usize], start: usize) -> FxHashSet<usize> {
    // `path` is expected to begin with `start` in our SCC DFS. If a caller provides
    // an unexpected path without `start`, we conservatively fall back to the full path.
    let last_start_pos = path.iter().rposition(|&node| node == start).unwrap_or(0);
    let mut segment_stack = FxHashSet::default();
    for node in &path[last_start_pos..] {
        segment_stack.insert(*node);
    }
    segment_stack
}

/// Traversal state for SCC path enumeration in an SCC tree.
///
/// This struct is graph-layer state only: it tracks path/segment/cycle bookkeeping
/// and intentionally does not include analysis-specific branch semantics.
#[derive(Clone, Debug)]
pub struct SccPathTraversalState {
    pub start: usize,
    pub cur: usize,
    pub path: Vec<usize>,
    pub segment_stack: FxHashSet<usize>,
    pub visited_since_enter: FxHashSet<usize>,
    pub baseline_at_dominator: FxHashSet<usize>,
    pub skip_child_enter: Option<usize>,
}

impl SccPathTraversalState {
    /// Create a traversal state rooted at an SCC dominator/entry `start`.
    pub fn new(start: usize) -> Self {
        let mut segment_stack = FxHashSet::default();
        segment_stack.insert(start);

        let mut visited_since_enter = FxHashSet::default();
        visited_since_enter.insert(start);

        Self {
            start,
            cur: start,
            path: vec![start],
            segment_stack,
            baseline_at_dominator: visited_since_enter.clone(),
            visited_since_enter,
            skip_child_enter: None,
        }
    }

    /// Return true if the current node belongs to the SCC being enumerated.
    pub fn is_cur_in_scc(&self, scc: &SccInfo) -> bool {
        node_is_in_current_scc(self.start, scc, self.cur)
    }

    /// Return true if `node` belongs to the SCC being enumerated.
    pub fn is_node_in_scc(&self, scc: &SccInfo, node: usize) -> bool {
        node_is_in_current_scc(self.start, scc, node)
    }

    /// Return true if traversal should stop because path explosion guards are hit.
    pub fn exceeds_complexity_limits(
        &self,
        max_path_len: usize,
        max_seen_paths: usize,
        seen_paths_len: usize,
    ) -> bool {
        self.path.len() > max_path_len || seen_paths_len > max_seen_paths
    }

    /// Apply dominator-boundary cycle policy for the current node.
    ///
    /// Returns `false` when the cycle ending at dominator introduces no new nodes
    /// and should be pruned.
    pub fn prepare_for_current_node(&mut self) -> bool {
        if self.cur != self.start {
            return true;
        }

        if self.path.len() > 1 {
            // Find previous occurrence of `start` before the trailing `start`.
            let prev_start_pos = self.path[..self.path.len() - 1]
                .iter()
                .rposition(|&node| node == self.start)
                .unwrap_or(0);
            // Nodes in the cycle segment exclude both dominator endpoints.
            let cycle_nodes = &self.path[prev_start_pos + 1..self.path.len() - 1];
            let introduces_new = cycle_nodes
                .iter()
                .any(|node| !self.baseline_at_dominator.contains(node));
            if !introduces_new {
                return false;
            }
        }

        // At dominator boundary, reset baseline and segment recursion stack.
        self.baseline_at_dominator = self.visited_since_enter.clone();
        self.segment_stack.clear();
        self.segment_stack.insert(self.start);
        true
    }

    /// Return true if `next` can be entered under current segment recursion policy.
    pub fn can_descend_to(&self, next: usize) -> bool {
        !self.segment_stack.contains(&next) || next == self.start
    }

    /// Return a new traversal state after descending one edge to `next`.
    pub fn descend_to(&self, next: usize) -> Self {
        let mut next_state = self.clone();
        next_state.cur = next;
        next_state.path.push(next);
        next_state.segment_stack.insert(next);
        next_state.visited_since_enter.insert(next);
        next_state.skip_child_enter = None;
        next_state
    }

    /// Return a copy with a child-enter skip marker for parent-level continuation.
    pub fn with_skip_child_enter(&self, child_enter: usize) -> Self {
        let mut next_state = self.clone();
        next_state.skip_child_enter = Some(child_enter);
        next_state
    }

    /// Build a new state after splicing a nested SCC path into the current path.
    pub fn with_spliced_path(
        &self,
        spliced_path: Vec<usize>,
        skip_child_enter: Option<usize>,
    ) -> Self {
        let mut visited_since_enter = self.visited_since_enter.clone();
        for node in &spliced_path {
            visited_since_enter.insert(*node);
        }

        let cur = *spliced_path.last().unwrap_or(&self.cur);
        let segment_stack = rebuild_segment_stack(&spliced_path, self.start);

        Self {
            start: self.start,
            cur,
            path: spliced_path,
            segment_stack,
            visited_since_enter,
            baseline_at_dominator: self.baseline_at_dominator.clone(),
            skip_child_enter,
        }
    }
}

struct SccComponentCollector {
    successors: Vec<Vec<usize>>,
    components: Vec<Vec<usize>>,
}

impl SccComponentCollector {
    fn new(successors: Vec<Vec<usize>>) -> Self {
        Self {
            successors,
            components: Vec::new(),
        }
    }
}

impl Scc for SccComponentCollector {
    fn on_scc_found(&mut self, _root: usize, scc_components: &[usize]) {
        self.components.push(scc_components.to_vec());
    }

    fn get_next(&mut self, root: usize) -> FxHashSet<usize> {
        self.successors
            .get(root)
            .into_iter()
            .flat_map(|successors| successors.iter().copied())
            .collect()
    }

    fn get_size(&mut self) -> usize {
        self.successors.len()
    }
}
