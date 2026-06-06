//! Shared SCC-tree and path-sensitive SCC traversal utilities.
//!
//! This module provides reusable SCC path enumeration with path-state
//! propagation, pruning, deduplication, and nested-SCC path splicing.
//! Concrete analyses define branch feasibility and state updates via hooks.
//!
//! It also provides whole-CFG path enumeration via [`compute_path_sensitive_paths`]
//! and the [`WholeCfgPathEnumerator`] trait, which is the unified entry point for
//! downstream consumers such as range analysis and Senryx.

use rustc_data_structures::fx::{FxHashMap, FxHashSet};

use super::scc::{Scc, SccInfo};

/// Maximum number of whole-CFG paths collected before stopping enumeration.
const WHOLE_CFG_PATH_LIMIT: usize = 4000;
/// Maximum DFS depth for whole-CFG path enumeration.
const WHOLE_CFG_PATH_DEPTH_LIMIT: usize = 256;

/// Stable key for deduplicating path + path-constraint combinations.
#[derive(Clone, Hash, PartialEq, Eq)]
struct PathKey {
    path: Vec<usize>,
    constraints: Vec<(usize, usize)>,
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

/// Convert unordered path constraints into a stable, hashable key.
pub fn constraints_key(constraints: &FxHashMap<usize, usize>) -> Vec<(usize, usize)> {
    let mut sorted_constraints: Vec<(usize, usize)> =
        constraints.iter().map(|(k, val)| (*k, *val)).collect();
    sorted_constraints.sort_unstable();
    sorted_constraints
}

/// Build a dedup key from a path and its associated constraints.
fn make_path_key(path: &[usize], constraints: &FxHashMap<usize, usize>) -> PathKey {
    PathKey {
        path: path.to_vec(),
        constraints: constraints_key(constraints),
    }
}

/// Insert `(path, constraints)` into `out` only if this combination is new.
fn record_unique_path(
    path: &[usize],
    constraints: &FxHashMap<usize, usize>,
    out: &mut Vec<SccEnumeratedPath>,
    seen_paths: &mut FxHashSet<PathKey>,
) {
    let key = make_path_key(path, constraints);
    if seen_paths.insert(key) {
        out.push(SccEnumeratedPath {
            blocks: path.to_vec(),
            constraints: constraints.clone(),
        });
    }
}

/// Return true when `node` belongs to the SCC currently being enumerated.
fn node_is_in_current_scc(start: usize, scc: &SccInfo, node: usize) -> bool {
    node == start || scc.nodes.contains(&node)
}

/// Rebuild the per-segment recursion stack from the suffix after the latest
/// dominator (`start`) occurrence in `path`.
fn rebuild_segment_stack(path: &[usize], start: usize) -> FxHashSet<usize> {
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
/// This struct tracks path/segment/cycle bookkeeping for SCC traversal.
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

pub type SccPathConstraints = FxHashMap<usize, usize>;

/// A single enumerated path through an SCC together with its accumulated path constraints.
///
/// `blocks` is the ordered sequence of CFG block indices visited along the path.
/// `constraints` holds the path-sensitive branch facts collected during traversal.
#[derive(Clone, Debug)]
pub struct SccEnumeratedPath {
    pub blocks: Vec<usize>,
    pub constraints: SccPathConstraints,
}

#[derive(Clone, Debug)]
pub struct SccPathTraversalConfig {
    pub max_path_len: usize,
    pub max_seen_paths: usize,
    pub max_depth: usize,
}

impl Default for SccPathTraversalConfig {
    fn default() -> Self {
        Self {
            max_path_len: 200,
            max_seen_paths: 4000,
            max_depth: 128,
        }
    }
}

#[derive(Clone, Debug)]
pub enum SccPathAction {
    Traverse {
        next: usize,
        constraints: SccPathConstraints,
    },
    RecordExit {
        constraints: SccPathConstraints,
    },
}

pub trait SccPathSemantics {
    fn on_node_enter(&mut self, _node: usize, _constraints: &mut SccPathConstraints) {}

    fn child_scc_enters<'a>(&self, scc: &'a SccInfo) -> &'a [usize] {
        &scc.child_sccs
    }

    fn enumerate_child_paths(
        &mut self,
        child_enter: usize,
        constraints: &SccPathConstraints,
    ) -> Vec<SccEnumeratedPath>;

    fn enumerate_actions(
        &mut self,
        scc: &SccInfo,
        state: &SccPathTraversalState,
        constraints: &SccPathConstraints,
    ) -> Vec<SccPathAction>;
}

fn record_scc_exit_path(
    scc: &SccInfo,
    node: usize,
    constraints: &SccPathConstraints,
    cur_path: &[usize],
    out: &mut Vec<SccEnumeratedPath>,
    seen_paths: &mut FxHashSet<PathKey>,
) {
    if !scc.exits.iter().any(|e| e.exit == node) {
        return;
    }
    record_unique_path(cur_path, constraints, out, seen_paths);
}

fn enumerate_scc_paths_inner<S: SccPathSemantics>(
    scc: &SccInfo,
    state: SccPathTraversalState,
    mut path_constraints: SccPathConstraints,
    paths_in_scc: &mut Vec<SccEnumeratedPath>,
    seen_paths: &mut FxHashSet<PathKey>,
    semantics: &mut S,
    config: &SccPathTraversalConfig,
    depth: usize,
) {
    if depth > config.max_depth {
        return;
    }

    if scc.nodes.is_empty() {
        record_unique_path(&state.path, &path_constraints, paths_in_scc, seen_paths);
        return;
    }

    if state.exceeds_complexity_limits(config.max_path_len, config.max_seen_paths, seen_paths.len())
    {
        return;
    }

    if !state.is_cur_in_scc(scc) {
        return;
    }

    let mut state = state;
    if !state.prepare_for_current_node() {
        return;
    }

    semantics.on_node_enter(state.cur, &mut path_constraints);

    for &child_enter in semantics.child_scc_enters(scc) {
        if state.cur != child_enter {
            continue;
        }

        if state.skip_child_enter == Some(child_enter) {
            break;
        }

        let sub_paths = semantics.enumerate_child_paths(child_enter, &path_constraints);

        enumerate_scc_paths_inner(
            scc,
            state.with_skip_child_enter(child_enter),
            path_constraints.clone(),
            paths_in_scc,
            seen_paths,
            semantics,
            config,
            depth + 1,
        );

        for sub_path in sub_paths {
            if sub_path.blocks.len() <= 1 {
                continue;
            }

            let mut new_path = state.path.clone();
            new_path.extend(&sub_path.blocks[1..]);
            let new_cur = *new_path
                .last()
                .expect("spliced child path must be non-empty");
            let next_skip_child_enter = if new_cur == child_enter {
                Some(child_enter)
            } else {
                None
            };

            enumerate_scc_paths_inner(
                scc,
                state.with_spliced_path(new_path, next_skip_child_enter),
                sub_path.constraints,
                paths_in_scc,
                seen_paths,
                semantics,
                config,
                depth + 1,
            );
        }
        return;
    }

    for action in semantics.enumerate_actions(scc, &state, &path_constraints) {
        match action {
            SccPathAction::RecordExit { constraints } => {
                record_scc_exit_path(
                    scc,
                    state.cur,
                    &constraints,
                    &state.path,
                    paths_in_scc,
                    seen_paths,
                );
            }
            SccPathAction::Traverse { next, constraints } => {
                if !state.is_node_in_scc(scc, next) {
                    record_scc_exit_path(
                        scc,
                        state.cur,
                        &constraints,
                        &state.path,
                        paths_in_scc,
                        seen_paths,
                    );
                    continue;
                }
                if !state.can_descend_to(next) {
                    continue;
                }
                enumerate_scc_paths_inner(
                    scc,
                    state.descend_to(next),
                    constraints,
                    paths_in_scc,
                    seen_paths,
                    semantics,
                    config,
                    depth + 1,
                );
            }
        }
    }
}

pub fn enumerate_scc_paths<S: SccPathSemantics>(
    start: usize,
    scc: &SccInfo,
    initial_constraints: SccPathConstraints,
    semantics: &mut S,
    config: SccPathTraversalConfig,
) -> Vec<SccEnumeratedPath> {
    let mut all_paths = Vec::new();
    let mut seen_paths: FxHashSet<PathKey> = FxHashSet::default();
    enumerate_scc_paths_inner(
        scc,
        SccPathTraversalState::new(start),
        initial_constraints,
        &mut all_paths,
        &mut seen_paths,
        semantics,
        &config,
        0,
    );
    all_paths
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

// ===========================================================================================
// Whole-CFG path-sensitive enumeration
// ===========================================================================================

/// Trait abstracting the CFG + SCC operations needed by whole-CFG path enumeration.
///
/// Implement this trait for your graph type to use [`compute_path_sensitive_paths`].
pub trait WholeCfgPathEnumerator {
    /// Total number of CFG blocks.
    fn block_count(&self) -> usize;

    /// Outgoing successor indices for block `index`.
    fn block_nexts(&self, index: usize) -> Vec<usize>;

    /// SCC-enter block index for block `index`.
    fn block_scc_enter(&self, index: usize) -> usize;

    /// Returns `true` when block `index` is the root of a non-trivial SCC
    /// (i.e., the SCC contains at least one other member node).
    fn block_has_scc_members(&self, index: usize) -> bool;

    /// Sort the SCC tree rooted at `enter` and enumerate all SCC-internal paths.
    ///
    /// The returned paths start at `enter` and end at an SCC exit node.
    fn enumerate_scc_paths_at(&mut self, enter: usize) -> Vec<SccEnumeratedPath>;
}

/// Compute all path-sensitive paths for a whole CFG.
///
/// This is the **unified entry point** for downstream consumers such as
/// range analysis and Senryx.  All SCC-internal loops are expanded via
/// [`WholeCfgPathEnumerator::enumerate_scc_paths_at`] so that the
/// returned paths contain the full block sequence for each feasible
/// execution.
pub fn compute_path_sensitive_paths<G: WholeCfgPathEnumerator>(graph: &mut G) -> Vec<Vec<usize>> {
    let mut all_paths = Vec::new();
    let mut seen_paths = FxHashSet::default();

    if graph.block_count() == 0 {
        return all_paths;
    }

    let mut current_path = vec![0];
    let mut active_blocks = FxHashSet::default();
    active_blocks.insert(0);

    collect_path_sensitive_paths_inner(
        graph,
        0,
        &mut current_path,
        &mut active_blocks,
        &mut all_paths,
        &mut seen_paths,
        0,
    );

    all_paths.sort_unstable();
    all_paths
}

fn collect_path_sensitive_paths_inner<G: WholeCfgPathEnumerator>(
    graph: &mut G,
    current: usize,
    current_path: &mut Vec<usize>,
    active_blocks: &mut FxHashSet<usize>,
    all_paths: &mut Vec<Vec<usize>>,
    seen_paths: &mut FxHashSet<Vec<usize>>,
    depth: usize,
) {
    if depth > WHOLE_CFG_PATH_DEPTH_LIMIT
        || all_paths.len() >= WHOLE_CFG_PATH_LIMIT
        || current >= graph.block_count()
    {
        return;
    }

    let cur_scc_enter = graph.block_scc_enter(current);
    if current == cur_scc_enter && graph.block_has_scc_members(current) {
        let paths_in_scc = graph.enumerate_scc_paths_at(current);

        if paths_in_scc.is_empty() {
            if seen_paths.insert(current_path.clone()) {
                all_paths.push(current_path.clone());
            }
            return;
        }

        for scc_segment in paths_in_scc {
            if all_paths.len() >= WHOLE_CFG_PATH_LIMIT {
                break;
            }

            let mut scc_path = current_path.clone();
            if scc_segment.blocks.len() > 1 {
                scc_path.extend_from_slice(&scc_segment.blocks[1..]);
            }

            let Some(&last) = scc_path.last() else {
                continue;
            };

            let mut nexts: Vec<usize> = graph
                .block_nexts(last)
                .into_iter()
                .filter(|&next| graph.block_scc_enter(next) != cur_scc_enter)
                .collect();
            nexts.sort_unstable();
            nexts.dedup();

            if nexts.is_empty() {
                if seen_paths.insert(scc_path.clone()) {
                    all_paths.push(scc_path);
                }
                continue;
            }

            for next in nexts {
                if active_blocks.contains(&next) {
                    if seen_paths.insert(scc_path.clone()) {
                        all_paths.push(scc_path.clone());
                    }
                    continue;
                }

                let mut continued_path = scc_path.clone();
                continued_path.push(next);
                active_blocks.insert(next);
                collect_path_sensitive_paths_inner(
                    graph,
                    next,
                    &mut continued_path,
                    active_blocks,
                    all_paths,
                    seen_paths,
                    depth + 1,
                );
                active_blocks.remove(&next);
            }
        }
        return;
    }

    let mut nexts = graph.block_nexts(current);
    nexts.sort_unstable();
    nexts.dedup();

    if nexts.is_empty() {
        if seen_paths.insert(current_path.clone()) {
            all_paths.push(current_path.clone());
        }
        return;
    }

    let mut followed = false;
    for next in nexts {
        if all_paths.len() >= WHOLE_CFG_PATH_LIMIT {
            break;
        }

        if active_blocks.contains(&next) {
            if seen_paths.insert(current_path.clone()) {
                all_paths.push(current_path.clone());
            }
            continue;
        }

        followed = true;
        current_path.push(next);
        active_blocks.insert(next);
        collect_path_sensitive_paths_inner(
            graph,
            next,
            current_path,
            active_blocks,
            all_paths,
            seen_paths,
            depth + 1,
        );
        active_blocks.remove(&next);
        current_path.pop();
    }

    if !followed && seen_paths.insert(current_path.clone()) {
        all_paths.push(current_path.clone());
    }
}
