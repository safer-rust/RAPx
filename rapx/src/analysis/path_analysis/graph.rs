use super::PathTree;
use crate::compat::{FxHashMap, FxHashSet};
use crate::graphs::{
    cfg::{CfgBlock, ControlFlowGraph},
    scc::{Scc, SccInfo},
};
use rustc_middle::{
    mir::{
        BasicBlock, Local, Operand, Rvalue, StatementKind, SwitchTargets, Terminator,
        TerminatorKind, UnwindAction,
    },
    ty::{TyCtxt, TyKind, TypingEnv},
};
use rustc_span::def_id::DefId;

/// Maximum number of whole-CFG paths collected before stopping enumeration.
const WHOLE_CFG_PATH_LIMIT: usize = 4000;
/// Maximum DFS depth for whole-CFG path enumeration.
const WHOLE_CFG_PATH_DEPTH_LIMIT: usize = 256;
/// Bounded cache size for SCC path enumeration.
const SCC_PATH_CACHE_LIMIT: usize = 2048;
/// Maximum DFS depth for intra-SCC path enumeration.
const SCC_MAX_DEPTH: usize = 128;
/// Maximum number of distinct paths collected per SCC.
const SCC_MAX_SEEN_PATHS: usize = 128;
/// Maximum path length within an SCC traversal.
const SCC_MAX_PATH_LEN: usize = 200;

/// Check whether the current entry→entry sub-path introduces a new block
/// *sequence* (not just new blocks).  Different branch choices inside the SCC
/// produce different sequences even when all block IDs have already been seen,
/// e.g. `if i % 2 == 0 { A } else { B }` alternates between two paths through
/// the same set of blocks on successive loop iterations.
fn check_postfix_segment(
    path: &[usize],
    enter: usize,
    segment_counts: &mut FxHashMap<Vec<usize>, usize>,
    max_repeats: usize,
) -> bool {
    let segment = extract_segment(path, enter);
    let count = segment_counts.entry(segment).or_insert(0);
    *count += 1;
    *count == 1 || *count - 1 <= max_repeats
}

fn extract_segment(path: &[usize], enter: usize) -> Vec<usize> {
    let prev_pos = path[..path.len() - 1]
        .iter()
        .rposition(|&node| node == enter)
        .unwrap_or(0);
    path[prev_pos + 1..path.len() - 1].to_vec()
}

#[derive(Clone, Debug)]
/// A single enumerated path through an SCC region.
///
/// `blocks` is the ordered sequence of MIR block indices from the SCC entry
/// to an exit point. `exit_successors` lists CFG successors of the last block
/// that are outside this SCC.
pub struct SccEnumeratedPath {
    pub blocks: Vec<usize>,
    pub exit_successors: Vec<usize>,
}

#[derive(Clone)]
pub struct PathGraph<'tcx> {
    pub cfg: ControlFlowGraph<'tcx>,
    /// Path-analysis-specific metadata: locals assigned in each block.
    pub assigned_locals: Vec<FxHashSet<usize>>,
    /// Path-analysis-specific metadata: discriminant local -> source local mapping.
    pub discriminants: FxHashMap<usize, usize>,
}

impl<'tcx> PathGraph<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, def_id: DefId) -> PathGraph<'tcx> {
        let body = tcx.optimized_mir(def_id);
        let basicblocks = &body.basic_blocks;
        let mut cfg_blocks = Vec::<CfgBlock>::new();
        let mut assigned_locals = Vec::new();
        let mut discriminants = FxHashMap::default();

        for i in 0..basicblocks.len() {
            let bb = &basicblocks[BasicBlock::from(i)];
            let mut cfg_block = CfgBlock::new(i, bb.is_cleanup);
            let mut block_assigned_locals = FxHashSet::default();

            for stmt in &bb.statements {
                if let StatementKind::Assign(assign) = &stmt.kind {
                    let (place, rvalue) = &**assign;
                    block_assigned_locals.insert(place.local.as_usize());
                    if let Rvalue::Discriminant(rv_place) = rvalue {
                        discriminants.insert(place.local.as_usize(), rv_place.local.as_usize());
                    }
                }
            }

            let Some(terminator) = &bb.terminator else {
                continue;
            };

            match terminator.kind.clone() {
                TerminatorKind::Goto { ref target } => {
                    cfg_block.add_next(target.as_usize());
                }
                TerminatorKind::SwitchInt {
                    discr: _,
                    ref targets,
                } => {
                    for (_, ref target) in targets.iter() {
                        cfg_block.add_next(target.as_usize());
                    }
                    cfg_block.add_next(targets.otherwise().as_usize());
                }
                TerminatorKind::Drop {
                    place: _,
                    target,
                    unwind,
                    replace: _,
                    drop: _,
                    #[cfg(not(rapx_rustc_ge_198))]
                        async_fut: _,
                } => {
                    cfg_block.add_next(target.as_usize());
                    if let UnwindAction::Cleanup(target) = unwind {
                        cfg_block.add_next(target.as_usize());
                    }
                }
                TerminatorKind::Call {
                    ref target,
                    ref unwind,
                    ..
                } => {
                    if let Some(tt) = target {
                        cfg_block.add_next(tt.as_usize());
                    }
                    if let UnwindAction::Cleanup(tt) = unwind {
                        cfg_block.add_next(tt.as_usize());
                    }
                }
                TerminatorKind::Assert {
                    cond: _,
                    expected: _,
                    msg: _,
                    ref target,
                    ref unwind,
                } => {
                    cfg_block.add_next(target.as_usize());
                    if let UnwindAction::Cleanup(target) = unwind {
                        cfg_block.add_next(target.as_usize());
                    }
                }
                TerminatorKind::Yield {
                    value: _,
                    ref resume,
                    resume_arg: _,
                    ref drop,
                } => {
                    cfg_block.add_next(resume.as_usize());
                    if let Some(target) = drop {
                        cfg_block.add_next(target.as_usize());
                    }
                }
                TerminatorKind::FalseEdge {
                    ref real_target,
                    imaginary_target: _,
                } => {
                    cfg_block.add_next(real_target.as_usize());
                }
                TerminatorKind::FalseUnwind {
                    ref real_target,
                    unwind: _,
                } => {
                    cfg_block.add_next(real_target.as_usize());
                }
                TerminatorKind::InlineAsm {
                    template: _,
                    operands: _,
                    options: _,
                    line_spans: _,
                    ref unwind,
                    targets,
                    asm_macro: _,
                } => {
                    for target in targets {
                        cfg_block.add_next(target.as_usize());
                    }
                    if let UnwindAction::Cleanup(target) = unwind {
                        cfg_block.add_next(target.as_usize());
                    }
                }
                _ => {}
            }

            cfg_blocks.push(cfg_block);
            assigned_locals.push(block_assigned_locals);
        }

        let cfg = ControlFlowGraph::new(def_id, tcx, cfg_blocks);

        PathGraph {
            cfg,
            assigned_locals,
            discriminants,
        }
    }

    pub fn find_scc(&mut self) {
        self.cfg.find_scc();
        self.populate_all_child_sccs();
    }

    pub fn def_id(&self) -> DefId {
        self.cfg.def_id
    }

    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.cfg.tcx
    }

    pub fn cfg_block(&self, index: usize) -> &CfgBlock {
        self.cfg.block(index)
    }

    pub fn cfg_block_mut(&mut self, index: usize) -> &mut CfgBlock {
        self.cfg.block_mut(index)
    }

    /// Retrieve the MIR terminator for the block at `index` on demand.
    pub fn terminator(&self, index: usize) -> Option<&Terminator<'tcx>> {
        self.cfg.terminator(index)
    }

    pub fn assigned_locals(&self, index: usize) -> Option<&FxHashSet<usize>> {
        self.assigned_locals.get(index)
    }

    /// Verify whether a given path (sequence of block indices) is reachable.
    ///
    /// The path can contain arbitrary loops. The verification uses
    /// discriminant/constant-based filtering: it tracks concrete values for
    /// enum discriminants across `SwitchInt` branches, invalidates them when
    /// the corresponding local is reassigned, and rejects transitions that
    /// contradict known constraints.
    ///
    /// Returns `false` if the path is empty or contains a transition that
    /// is provably unreachable.
    pub fn is_path_reachable(&self, path: &[usize]) -> bool {
        self.is_path_reachable_with(path, &FxHashMap::default())
    }

    /// Like `is_path_reachable` but accepts caller-provided initial
    /// constraints (e.g. accumulated before entering an SCC).
    pub fn is_path_reachable_with(
        &self,
        path: &[usize],
        initial: &FxHashMap<usize, usize>,
    ) -> bool {
        if path.is_empty() {
            return false;
        }
        if path.len() == 1 {
            return true;
        }

        let mut constraints: FxHashMap<usize, usize> = initial.clone();

        for i in 0..path.len() - 1 {
            let cur = path[i];
            let next = path[i + 1];

            if cur >= self.cfg.blocks.len() || next >= self.cfg.blocks.len() {
                return false;
            }

            // Invalidate constraints for locals assigned in the current block.
            if let Some(assigned) = self.assigned_locals.get(cur) {
                for local in assigned {
                    constraints.remove(local);
                }
            }

            let successors = &self.cfg.block(cur).next;

            // Fast path: if next is not even a CFG successor, it's impossible.
            if !successors.contains(&next) {
                // Cleanup blocks can be special; if this is a call/drop terminator,
                // also check unwind targets that may not be in `next` of the cfg block.
                if !self.is_unwind_target(cur, next) {
                    return false;
                }
            }

            // Handle SwitchInt with constraint tracking.
            if !self.check_switch_transition(cur, next, &mut constraints) {
                return false;
            }
        }

        true
    }

    /// Like `is_path_reachable` but returns the reconstructed discriminant
    /// constraints. Returns `None` if the path is unreachable.
    pub fn is_path_reachable_with_constraints(
        &self,
        path: &[usize],
    ) -> Option<FxHashMap<usize, usize>> {
        if path.is_empty() || path[0] != 0 {
            return None;
        }
        self.check_reachability(path)
    }

    /// Check a path segment with caller-provided initial constraints.
    /// Returns `None` if unreachable, otherwise the reconstructed constraints.
    pub fn check_segment_reachability_with(
        &self,
        path: &[usize],
        initial: &FxHashMap<usize, usize>,
    ) -> Option<FxHashMap<usize, usize>> {
        if path.len() <= 1 {
            return Some(initial.clone());
        }
        self.check_reachability_from(path, initial)
    }

    fn check_reachability(&self, path: &[usize]) -> Option<FxHashMap<usize, usize>> {
        self.check_reachability_from(path, &FxHashMap::default())
    }

    fn check_reachability_from(
        &self,
        path: &[usize],
        initial: &FxHashMap<usize, usize>,
    ) -> Option<FxHashMap<usize, usize>> {
        let mut constraints: FxHashMap<usize, usize> = initial.clone();

        for i in 0..path.len() - 1 {
            let cur = path[i];
            let next = path[i + 1];

            if cur >= self.cfg.blocks.len() || next >= self.cfg.blocks.len() {
                return None;
            }

            if let Some(assigned) = self.assigned_locals.get(cur) {
                for local in assigned {
                    constraints.remove(local);
                }
            }

            let successors = &self.cfg.block(cur).next;
            if !successors.contains(&next) {
                if !self.is_unwind_target(cur, next) {
                    return None;
                }
            }

            if !self.check_switch_transition(cur, next, &mut constraints) {
                return None;
            }
        }

        Some(constraints)
    }

    /// Check whether `cur → next` is a valid `SwitchInt` transition given
    /// current discriminant constraints. Returns `false` when the transition
    /// contradicts a known discriminant value. Also records newly learned
    /// constraints from the taken branch into `constraints`.
    fn check_switch_transition(
        &self,
        cur: usize,
        next: usize,
        constraints: &mut FxHashMap<usize, usize>,
    ) -> bool {
        let Some(terminator) = self.cfg.terminator(cur) else {
            return true;
        };

        match &terminator.kind {
            TerminatorKind::SwitchInt { discr, targets } => {
                let discr_local = discr.place().map(|p| p.local.as_usize());
                let constraint_local = discr_local
                    .and_then(|l| self.discriminants.get(&l).copied())
                    .or(discr_local);

                // Collect all possible successor blocks for this switch.
                let all_targets: FxHashSet<usize> = targets
                    .iter()
                    .map(|(_, bb)| bb.as_usize())
                    .chain(std::iter::once(targets.otherwise().as_usize()))
                    .collect();

                if !all_targets.contains(&next) {
                    return false;
                }

                // Try to evaluate a concrete constant for the discriminant.
                let const_val = match discr {
                    Operand::Constant(c) => c
                        .const_
                        .try_eval_target_usize(
                            self.cfg.tcx,
                            TypingEnv::post_analysis(self.cfg.tcx, self.cfg.def_id),
                        )
                        .map(|v| v as usize),
                    _ => None,
                };

                if let Some(val) = const_val {
                    // Discriminant is a literal constant — only one target is
                    // reachable.
                    let expected = resolve_switch_target(targets, val as u128);
                    if next != expected {
                        return false;
                    }
                    if let Some(local) = constraint_local {
                        constraints.insert(local, val);
                    }
                    return true;
                }

                if let Some(local) = constraint_local {
                    if let Some(&known_val) = constraints.get(&local) {
                        let expected = resolve_switch_target(targets, known_val as u128);
                        if next != expected {
                            return false;
                        }
                        return true;
                    }
                }

                // No prior constraint — conservatively allow any valid target
                // and record the newly learned constraint from the taken branch.
                if let Some(local) = constraint_local {
                    if let Some((val, _)) = targets.iter().find(|(_, bb)| bb.as_usize() == next) {
                        constraints.insert(local, val as usize);
                    } else {
                        if let Some(inferred) = self.infer_otherwise_value(targets, local) {
                            constraints.insert(local, inferred);
                        }
                    }
                }

                true
            }
            _ => true,
        }
    }

    /// For the "otherwise" branch of a `SwitchInt`, try to infer the single
    /// concrete value that the discriminant must have (because all other
    /// possible values are covered by explicit targets).
    fn infer_otherwise_value(&self, targets: &SwitchTargets, discr_local: usize) -> Option<usize> {
        let body = self.cfg.tcx.optimized_mir(self.cfg.def_id);
        let discr_ty = body.local_decls[Local::from_usize(discr_local)].ty;

        let possible_values: Vec<usize> = match discr_ty.kind() {
            TyKind::Bool => vec![0, 1],
            TyKind::Adt(adt_def, _) if adt_def.is_enum() => (0..adt_def.variants().len()).collect(),
            _ => return None,
        };

        let explicit_values: FxHashSet<usize> = targets.iter().map(|(v, _)| v as usize).collect();
        let remaining: Vec<usize> = possible_values
            .into_iter()
            .filter(|v| !explicit_values.contains(v))
            .collect();

        if remaining.len() == 1 {
            Some(remaining[0])
        } else {
            None
        }
    }

    /// Check whether `next` is an unwind target reachable from `cur` via a
    /// call or drop terminator (may not be recorded as a normal CFG successor).
    fn is_unwind_target(&self, cur: usize, next: usize) -> bool {
        let Some(terminator) = self.cfg.terminator(cur) else {
            return false;
        };

        let unwind = match &terminator.kind {
            TerminatorKind::Call { unwind, .. }
            | TerminatorKind::Drop { unwind, .. }
            | TerminatorKind::Assert { unwind, .. } => unwind,
            _ => return false,
        };

        if let UnwindAction::Cleanup(target) = unwind {
            return target.as_usize() == next;
        }
        false
    }

    /// Populate the `child_sccs` field for a given SCC entry block, then
    /// recurse into those child SCCs. Called eagerly from `find_scc()` so
    /// that enumeration can be purely read-only on the graph.
    fn populate_child_sccs(&mut self, enter: usize) {
        let nodes: Vec<usize> = self.cfg.block(enter).scc.nodes.iter().cloned().collect();
        let mut child_enters = Vec::new();
        let mut seen = FxHashSet::default();

        for node in nodes {
            if let Some(block) = self.cfg.blocks.get(node) {
                let node_enter = block.scc.enter;
                let non_trivial = !block.scc.nodes.is_empty();
                if node_enter != enter && non_trivial && seen.insert(node_enter) {
                    child_enters.push(node_enter);
                }
            }
        }

        self.cfg.block_mut(enter).scc.child_sccs = child_enters;

        let child_count = self.cfg.block(enter).scc.child_sccs.len();
        for i in 0..child_count {
            let child_enter = self.cfg.block(enter).scc.child_sccs[i];
            self.populate_child_sccs(child_enter);
        }
    }

    fn populate_all_child_sccs(&mut self) {
        let mut visited = FxHashSet::default();
        let block_count = self.cfg.blocks.len();
        for i in 0..block_count {
            let scc = &self.cfg.block(i).scc;
            let enter = scc.enter;
            if scc.nodes.is_empty() || !visited.insert(enter) {
                continue;
            }
            self.populate_child_sccs(enter);
        }
    }
}

/// Enumerates whole-CFG paths from a `PathGraph` into a `PathTree`.
///
/// Owns the SCC-path cache so that repeated enumeration (e.g. with different
/// `postfix_repeat` values) can reuse cached SCC paths. The underlying graph
/// is borrowed immutably — it must have `find_scc()` called beforehand.
pub struct PathEnumerator<'g, 'tcx> {
    graph: &'g PathGraph<'tcx>,
    scc_path_cache: FxHashMap<(DefId, usize, usize), Vec<SccEnumeratedPath>>,
}

impl<'g, 'tcx> PathEnumerator<'g, 'tcx> {
    pub fn new(graph: &'g PathGraph<'tcx>) -> Self {
        PathEnumerator {
            graph,
            scc_path_cache: FxHashMap::default(),
        }
    }

    /// Enumerate all structurally possible whole-CFG paths.
    ///
    /// SCC regions are flattened into a bounded set of acyclic paths. No
    /// constraint-based filtering is performed here — reachability checking
    /// is done separately via `PathGraph::is_path_reachable`.
    pub fn enumerate_paths(&mut self) -> PathTree {
        self.enumerate_paths_repeat(0)
    }

    /// Enumerate whole-CFG paths allowing each SCC postfix segment to repeat
    /// up to `postfix_repeat` additional times. `postfix_repeat = 0` gives
    /// the same result as `enumerate_paths`.
    pub fn enumerate_paths_repeat(&mut self, postfix_repeat: usize) -> PathTree {
        let mut tree = PathTree::new();

        if self.graph.cfg.blocks.is_empty() {
            return tree;
        }

        self.collect_whole_cfg_paths(0, &mut vec![0], &mut tree, 0, postfix_repeat);

        tree
    }

    /// Enumerate all structurally possible simple paths through `scc`
    /// starting at `start`.
    ///
    /// The SCC is traversed depth-first. `segment_counts` tracks how many
    /// times each postfix segment has appeared — when a segment's count
    /// exceeds `postfix_repeat + 1`, the branch is pruned.
    ///
    /// Results are cached per `(def_id, scc_enter)`.
    pub fn find_scc_paths(&mut self, start: usize, scc: &SccInfo) -> Vec<SccEnumeratedPath> {
        self.find_scc_paths_repeat(start, scc, 0)
    }

    /// Enumerate all structurally possible simple paths through `scc`,
    /// allowing the same postfix segment to repeat up to `postfix_repeat`
    /// additional times. `postfix_repeat = 0` is equivalent to the default
    /// `find_scc_paths`.
    ///
    /// Results are cached per `(def_id, scc_enter, postfix_repeat)`.
    pub fn find_scc_paths_repeat(
        &mut self,
        start: usize,
        scc: &SccInfo,
        postfix_repeat: usize,
    ) -> Vec<SccEnumeratedPath> {
        let cache_key = (self.graph.cfg.def_id, scc.enter, postfix_repeat);
        if let Some(cached) = self.scc_path_cache.get(&cache_key) {
            return cached.clone();
        }

        let mut out = Vec::new();
        let mut seen: FxHashSet<Vec<usize>> = FxHashSet::default();
        let mut path = vec![start];
        let mut segment_counts = FxHashMap::default();

        self.dfs_scc_tree(
            scc,
            start,
            &mut path,
            &mut segment_counts,
            postfix_repeat,
            &mut out,
            &mut seen,
            0,
        );

        if self.scc_path_cache.len() >= SCC_PATH_CACHE_LIMIT {
            self.scc_path_cache.clear();
        }
        self.scc_path_cache.insert(cache_key, out.clone());

        out
    }

    /// Recursive DFS through one level of the SCC tree.
    ///
    /// Enumerates structurally possible paths through the SCC to exit points.
    /// No constraint tracking — `check_postfix_segment` prunes repeated
    /// loop-body segments purely by block-id sequence.
    ///
    /// When `postfix_repeat > 0`, allows the same postfix segment to repeat
    /// up to `postfix_repeat` additional times beyond the first occurrence.
    ///
    /// Child SCC paths are pre-enumerated via `find_scc_paths` and treated as
    /// atomic building blocks (no recursive descent into child SCC internals).
    #[allow(clippy::too_many_arguments)]
    fn dfs_scc_tree(
        &mut self,
        scc: &SccInfo,
        cur: usize,
        path: &mut Vec<usize>,
        segment_counts: &mut FxHashMap<Vec<usize>, usize>,
        postfix_repeat: usize,
        out: &mut Vec<SccEnumeratedPath>,
        seen_paths: &mut FxHashSet<Vec<usize>>,
        depth: usize,
    ) {
        if depth > SCC_MAX_DEPTH {
            return;
        }
        if out.len() >= SCC_MAX_SEEN_PATHS {
            return;
        }
        if path.len() > SCC_MAX_PATH_LEN {
            return;
        }
        if cur != scc.enter && !scc.nodes.contains(&cur) {
            return;
        }

        if cur == scc.enter && path.len() > 1 {
            if !check_postfix_segment(path, scc.enter, segment_counts, postfix_repeat) {
                if scc.exits.iter().any(|e| e.exit == cur) {
                    self.record_unique_path(path, scc, out, seen_paths);
                }
                return;
            }
        }

        if scc.exits.iter().any(|e| e.exit == cur) {
            self.record_unique_path(path, scc, out, seen_paths);
        }

        let is_child = scc.child_sccs.contains(&cur);

        if is_child {
            let child_scc = self.graph.cfg_block(cur).scc.clone();
            let child_paths = self.find_scc_paths_repeat(cur, &child_scc, postfix_repeat);

            for child_path in &child_paths {
                if child_path.blocks.len() <= 1 {
                    continue;
                }
                let orig_len = path.len();
                path.extend(&child_path.blocks[1..]);

                for &next in &child_path.exit_successors {
                    path.push(next);
                    self.dfs_scc_tree(
                        scc,
                        next,
                        path,
                        segment_counts,
                        postfix_repeat,
                        out,
                        seen_paths,
                        depth + 1,
                    );
                    path.pop();
                }
                path.truncate(orig_len);
            }
            return;
        }

        let successors = self.enumerate_scc_traversals(cur);
        let saved_counts = segment_counts.clone();
        for next in successors {
            if next != scc.enter && !scc.nodes.contains(&next) {
                self.record_unique_path(path, scc, out, seen_paths);
                continue;
            }
            let mut branch_counts = saved_counts.clone();
            path.push(next);
            self.dfs_scc_tree(
                scc,
                next,
                path,
                &mut branch_counts,
                postfix_repeat,
                out,
                seen_paths,
                depth + 1,
            );
            path.pop();
        }
    }

    /// Return all CFG successors of `cur` as traversal actions.
    ///
    /// No constraint-based narrowing — purely structural.
    fn enumerate_scc_traversals(&self, cur: usize) -> Vec<usize> {
        self.graph.cfg.block(cur).next.iter().copied().collect()
    }

    /// Depth-first enumeration of all CFG paths from `current` to a terminator.
    ///
    /// SCC nodes are flattened via `find_scc_paths`; non-SCC blocks are followed
    /// one by one.  No cycle detection is needed because the post-SCC CFG is a DAG.
    fn collect_whole_cfg_paths(
        &mut self,
        current: usize,
        path: &mut Vec<usize>,
        tree: &mut PathTree,
        depth: usize,
        postfix_repeat: usize,
    ) {
        if current >= self.graph.cfg.blocks.len() {
            return;
        }
        if depth > WHOLE_CFG_PATH_DEPTH_LIMIT || tree.len() >= WHOLE_CFG_PATH_LIMIT {
            return;
        }

        let scc_info = self.graph.cfg_block(current).scc.clone();
        let is_scc = current == scc_info.enter && !scc_info.nodes.is_empty();
        if is_scc {
            let scc = self.sort_scc_tree(&scc_info);
            let segments = self.find_scc_paths_repeat(current, &scc, postfix_repeat);

            if segments.is_empty() {
                if self.graph.is_path_reachable(path) {
                    tree.insert(path);
                }
                return;
            }

            for seg in segments {
                if tree.len() >= WHOLE_CFG_PATH_LIMIT {
                    break;
                }

                let orig_len = path.len();
                if seg.blocks.len() > 1 {
                    path.extend_from_slice(&seg.blocks[1..]);
                }

                if seg.exit_successors.is_empty() {
                    if self.graph.is_path_reachable(path) {
                        tree.insert(path);
                    }
                } else {
                    for &next in &seg.exit_successors {
                        path.push(next);
                        self.collect_whole_cfg_paths(next, path, tree, depth + 1, postfix_repeat);
                        path.pop();
                    }
                }

                path.truncate(orig_len);
            }
            return;
        }

        // Non-SCC block: follow CFG successors.
        let successors: Vec<usize> = self.graph.cfg_block(current).next.iter().copied().collect();
        if successors.is_empty() {
            if self.graph.is_path_reachable(path) {
                tree.insert(path);
            }
            return;
        }

        for next in successors {
            path.push(next);
            self.collect_whole_cfg_paths(next, path, tree, depth + 1, postfix_repeat);
            path.pop();
        }
    }

    fn sort_scc_tree(&self, scc: &SccInfo) -> SccInfo {
        self.graph.cfg_block(scc.enter).scc.clone()
    }

    fn record_unique_path(
        &self,
        path: &[usize],
        scc: &SccInfo,
        out: &mut Vec<SccEnumeratedPath>,
        seen_paths: &mut FxHashSet<Vec<usize>>,
    ) {
        if !seen_paths.insert(path.to_vec()) {
            return;
        }
        let exit_successors = self.compute_exit_successors(path, scc);
        out.push(SccEnumeratedPath {
            blocks: path.to_vec(),
            exit_successors,
        });
    }

    fn compute_exit_successors(&self, path: &[usize], scc: &SccInfo) -> Vec<usize> {
        let Some(&last) = path.last() else {
            return vec![];
        };
        scc.exits
            .iter()
            .filter(|e| e.exit == last)
            .map(|e| e.to)
            .filter(|&n| !scc.child_sccs.contains(&self.graph.cfg.block(n).scc.enter()))
            .collect()
    }
}

/// Resolve a concrete discriminant value to the corresponding `SwitchInt`
/// successor block index.
fn resolve_switch_target(targets: &SwitchTargets, val: u128) -> usize {
    targets
        .iter()
        .find(|(v, _)| *v == val)
        .map(|(_, bb)| bb.as_usize())
        .unwrap_or_else(|| targets.otherwise().as_usize())
}
