use crate::graphs::{
    cfg::{CfgBlock, ControlFlowGraph},
    scc::{Scc, SccInfo},
};
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_middle::{
    mir::{BasicBlock, Rvalue, StatementKind, Terminator, TerminatorKind, UnwindAction},
    ty::TyCtxt,
};
use rustc_span::def_id::DefId;
use std::cell::RefCell;

/// Maximum number of whole-CFG paths collected before stopping enumeration.
const WHOLE_CFG_PATH_LIMIT: usize = 4000;
/// Maximum DFS depth for whole-CFG path enumeration.
const WHOLE_CFG_PATH_DEPTH_LIMIT: usize = 256;
/// Bounded cache for SCC path enumeration.
const SCC_PATH_CACHE_LIMIT: usize = 2048;

thread_local! {
    static SCC_PATH_CACHE: RefCell<
        FxHashMap<SccPathCacheKey, Vec<SccEnumeratedPath>>
    > = RefCell::new(FxHashMap::default());
}

#[derive(Clone, Hash, PartialEq, Eq)]
struct PathKey {
    path: Vec<usize>,
    constraints: Vec<(usize, usize)>,
}

#[derive(Clone, Hash, PartialEq, Eq)]
struct SccPathCacheKey {
    def_id: DefId,
    scc_enter: usize,
    constraints: Vec<(usize, usize)>,
}

impl SccPathCacheKey {
    fn new(def_id: DefId, scc_enter: usize, initial_constraints: &FxHashMap<usize, usize>) -> Self {
        Self {
            def_id,
            scc_enter,
            constraints: constraints_key(initial_constraints),
        }
    }
}

pub type SccPathConstraints = FxHashMap<usize, usize>;

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

    pub fn is_cur_in_scc(&self, scc: &SccInfo) -> bool {
        node_is_in_current_scc(self.start, scc, self.cur)
    }

    pub fn is_node_in_scc(&self, scc: &SccInfo, node: usize) -> bool {
        node_is_in_current_scc(self.start, scc, node)
    }

    pub fn exceeds_complexity_limits(
        &self,
        max_path_len: usize,
        max_seen_paths: usize,
        seen_paths_len: usize,
    ) -> bool {
        self.path.len() > max_path_len || seen_paths_len > max_seen_paths
    }

    pub fn prepare_for_current_node(&mut self) -> bool {
        if self.cur != self.start {
            return true;
        }

        if self.path.len() > 1 {
            let prev_start_pos = self.path[..self.path.len() - 1]
                .iter()
                .rposition(|&node| node == self.start)
                .unwrap_or(0);
            let cycle_nodes = &self.path[prev_start_pos + 1..self.path.len() - 1];
            let introduces_new = cycle_nodes
                .iter()
                .any(|node| !self.baseline_at_dominator.contains(node));
            if !introduces_new {
                return false;
            }
        }

        self.baseline_at_dominator = self.visited_since_enter.clone();
        self.segment_stack.clear();
        self.segment_stack.insert(self.start);
        true
    }

    pub fn can_descend_to(&self, next: usize) -> bool {
        !self.segment_stack.contains(&next) || next == self.start
    }

    pub fn descend_to(&self, next: usize) -> Self {
        let mut next_state = self.clone();
        next_state.cur = next;
        next_state.path.push(next);
        next_state.segment_stack.insert(next);
        next_state.visited_since_enter.insert(next);
        next_state.skip_child_enter = None;
        next_state
    }

    pub fn with_skip_child_enter(&self, child_enter: usize) -> Self {
        let mut next_state = self.clone();
        next_state.skip_child_enter = Some(child_enter);
        next_state
    }

    pub fn with_spliced_path(&self, spliced_path: Vec<usize>, skip_child_enter: Option<usize>) -> Self {
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

#[derive(Clone)]
pub struct PathGraph<'tcx> {
    pub cfg: ControlFlowGraph<'tcx>,
    /// Path-analysis-specific metadata: locals assigned in each block.
    pub assigned_locals: Vec<FxHashSet<usize>>,
    /// Path-analysis-specific metadata: discriminant local -> source local mapping.
    pub discriminants: FxHashMap<usize, usize>,
}

type OnNodeEnterFn<C> = fn(&mut C, usize, &mut SccPathConstraints);
type EnumerateChildPathsFn<C> = fn(&mut C, usize, &SccPathConstraints) -> Vec<SccEnumeratedPath>;
type EnumerateActionsFn<C> =
    fn(&mut C, &SccInfo, &SccPathTraversalState, &SccPathConstraints) -> Vec<SccPathAction>;

pub(crate) fn enumerate_scc_paths_cached_with<C>(
    def_id: DefId,
    start: usize,
    scc: &SccInfo,
    initial_constraints: SccPathConstraints,
    context: &mut C,
    on_node_enter: OnNodeEnterFn<C>,
    enumerate_child_paths: EnumerateChildPathsFn<C>,
    enumerate_actions: EnumerateActionsFn<C>,
    config: SccPathTraversalConfig,
) -> Vec<SccEnumeratedPath> {
    let key = SccPathCacheKey::new(def_id, scc.enter, &initial_constraints);
    if let Some(cached) = SCC_PATH_CACHE.with(|c| c.borrow().get(&key).cloned()) {
        return cached;
    }

    let all_paths = enumerate_scc_paths_with(
        start,
        scc,
        initial_constraints,
        context,
        on_node_enter,
        enumerate_child_paths,
        enumerate_actions,
        config,
    );

    SCC_PATH_CACHE.with(|c| {
        let mut cache = c.borrow_mut();
        if cache.len() >= SCC_PATH_CACHE_LIMIT {
            cache.clear();
        }
        cache.insert(key, all_paths.clone());
    });

    all_paths
}

fn enumerate_scc_paths_with<C>(
    start: usize,
    scc: &SccInfo,
    initial_constraints: SccPathConstraints,
    context: &mut C,
    on_node_enter: OnNodeEnterFn<C>,
    enumerate_child_paths: EnumerateChildPathsFn<C>,
    enumerate_actions: EnumerateActionsFn<C>,
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
        context,
        on_node_enter,
        enumerate_child_paths,
        enumerate_actions,
        &config,
        0,
    );
    all_paths
}

fn enumerate_scc_paths_inner<C>(
    scc: &SccInfo,
    state: SccPathTraversalState,
    mut path_constraints: SccPathConstraints,
    paths_in_scc: &mut Vec<SccEnumeratedPath>,
    seen_paths: &mut FxHashSet<PathKey>,
    context: &mut C,
    on_node_enter: OnNodeEnterFn<C>,
    enumerate_child_paths: EnumerateChildPathsFn<C>,
    enumerate_actions: EnumerateActionsFn<C>,
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

    if state.exceeds_complexity_limits(config.max_path_len, config.max_seen_paths, seen_paths.len()) {
        return;
    }

    if !state.is_cur_in_scc(scc) {
        return;
    }

    let mut state = state;
    if !state.prepare_for_current_node() {
        return;
    }

    on_node_enter(context, state.cur, &mut path_constraints);

    for &child_enter in &scc.child_sccs {
        if state.cur != child_enter {
            continue;
        }

        if state.skip_child_enter == Some(child_enter) {
            break;
        }

        let sub_paths = enumerate_child_paths(context, child_enter, &path_constraints);

        enumerate_scc_paths_inner(
            scc,
            state.with_skip_child_enter(child_enter),
            path_constraints.clone(),
            paths_in_scc,
            seen_paths,
            context,
            on_node_enter,
            enumerate_child_paths,
            enumerate_actions,
            config,
            depth + 1,
        );

        for sub_path in sub_paths {
            if sub_path.blocks.len() <= 1 {
                continue;
            }

            let mut new_path = state.path.clone();
            new_path.extend(&sub_path.blocks[1..]);
            let new_cur = *new_path.last().expect("spliced child path must be non-empty");
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
                context,
                on_node_enter,
                enumerate_child_paths,
                enumerate_actions,
                config,
                depth + 1,
            );
        }
        return;
    }

    for action in enumerate_actions(context, scc, &state, &path_constraints) {
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
                    context,
                    on_node_enter,
                    enumerate_child_paths,
                    enumerate_actions,
                    config,
                    depth + 1,
                );
            }
        }
    }
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
                if let StatementKind::Assign(box (place, rvalue)) = &stmt.kind {
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

    pub fn enumerate_paths(&mut self) -> Vec<Vec<usize>> {
        let mut all_paths = Vec::new();
        let mut seen_paths = FxHashSet::default();

        if self.cfg.blocks.is_empty() {
            return all_paths;
        }

        let mut current_path = vec![0];
        let mut active_blocks = FxHashSet::default();
        active_blocks.insert(0);

        self.collect_path_sensitive_paths_inner(
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

    pub fn sort_scc_tree(&mut self, scc: &SccInfo) -> SccInfo {
        self.populate_child_sccs(scc.enter);
        self.cfg.block(scc.enter).scc.clone()
    }

    pub fn find_scc_paths(
        &mut self,
        start: usize,
        scc: &SccInfo,
        initial_constraints: &FxHashMap<usize, usize>,
    ) -> Vec<SccEnumeratedPath> {
        let def_id = self.cfg.def_id;
        enumerate_scc_paths_cached_with(
            def_id,
            start,
            scc,
            initial_constraints.clone(),
            self,
            PathGraph::on_scc_node_enter,
            PathGraph::enumerate_child_scc_paths,
            PathGraph::enumerate_scc_actions,
            SccPathTraversalConfig::default(),
        )
    }

    fn on_scc_node_enter(&mut self, node: usize, constraints: &mut FxHashMap<usize, usize>) {
        if let Some(assigned_locals) = self.assigned_locals.get(node) {
            for local in assigned_locals {
                constraints.remove(local);
            }
        }
    }

    fn enumerate_child_scc_paths(
        &mut self,
        child_enter: usize,
        constraints: &FxHashMap<usize, usize>,
    ) -> Vec<SccEnumeratedPath> {
        let child_scc = self.cfg.block(child_enter).scc.clone();
        self.find_scc_paths(child_enter, &child_scc, constraints)
    }

    fn enumerate_scc_actions(
        &mut self,
        _scc: &SccInfo,
        state: &SccPathTraversalState,
        constraints: &FxHashMap<usize, usize>,
    ) -> Vec<SccPathAction> {
        let mut actions = vec![SccPathAction::RecordExit {
            constraints: constraints.clone(),
        }];
        for next in self.cfg.block(state.cur).next.clone() {
            actions.push(SccPathAction::Traverse {
                next,
                constraints: constraints.clone(),
            });
        }
        actions
    }

    fn collect_path_sensitive_paths_inner(
        &mut self,
        current: usize,
        current_path: &mut Vec<usize>,
        active_blocks: &mut FxHashSet<usize>,
        all_paths: &mut Vec<Vec<usize>>,
        seen_paths: &mut FxHashSet<Vec<usize>>,
        depth: usize,
    ) {
        if depth > WHOLE_CFG_PATH_DEPTH_LIMIT
            || all_paths.len() >= WHOLE_CFG_PATH_LIMIT
            || current >= self.cfg.blocks.len()
        {
            return;
        }

        let cur_scc_enter = self.cfg.block(current).scc.enter;
        if current == cur_scc_enter && !self.cfg.block(current).scc.nodes.is_empty() {
            let cur_scc = self.cfg.block(current).scc.clone();
            let scc = self.sort_scc_tree(&cur_scc);
            let paths_in_scc = self.find_scc_paths(current, &scc, &FxHashMap::default());

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

                let mut nexts: Vec<usize> = self
                    .cfg
                    .block(last)
                    .next
                    .iter()
                    .copied()
                    .filter(|&next| self.cfg.block(next).scc.enter != cur_scc_enter)
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
                    self.collect_path_sensitive_paths_inner(
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

        let mut nexts: Vec<usize> = self.cfg.block(current).next.iter().copied().collect();
        nexts.sort_unstable();
        nexts.dedup();

        if nexts.is_empty() {
            if seen_paths.insert(current_path.clone()) {
                all_paths.push(current_path.clone());
            }
            return;
        }

        for next in nexts {
            if active_blocks.contains(&next) {
                if seen_paths.insert(current_path.clone()) {
                    all_paths.push(current_path.clone());
                }
                continue;
            }

            active_blocks.insert(next);
            current_path.push(next);
            self.collect_path_sensitive_paths_inner(
                next,
                current_path,
                active_blocks,
                all_paths,
                seen_paths,
                depth + 1,
            );
            current_path.pop();
            active_blocks.remove(&next);
        }
    }

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
        for &child_enter in &self.cfg.block(enter).scc.child_sccs.clone() {
            self.populate_child_sccs(child_enter);
        }
    }
}

pub(crate) fn constraints_key(constraints: &FxHashMap<usize, usize>) -> Vec<(usize, usize)> {
    let mut sorted_constraints: Vec<(usize, usize)> =
        constraints.iter().map(|(k, val)| (*k, *val)).collect();
    sorted_constraints.sort_unstable();
    sorted_constraints
}

fn make_path_key(path: &[usize], constraints: &FxHashMap<usize, usize>) -> PathKey {
    PathKey {
        path: path.to_vec(),
        constraints: constraints_key(constraints),
    }
}

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

fn node_is_in_current_scc(start: usize, scc: &SccInfo, node: usize) -> bool {
    node == start || scc.nodes.contains(&node)
}

fn rebuild_segment_stack(path: &[usize], start: usize) -> FxHashSet<usize> {
    let last_start_pos = path.iter().rposition(|&node| node == start).unwrap_or(0);
    let mut segment_stack = FxHashSet::default();
    for node in &path[last_start_pos..] {
        segment_stack.insert(*node);
    }
    segment_stack
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
