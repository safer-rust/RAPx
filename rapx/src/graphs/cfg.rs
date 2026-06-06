use crate::graphs::scc::{Scc, SccExit, SccInfo};
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_middle::{mir::Terminator, ty::TyCtxt};
use rustc_span::def_id::DefId;

/// Reusable CFG block structure shared by analyses built over MIR.
#[derive(Debug, Clone)]
pub struct CfgBlock<'tcx> {
    pub index: usize,
    pub is_cleanup: bool,
    pub next: FxHashSet<usize>,
    pub terminator: Option<Terminator<'tcx>>,
    /// Used in SCC/path handling to clear stale path constraints after assignments.
    pub assigned_locals: FxHashSet<usize>,
    /// All nodes belonging to the SCC represented by this block.
    pub scc: SccInfo,
}

impl<'tcx> CfgBlock<'tcx> {
    pub fn new(index: usize, is_cleanup: bool) -> Self {
        Self {
            index,
            is_cleanup,
            next: FxHashSet::default(),
            terminator: None,
            assigned_locals: FxHashSet::default(),
            scc: SccInfo::new(index),
        }
    }

    pub fn add_next(&mut self, index: usize) {
        self.next.insert(index);
    }
}

/// Control-flow graph metadata independent from any particular analysis facts.
#[derive(Clone)]
pub struct ControlFlowGraph<'tcx> {
    pub def_id: DefId,
    pub tcx: TyCtxt<'tcx>,
    pub blocks: Vec<CfgBlock<'tcx>>,
    /// Path-sensitive constants tracked during traversal.
    pub constants: FxHashMap<usize, usize>,
    /// Path-sensitive discriminant source mapping tracked during traversal.
    pub discriminants: FxHashMap<usize, usize>,
    pub visit_times: usize,
}

impl<'tcx> ControlFlowGraph<'tcx> {
    pub fn new(def_id: DefId, tcx: TyCtxt<'tcx>, blocks: Vec<CfgBlock<'tcx>>) -> Self {
        Self {
            def_id,
            tcx,
            blocks,
            constants: FxHashMap::default(),
            discriminants: FxHashMap::default(),
            visit_times: 0,
        }
    }

    pub fn block(&self, index: usize) -> &CfgBlock<'tcx> {
        &self.blocks[index]
    }

    pub fn block_mut(&mut self, index: usize) -> &mut CfgBlock<'tcx> {
        &mut self.blocks[index]
    }

    /// Enumerate acyclic CFG paths from the current block to an exit block.
    ///
    /// MIR loops are represented as back edges in `CfgBlock::next`. The path
    /// consumer only needs one finite traversal that reaches each unsafe
    /// callsite, so this DFS cuts a path when it would revisit a block already
    /// on the current stack. Non-cycle successors are still explored, which
    /// keeps loop exits visible without risking unbounded path growth.
    pub fn dfs_on_spanning_tree(
        &self,
        index: usize,
        stack: &mut Vec<usize>,
        paths: &mut Vec<Vec<usize>>,
    ) {
        const PATH_ENUM_LIMIT: usize = 4000;

        if paths.len() >= PATH_ENUM_LIMIT {
            return;
        }
        if index >= self.blocks.len() {
            return;
        }

        let mut nexts: Vec<usize> = self.block(index).next.iter().copied().collect();
        nexts.sort_unstable();

        if nexts.is_empty() {
            paths.push(stack.clone());
            return;
        }

        let mut followed = false;
        for next in nexts {
            if paths.len() >= PATH_ENUM_LIMIT {
                break;
            }
            if next >= self.blocks.len() {
                continue;
            }
            if stack.contains(&next) {
                paths.push(stack.clone());
                continue;
            }

            followed = true;
            stack.push(next);
            self.dfs_on_spanning_tree(next, stack, paths);
            stack.pop();
        }

        if !followed {
            paths.push(stack.clone());
        }
    }

    /// Return all finite MIR CFG paths starting from the entry block.
    pub fn get_paths(&self) -> Vec<Vec<usize>> {
        let mut paths = Vec::new();
        if self.blocks.is_empty() {
            return paths;
        }
        let mut stack = vec![0];
        self.dfs_on_spanning_tree(0, &mut stack, &mut paths);
        paths
    }

    pub fn get_all_branch_sub_blocks_paths(&self) -> Vec<Vec<usize>> {
        let all_paths = self.get_paths();
        let mut unique_branch_sub_blocks = FxHashSet::<Vec<usize>>::default();

        for path in all_paths {
            let branch_blocks_for_this_path = self.get_branch_sub_blocks_for_path(&path);
            rap_debug!(
                "Branch blocks for path {:?}: {:?}",
                path,
                branch_blocks_for_this_path
            );
            unique_branch_sub_blocks.insert(branch_blocks_for_this_path);
        }

        unique_branch_sub_blocks.into_iter().collect()
    }

    pub fn get_branch_sub_blocks_for_path(&self, path: &[usize]) -> Vec<usize> {
        let mut expanded_path = Vec::new();
        let mut processed_scc_indices = FxHashSet::default();

        for &block_idx in path {
            let scc_idx = self.block(block_idx).scc.enter;
            processed_scc_indices.insert(scc_idx);
            expanded_path.push(scc_idx);
        }

        expanded_path
    }

    pub fn sort_scc_tree(&mut self, scc: &SccInfo) -> SccInfo {
        self.populate_child_sccs(scc.enter);
        self.block(scc.enter).scc.clone()
    }

    fn populate_child_sccs(&mut self, enter: usize) {
        let nodes: Vec<usize> = self.block(enter).scc.nodes.iter().cloned().collect();
        let mut child_enters = Vec::new();
        let mut seen = FxHashSet::default();

        for node in nodes {
            if let Some(block) = self.blocks.get(node) {
                let node_enter = block.scc.enter;
                let non_trivial = !block.scc.nodes.is_empty();
                if node_enter != enter && non_trivial && seen.insert(node_enter) {
                    child_enters.push(node_enter);
                }
            }
        }

        self.block_mut(enter).scc.child_sccs = child_enters;

        for &child_enter in &self.block(enter).scc.child_sccs.clone() {
            self.populate_child_sccs(child_enter);
        }
    }

    pub fn visit_times(&self) -> usize {
        self.visit_times
    }

    pub fn increment_visit_times(&mut self) -> usize {
        self.visit_times += 1;
        self.visit_times
    }
}

pub fn scc_handler<'tcx>(
    graph: &mut ControlFlowGraph<'tcx>,
    root: usize,
    scc_components: &[usize],
) {
    rap_debug!(
        "Scc found: root = {}, components = {:?}",
        root,
        scc_components
    );
    graph.block_mut(root).scc.enter = root;
    if scc_components.len() <= 1 {
        return;
    }

    let nexts = graph.block(root).next.clone();
    for next in nexts {
        if !scc_components.contains(&next) {
            let scc_exit = SccExit::new(root, next);
            graph.block_mut(root).scc.exits.insert(scc_exit);
        }
    }

    for &node in &scc_components[1..] {
        graph.block_mut(root).scc.nodes.insert(node);
        graph.block_mut(node).scc.enter = root;
        let nexts = graph.block(node).next.clone();
        for next in nexts {
            if !scc_components.contains(&next) {
                let scc_exit = SccExit::new(node, next);
                graph.block_mut(root).scc.exits.insert(scc_exit);
            }
            if next == root {
                graph.block_mut(root).scc.backnodes.insert(node);
            }
        }
    }

    rap_debug!("Scc Info: {:?}", graph.block(root).scc);
    let mut backups: Vec<(usize, FxHashSet<usize>)> = Vec::new();

    let block0 = graph.block_mut(0);
    backups.push((0, block0.next.clone()));
    block0.next.clear();
    block0.next.insert(root);

    let scc_exits = graph.block(root).scc.exits.clone();
    let backnodes = graph.block(root).scc.backnodes.clone();

    for &node in &scc_components[1..] {
        let block = graph.block_mut(node);
        if backnodes.contains(&node) {
            backups.push((node, block.next.clone()));
            block.next.remove(&root);
        }
    }

    for exit in &scc_exits {
        let block_to = graph.block_mut(exit.to);
        backups.push((exit.to, block_to.next.clone()));
        block_to.next.clear();
    }
    graph.find_scc();

    for backup in &backups {
        graph.block_mut(backup.0).next = backup.1.clone();
    }
}

impl<'tcx> Scc for ControlFlowGraph<'tcx> {
    fn on_scc_found(&mut self, root: usize, scc_components: &[usize]) {
        scc_handler(self, root, scc_components);
    }

    fn get_next(&mut self, root: usize) -> FxHashSet<usize> {
        self.block(root).next.clone()
    }

    fn get_size(&mut self) -> usize {
        self.blocks.len()
    }
}
