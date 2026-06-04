use crate::graphs::{
    cfg::{CfgBlock, ControlFlowGraph},
    scc::{Scc, SccExit, SccInfo},
};
use rustc_data_structures::fx::FxHashSet;

/// Meet-over-paths metadata attached to a CFG block.
#[derive(Debug, Clone)]
pub struct MopBlockInfo {
    /// Used in SCC/path handling to clear stale path constraints after assignments.
    pub assigned_locals: FxHashSet<usize>,
    /// All nodes belonging to the SCC represented by this block.
    pub scc: SccInfo,
}

impl MopBlockInfo {
    pub fn new(index: usize) -> Self {
        Self {
            assigned_locals: FxHashSet::default(),
            scc: SccInfo::new(index),
        }
    }
}

/// Reusable MOP traversal state layered on top of a MIR CFG.
#[derive(Clone)]
pub struct MeetOverPathsGraph<'tcx> {
    pub cfg: ControlFlowGraph<'tcx>,
    pub blocks: Vec<MopBlockInfo>,
    pub visit_times: usize,
}

impl<'tcx> MeetOverPathsGraph<'tcx> {
    pub fn new(cfg: ControlFlowGraph<'tcx>, blocks: Vec<MopBlockInfo>) -> Self {
        Self {
            cfg,
            blocks,
            visit_times: 0,
        }
    }

    pub fn cfg_block(&self, index: usize) -> &CfgBlock<'tcx> {
        &self.cfg.blocks[index]
    }

    pub fn cfg_block_mut(&mut self, index: usize) -> &mut CfgBlock<'tcx> {
        &mut self.cfg.blocks[index]
    }

    pub fn mop_block(&self, index: usize) -> &MopBlockInfo {
        &self.blocks[index]
    }

    pub fn mop_block_mut(&mut self, index: usize) -> &mut MopBlockInfo {
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
        if index >= self.cfg.blocks.len() {
            return;
        }

        let mut nexts: Vec<usize> = self.cfg_block(index).next.iter().copied().collect();
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
            if next >= self.cfg.blocks.len() {
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
        if self.cfg.blocks.is_empty() {
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
            let scc_idx = self.mop_block(block_idx).scc.enter;

            if processed_scc_indices.insert(scc_idx) {
                expanded_path.push(scc_idx);
            } else {
                expanded_path.push(scc_idx);
            }
        }

        expanded_path
    }

    pub fn sort_scc_tree(&mut self, scc: &SccInfo) -> SccInfo {
        self.populate_child_sccs(scc.enter);
        self.mop_block(scc.enter).scc.clone()
    }

    fn populate_child_sccs(&mut self, enter: usize) {
        let nodes: Vec<usize> = self.mop_block(enter).scc.nodes.iter().cloned().collect();
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

        self.mop_block_mut(enter).scc.child_sccs = child_enters;

        for &child_enter in &self.mop_block(enter).scc.child_sccs.clone() {
            self.populate_child_sccs(child_enter);
        }
    }
}

pub fn scc_handler<'tcx>(
    graph: &mut MeetOverPathsGraph<'tcx>,
    root: usize,
    scc_components: &[usize],
) {
    rap_debug!(
        "Scc found: root = {}, components = {:?}",
        root,
        scc_components
    );
    graph.mop_block_mut(root).scc.enter = root;
    if scc_components.len() <= 1 {
        return;
    }

    let nexts = graph.cfg_block(root).next.clone();
    for next in nexts {
        if !scc_components.contains(&next) {
            let scc_exit = SccExit::new(root, next);
            graph.mop_block_mut(root).scc.exits.insert(scc_exit);
        }
    }

    for &node in &scc_components[1..] {
        graph.mop_block_mut(root).scc.nodes.insert(node);
        graph.mop_block_mut(node).scc.enter = root;
        let nexts = graph.cfg_block(node).next.clone();
        for next in nexts {
            if !scc_components.contains(&next) {
                let scc_exit = SccExit::new(node, next);
                graph.mop_block_mut(root).scc.exits.insert(scc_exit);
            }
            if next == root {
                graph.mop_block_mut(root).scc.backnodes.insert(node);
            }
        }
    }

    rap_debug!("Scc Info: {:?}", graph.mop_block(root).scc);
    let mut backups: Vec<(usize, FxHashSet<usize>)> = Vec::new();

    let block0 = graph.cfg_block_mut(0);
    backups.push((0, block0.next.clone()));
    block0.next.clear();
    block0.next.insert(root);

    let scc_exits = graph.mop_block(root).scc.exits.clone();
    let backnodes = graph.mop_block(root).scc.backnodes.clone();

    for &node in scc_components.iter() {
        let block = graph.cfg_block_mut(node);
        if backnodes.contains(&node) {
            backups.push((node, block.next.clone()));
            block.next.remove(&root);
        }
    }

    for exit in &scc_exits {
        let block_to = graph.cfg_block_mut(exit.to);
        backups.push((exit.to, block_to.next.clone()));
        block_to.next.clear();
    }
    graph.find_scc();

    for backup in &backups {
        graph.cfg_block_mut(backup.0).next = backup.1.clone();
    }
}

impl<'tcx> Scc for MeetOverPathsGraph<'tcx> {
    fn on_scc_found(&mut self, root: usize, scc_components: &[usize]) {
        scc_handler(self, root, scc_components);
    }

    fn get_next(&mut self, root: usize) -> FxHashSet<usize> {
        self.cfg_block(root).next.clone()
    }

    fn get_size(&mut self) -> usize {
        self.cfg.blocks.len()
    }
}
