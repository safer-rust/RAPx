//! Path extraction for verification targets.
//!
//! This module builds finite paths from a function CFG to each unsafe callsite.
//! Loops are kept finite by treating a loop as a single step through one of its
//! exits when the target callsite is outside the loop.  If the target callsite is
//! inside a loop, the path starts at the loop header and reaches the callsite
//! within one loop iteration.

use std::fmt;

use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def_id::DefId;
use rustc_middle::{mir::BasicBlock, ty::TyCtxt};

use crate::utils::scc::Scc;

use super::helpers::{CFG, Callsite, CallsiteLocation};

/// Extracts loop-aware paths for one function body.
pub struct PathExtractor<'tcx> {
    cfg: CFG,
    callsites: Vec<Callsite<'tcx>>,
    loops: Vec<LoopInfo>,
    block_to_loop: FxHashMap<BasicBlock, LoopId>,
    paths: FxHashMap<CallsiteLocation, Vec<Path>>,
}

impl<'tcx> PathExtractor<'tcx> {
    /// Create a path extractor for `def_id` and the callsites found in that body.
    pub fn new(tcx: TyCtxt<'tcx>, def_id: DefId, callsites: Vec<Callsite<'tcx>>) -> Self {
        Self {
            cfg: CFG::new(tcx, def_id),
            callsites,
            loops: Vec::new(),
            block_to_loop: FxHashMap::default(),
            paths: FxHashMap::default(),
        }
    }

    /// Run loop detection and path extraction, then return the collected result.
    pub fn run(mut self) -> PathResult<'tcx> {
        self.find_loops();
        self.find_paths();
        PathResult {
            callsites: self.callsites,
            loops: self.loops,
            paths: self.paths,
        }
    }

    /// Detect loops in the function CFG and store their block-to-loop map.
    fn find_loops(&mut self) {
        let (loops, block_to_loop) = find_loops(&self.cfg);
        self.loops = loops;
        self.block_to_loop = block_to_loop;
    }

    /// Extract paths for every callsite owned by this extractor.
    fn find_paths(&mut self) {
        let by_block = self.callsites_by_block();
        for index in 0..self.callsites.len() {
            let callsite = self.callsites[index].clone();
            let paths = self.find_paths_for_callsite(&callsite, &by_block);
            self.paths.insert(callsite.location(), paths);
        }
    }

    /// Build a map from callsite basic blocks to their stable locations.
    fn callsites_by_block(&self) -> FxHashMap<BasicBlock, CallsiteLocation> {
        self.callsites
            .iter()
            .map(|callsite| (callsite.block, callsite.location()))
            .collect()
    }

    /// Extract paths for one callsite according to whether it is inside a loop.
    fn find_paths_for_callsite(
        &self,
        callsite: &Callsite<'tcx>,
        by_block: &FxHashMap<BasicBlock, CallsiteLocation>,
    ) -> Vec<Path> {
        let target = callsite.location();
        if let Some(loop_id) = self.block_to_loop.get(&callsite.block).copied() {
            self.find_loop_paths(loop_id, target, callsite.block)
        } else {
            self.find_entry_paths(target, callsite.block, by_block)
        }
    }

    /// Enumerate finite paths from function entry to a callsite outside loops.
    ///
    /// The search does not expand loop bodies.  When a successor enters a loop
    /// that does not contain the target callsite, the path records one loop-exit
    /// step and continues from the exit destination.
    fn find_entry_paths(
        &self,
        target: CallsiteLocation,
        target_block: BasicBlock,
        by_block: &FxHashMap<BasicBlock, CallsiteLocation>,
    ) -> Vec<Path> {
        const PATH_LIMIT: usize = 1024;
        let mut results = Vec::new();
        let mut stack = vec![PathStep::Block(self.cfg.entry)];
        let mut visited = FxHashSet::default();
        visited.insert(self.cfg.entry);
        self.dfs_entry_paths(
            self.cfg.entry,
            target,
            target_block,
            by_block,
            &mut visited,
            &mut stack,
            &mut results,
            PATH_LIMIT,
        );
        results
    }

    /// Search from the current block to an outside-loop target callsite.
    ///
    /// Normal blocks are recorded directly.  Entering a loop records a
    /// `PathStep::LoopExit` for each loop exit rather than visiting the loop
    /// body, which keeps the produced paths finite.
    fn dfs_entry_paths(
        &self,
        current: BasicBlock,
        target: CallsiteLocation,
        target_block: BasicBlock,
        by_block: &FxHashMap<BasicBlock, CallsiteLocation>,
        visited: &mut FxHashSet<BasicBlock>,
        stack: &mut Vec<PathStep>,
        results: &mut Vec<Path>,
        limit: usize,
    ) {
        if results.len() >= limit {
            return;
        }

        if current == target_block {
            stack.push(PathStep::Callsite(target));
            results.push(Path {
                target,
                start: PathStart::FunctionEntry,
                steps: stack.clone(),
            });
            stack.pop();
            return;
        }

        for &next in self.cfg.successors(current) {
            if results.len() >= limit {
                break;
            }

            if let Some(loop_id) = self.block_to_loop.get(&next).copied() {
                if self.block_to_loop.get(&target_block).copied() == Some(loop_id) {
                    continue;
                }
                self.follow_loop_exits(
                    loop_id,
                    target,
                    target_block,
                    by_block,
                    visited,
                    stack,
                    results,
                    limit,
                );
                continue;
            }

            if visited.contains(&next) || has_other_callsite(next, target, by_block) {
                continue;
            }

            stack.push(PathStep::Block(next));
            visited.insert(next);
            self.dfs_entry_paths(
                next,
                target,
                target_block,
                by_block,
                visited,
                stack,
                results,
                limit,
            );
            visited.remove(&next);
            stack.pop();
        }
    }

    /// Continue an entry path through every exit of a loop.
    ///
    /// This routine is used only when the target callsite is outside the loop.
    /// It records the selected exit and resumes the DFS at the exit destination.
    fn follow_loop_exits(
        &self,
        loop_id: LoopId,
        target: CallsiteLocation,
        target_block: BasicBlock,
        by_block: &FxHashMap<BasicBlock, CallsiteLocation>,
        visited: &mut FxHashSet<BasicBlock>,
        stack: &mut Vec<PathStep>,
        results: &mut Vec<Path>,
        limit: usize,
    ) {
        let loop_info = &self.loops[loop_id.index()];
        for exit in &loop_info.exits {
            if results.len() >= limit {
                break;
            }
            if visited.contains(&exit.to) {
                continue;
            }

            stack.push(PathStep::LoopExit {
                loop_id,
                from: exit.from,
                to: exit.to,
            });
            stack.push(PathStep::Block(exit.to));
            visited.insert(exit.to);
            self.dfs_entry_paths(
                exit.to,
                target,
                target_block,
                by_block,
                visited,
                stack,
                results,
                limit,
            );
            visited.remove(&exit.to);
            stack.pop();
            stack.pop();
        }
    }

    /// Enumerate paths from a loop header to a callsite inside that loop.
    ///
    /// These paths represent one possible iteration reaching the callsite.  The
    /// number of earlier iterations is intentionally not encoded in the path;
    /// later verification stages should use loop facts to describe the header
    /// state.
    fn find_loop_paths(
        &self,
        loop_id: LoopId,
        target: CallsiteLocation,
        target_block: BasicBlock,
    ) -> Vec<Path> {
        const PATH_LIMIT: usize = 1024;
        let loop_info = &self.loops[loop_id.index()];
        let loop_blocks: FxHashSet<BasicBlock> = loop_info.blocks.iter().copied().collect();
        let mut results = Vec::new();
        let mut stack = vec![PathStep::Block(loop_info.header)];
        let mut visited = FxHashSet::default();
        visited.insert(loop_info.header);
        self.dfs_loop_paths(
            loop_id,
            loop_info.header,
            target,
            target_block,
            &loop_blocks,
            &mut visited,
            &mut stack,
            &mut results,
            PATH_LIMIT,
        );
        results
    }

    /// Search inside one loop from its header to an internal callsite.
    ///
    /// Successors that leave the loop are ignored because outside-loop paths are
    /// represented by loop exits.  This search only describes how an iteration
    /// reaches a callsite located in the loop body.
    fn dfs_loop_paths(
        &self,
        loop_id: LoopId,
        current: BasicBlock,
        target: CallsiteLocation,
        target_block: BasicBlock,
        loop_blocks: &FxHashSet<BasicBlock>,
        visited: &mut FxHashSet<BasicBlock>,
        stack: &mut Vec<PathStep>,
        results: &mut Vec<Path>,
        limit: usize,
    ) {
        if results.len() >= limit {
            return;
        }

        if current == target_block {
            stack.push(PathStep::Callsite(target));
            results.push(Path {
                target,
                start: PathStart::LoopHeader { loop_id },
                steps: stack.clone(),
            });
            stack.pop();
            return;
        }

        for &next in self.cfg.successors(current) {
            if !loop_blocks.contains(&next) || visited.contains(&next) {
                continue;
            }
            stack.push(PathStep::Block(next));
            visited.insert(next);
            self.dfs_loop_paths(
                loop_id,
                next,
                target,
                target_block,
                loop_blocks,
                visited,
                stack,
                results,
                limit,
            );
            visited.remove(&next);
            stack.pop();
        }
    }
}

/// Result produced by a completed path extraction run.
pub struct PathResult<'tcx> {
    callsites: Vec<Callsite<'tcx>>,
    loops: Vec<LoopInfo>,
    paths: FxHashMap<CallsiteLocation, Vec<Path>>,
}

impl<'tcx> PathResult<'tcx> {
    /// Return all callsites used during path extraction.
    pub fn callsites(&self) -> &[Callsite<'tcx>] {
        &self.callsites
    }

    /// Return all loops detected in the function CFG.
    pub fn loops(&self) -> &[LoopInfo] {
        &self.loops
    }

    /// Return the paths extracted for one callsite location.
    pub fn paths_for(&self, location: CallsiteLocation) -> &[Path] {
        self.paths.get(&location).map(Vec::as_slice).unwrap_or(&[])
    }
}

/// A finite verification path reaching one callsite.
#[derive(Clone, Debug)]
pub struct Path {
    /// Callsite reached by this path.
    pub target: CallsiteLocation,
    /// Where the path starts.
    pub start: PathStart,
    /// Ordered steps from the start point to the target callsite.
    pub steps: Vec<PathStep>,
}

impl Path {
    /// Render this path as a compact string for diagnostics.
    pub fn describe(&self) -> String {
        self.steps
            .iter()
            .map(|step| match step {
                PathStep::Block(bb) => format!("bb{}", bb.as_usize()),
                PathStep::LoopExit { loop_id, from, to } => {
                    format!(
                        "Loop#{}.exit(bb{} -> bb{})",
                        loop_id.index(),
                        from.as_usize(),
                        to.as_usize()
                    )
                }
                PathStep::Callsite(location) => {
                    format!("callsite(bb{})", location.block.as_usize())
                }
            })
            .collect::<Vec<_>>()
            .join(" -> ")
    }
}

/// Start point for a finite verification path.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PathStart {
    /// The path starts at the function entry block.
    FunctionEntry,
    /// The path starts at the header of a loop containing the target callsite.
    LoopHeader { loop_id: LoopId },
}

/// One step in a finite verification path.
#[derive(Clone, Debug)]
pub enum PathStep {
    /// A normal MIR basic block.
    Block(BasicBlock),
    /// An abstract step that enters a loop and leaves through one exit edge.
    LoopExit {
        loop_id: LoopId,
        from: BasicBlock,
        to: BasicBlock,
    },
    /// The target callsite that terminates the path.
    Callsite(CallsiteLocation),
}

/// Identifier for a detected loop in one function body.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct LoopId(usize);

impl LoopId {
    /// Create a loop id from its index in the local loop list.
    fn new(index: usize) -> Self {
        Self(index)
    }

    /// Return the index of this loop id in the local loop list.
    pub fn index(self) -> usize {
        self.0
    }
}

impl fmt::Display for LoopId {
    /// Format a loop id as its numeric index.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// Information recorded for one detected loop.
#[derive(Clone, Debug)]
pub struct LoopInfo {
    /// Local id of this loop.
    pub id: LoopId,
    /// Header block chosen for this loop.
    pub header: BasicBlock,
    /// Blocks that belong to the loop.
    pub blocks: Vec<BasicBlock>,
    /// Edges that leave the loop.
    pub exits: Vec<LoopExit>,
    /// Edges inside the loop that go back to an earlier block or the header.
    pub backedges: Vec<(BasicBlock, BasicBlock)>,
    /// Current summary status for the loop.
    pub transfer: LoopTransfer,
}

/// An edge that leaves a detected loop.
#[derive(Clone, Debug)]
pub struct LoopExit {
    /// Source block inside the loop.
    pub from: BasicBlock,
    /// Destination block outside the loop.
    pub to: BasicBlock,
}

/// Conservative summary status for a loop.
#[derive(Clone, Debug)]
pub enum LoopTransfer {
    /// The loop has not yet been classified by later verification stages.
    Unknown,
    /// The loop can be ignored for the current obligation.
    Skip,
    /// The loop may modify relevant state without a precise summary.
    Havoc,
}

/// Return true when `block` contains a non-target callsite.
fn has_other_callsite(
    block: BasicBlock,
    target: CallsiteLocation,
    by_block: &FxHashMap<BasicBlock, CallsiteLocation>,
) -> bool {
    by_block
        .get(&block)
        .map(|location| *location != target)
        .unwrap_or(false)
}

/// Detect loops in a CFG using SCCs.
fn find_loops(cfg: &CFG) -> (Vec<LoopInfo>, FxHashMap<BasicBlock, LoopId>) {
    let mut detector = SccDetector::new(cfg.successors.clone());
    detector.find_scc();

    let mut loops = Vec::new();
    let mut block_to_loop = FxHashMap::default();
    for mut component in detector.components {
        component.sort_unstable();
        let is_self_loop = component.len() == 1
            && cfg.successors[component[0]]
                .iter()
                .any(|succ| succ.as_usize() == component[0]);
        if component.len() <= 1 && !is_self_loop {
            continue;
        }

        let id = LoopId::new(loops.len());
        let header = BasicBlock::from_usize(component[0]);
        let block_set: FxHashSet<usize> = component.iter().copied().collect();
        let mut exits = Vec::new();
        let mut backedges = Vec::new();

        for &block_idx in &component {
            let block = BasicBlock::from_usize(block_idx);
            for &succ in cfg.successors(block) {
                let succ_idx = succ.as_usize();
                if block_set.contains(&succ_idx) {
                    if succ_idx <= block_idx || succ == header {
                        backedges.push((block, succ));
                    }
                } else {
                    exits.push(LoopExit {
                        from: block,
                        to: succ,
                    });
                }
            }
        }

        for &block_idx in &component {
            block_to_loop.insert(BasicBlock::from_usize(block_idx), id);
        }

        loops.push(LoopInfo {
            id,
            header,
            blocks: component.into_iter().map(BasicBlock::from_usize).collect(),
            exits,
            backedges,
            transfer: LoopTransfer::Unknown,
        });
    }

    (loops, block_to_loop)
}

/// Adapter that lets the shared SCC utility run over a MIR CFG.
struct SccDetector {
    successors: Vec<Vec<BasicBlock>>,
    components: Vec<Vec<usize>>,
}

impl SccDetector {
    /// Create an SCC detector over a concrete successor list.
    fn new(successors: Vec<Vec<BasicBlock>>) -> Self {
        Self {
            successors,
            components: Vec::new(),
        }
    }
}

impl Scc for SccDetector {
    /// Store every SCC discovered by the shared Tarjan utility.
    fn on_scc_found(&mut self, _root: usize, scc_components: &[usize]) {
        self.components.push(scc_components.to_vec());
    }

    /// Return outgoing successor indices for the SCC traversal.
    fn get_next(&mut self, root: usize) -> FxHashSet<usize> {
        self.successors
            .get(root)
            .into_iter()
            .flat_map(|successors| successors.iter().map(|bb| bb.as_usize()))
            .collect()
    }

    /// Return the number of CFG nodes in the detector graph.
    fn get_size(&mut self) -> usize {
        self.successors.len()
    }
}
