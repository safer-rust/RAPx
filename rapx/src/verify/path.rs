//! Loop-aware MIR path extraction for verification targets.
//!
//! The extractor builds a finite path skeleton for each unsafe callsite.  Loops
//! are represented by abstract exit-port items when the callsite is outside the
//! loop, and by header-to-callsite intra-loop paths when the callsite is inside
//! the loop.  Later stages can attach evidence reduction and SMT semantics to
//! these skeletons.

use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{BasicBlock, TerminatorKind, UnwindAction},
    ty::TyCtxt,
};

use crate::utils::scc::Scc;

use super::callsite::UnsafeCallsite;

/// Identifier for an unsafe callsite within one function body.
pub type UnsafeCallsiteId = usize;

/// Identifier for a loop node within one function body.
pub type LoopId = usize;

/// A compact MIR CFG used by the verifier path extractor.
#[derive(Clone, Debug)]
pub struct MirCfg {
    pub def_id: DefId,
    pub entry: BasicBlock,
    pub successors: Vec<Vec<BasicBlock>>,
}

impl MirCfg {
    /// Build a successor graph from optimized MIR.
    pub fn new(tcx: TyCtxt<'_>, def_id: DefId) -> Self {
        let body = tcx.optimized_mir(def_id);
        let successors = body
            .basic_blocks
            .iter()
            .map(|block| terminator_successors(&block.terminator().kind))
            .collect();
        Self {
            def_id,
            entry: BasicBlock::from_usize(0),
            successors,
        }
    }

    /// Return successors of a block.
    pub fn successors(&self, block: BasicBlock) -> &[BasicBlock] {
        self.successors
            .get(block.as_usize())
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }

    /// Return the number of basic blocks.
    pub fn len(&self) -> usize {
        self.successors.len()
    }
}

/// A loop exit edge exposed as a path-class port.
#[derive(Clone, Debug)]
pub struct LoopExit {
    pub from: BasicBlock,
    pub to: BasicBlock,
}

/// A conservative loop transfer placeholder.
#[derive(Clone, Debug)]
pub enum LoopTransfer {
    /// The loop is irrelevant to the current obligation.
    Skip,
    /// The loop modifies relevant state and no summary is currently available.
    Havoc,
    /// The loop was detected but not yet classified.
    Unknown,
}

/// A loop abstract node in the verifier path graph.
#[derive(Clone, Debug)]
pub struct LoopNode {
    pub id: LoopId,
    pub header: BasicBlock,
    pub body: Vec<BasicBlock>,
    pub exits: Vec<LoopExit>,
    pub backedges: Vec<(BasicBlock, BasicBlock)>,
    pub internal_callsites: Vec<UnsafeCallsiteId>,
    pub transfer: LoopTransfer,
}

/// One item in a finite verification path skeleton.
#[derive(Clone, Debug)]
pub enum PathItem {
    Block(BasicBlock),
    LoopExit {
        loop_id: LoopId,
        from: BasicBlock,
        to: BasicBlock,
    },
    Callsite(UnsafeCallsiteId),
    InternalLoopCallsite {
        loop_id: LoopId,
        callsite: UnsafeCallsiteId,
    },
}

/// Whether a path reaches a callsite from function entry or from a loop header.
#[derive(Clone, Debug)]
pub enum PathKind {
    EntryToCallsite,
    LoopHeaderToCallsite { loop_id: LoopId },
}

/// A finite path skeleton reaching one unsafe callsite.
#[derive(Clone, Debug)]
pub struct VerifyPath {
    pub callsite: UnsafeCallsiteId,
    pub kind: PathKind,
    pub items: Vec<PathItem>,
}

impl VerifyPath {
    /// Render the path skeleton for logging.
    pub fn describe(&self) -> String {
        self.items
            .iter()
            .map(|item| match item {
                PathItem::Block(bb) => format!("bb{}", bb.as_usize()),
                PathItem::LoopExit { loop_id, from, to } => {
                    format!(
                        "Loop#{loop_id}.exit(bb{} -> bb{})",
                        from.as_usize(),
                        to.as_usize()
                    )
                }
                PathItem::Callsite(id) => format!("callsite#{id}"),
                PathItem::InternalLoopCallsite { loop_id, callsite } => {
                    format!("Loop#{loop_id}.callsite#{callsite}")
                }
            })
            .collect::<Vec<_>>()
            .join(" -> ")
    }
}

/// Extract loop-aware path skeletons for a function.
pub struct VerifyPathExtractor {
    cfg: MirCfg,
    loops: Vec<LoopNode>,
    block_to_loop: FxHashMap<usize, LoopId>,
}

impl VerifyPathExtractor {
    /// Create a new extractor for `def_id`.
    pub fn new(tcx: TyCtxt<'_>, def_id: DefId) -> Self {
        let cfg = MirCfg::new(tcx, def_id);
        let (loops, block_to_loop) = detect_loops(&cfg);
        Self {
            cfg,
            loops,
            block_to_loop,
        }
    }

    /// Return detected loop nodes.
    pub fn loops(&self) -> &[LoopNode] {
        &self.loops
    }

    /// Extract paths for each unsafe callsite.
    pub fn extract_paths<'tcx>(&self, callsites: &[UnsafeCallsite<'tcx>]) -> Vec<VerifyPath> {
        let mut by_block: FxHashMap<usize, Vec<UnsafeCallsiteId>> = FxHashMap::default();
        for (id, callsite) in callsites.iter().enumerate() {
            by_block
                .entry(callsite.block.as_usize())
                .or_default()
                .push(id);
        }

        let mut paths = Vec::new();
        for (id, callsite) in callsites.iter().enumerate() {
            if let Some(loop_id) = self.block_to_loop.get(&callsite.block.as_usize()).copied() {
                paths.extend(self.extract_intra_loop_paths(loop_id, id, callsite.block));
            } else {
                paths.extend(self.extract_entry_paths(id, callsite.block, &by_block));
            }
        }
        paths
    }

    /// Enumerate finite entry-to-callsite path skeletons for a callsite outside loops.
    ///
    /// Loop bodies are not expanded here.  If traversal reaches a loop that does
    /// not contain the target callsite, the path is extended through each loop
    /// exit port instead.
    fn extract_entry_paths(
        &self,
        callsite_id: UnsafeCallsiteId,
        target: BasicBlock,
        by_block: &FxHashMap<usize, Vec<UnsafeCallsiteId>>,
    ) -> Vec<VerifyPath> {
        const PATH_LIMIT: usize = 1024;
        let mut results = Vec::new();
        let mut stack = vec![PathItem::Block(self.cfg.entry)];
        let mut visited = FxHashSet::default();
        visited.insert(self.cfg.entry.as_usize());
        self.dfs_entry_paths(
            self.cfg.entry,
            target,
            callsite_id,
            by_block,
            &mut visited,
            &mut stack,
            &mut results,
            PATH_LIMIT,
        );
        results
    }

    /// Depth-first search over the quotient CFG from function entry to a callsite.
    ///
    /// The DFS records normal blocks directly and records loops as `LoopExit`
    /// items.  `visited` keeps the skeleton finite, while `limit` prevents path
    /// explosion in large branchy functions.
    fn dfs_entry_paths(
        &self,
        current: BasicBlock,
        target: BasicBlock,
        callsite_id: UnsafeCallsiteId,
        by_block: &FxHashMap<usize, Vec<UnsafeCallsiteId>>,
        visited: &mut FxHashSet<usize>,
        stack: &mut Vec<PathItem>,
        results: &mut Vec<VerifyPath>,
        limit: usize,
    ) {
        if results.len() >= limit {
            return;
        }
        if current == target {
            stack.push(PathItem::Callsite(callsite_id));
            results.push(VerifyPath {
                callsite: callsite_id,
                kind: PathKind::EntryToCallsite,
                items: stack.clone(),
            });
            stack.pop();
            return;
        }

        let Some(successors) = self.cfg.successors.get(current.as_usize()) else {
            return;
        };

        for &next in successors {
            if results.len() >= limit {
                break;
            }
            if let Some(loop_id) = self.block_to_loop.get(&next.as_usize()).copied() {
                if self.block_to_loop.get(&target.as_usize()).copied() == Some(loop_id) {
                    continue;
                }
                let loop_node = &self.loops[loop_id];
                for exit in &loop_node.exits {
                    if results.len() >= limit {
                        break;
                    }
                    let to_idx = exit.to.as_usize();
                    if visited.contains(&to_idx) {
                        continue;
                    }
                    stack.push(PathItem::LoopExit {
                        loop_id,
                        from: exit.from,
                        to: exit.to,
                    });
                    stack.push(PathItem::Block(exit.to));
                    visited.insert(to_idx);
                    self.dfs_entry_paths(
                        exit.to,
                        target,
                        callsite_id,
                        by_block,
                        visited,
                        stack,
                        results,
                        limit,
                    );
                    visited.remove(&to_idx);
                    stack.pop();
                    stack.pop();
                }
                continue;
            }

            let next_idx = next.as_usize();
            if visited.contains(&next_idx) {
                continue;
            }
            if contains_other_callsite(next, callsite_id, by_block) {
                continue;
            }
            stack.push(PathItem::Block(next));
            visited.insert(next_idx);
            self.dfs_entry_paths(
                next,
                target,
                callsite_id,
                by_block,
                visited,
                stack,
                results,
                limit,
            );
            visited.remove(&next_idx);
            stack.pop();
        }
    }

    /// Enumerate header-to-callsite paths for a callsite located inside a loop.
    ///
    /// The returned paths are one-iteration path classes: they start at the loop
    /// header and stop at the internal unsafe callsite.  Later verification
    /// stages should interpret the path under the loop header context, not under
    /// one concrete number of previous iterations.
    fn extract_intra_loop_paths(
        &self,
        loop_id: LoopId,
        callsite_id: UnsafeCallsiteId,
        target: BasicBlock,
    ) -> Vec<VerifyPath> {
        const PATH_LIMIT: usize = 1024;
        let loop_node = &self.loops[loop_id];
        let body: FxHashSet<usize> = loop_node.body.iter().map(|bb| bb.as_usize()).collect();
        let mut results = Vec::new();
        let mut stack = vec![PathItem::Block(loop_node.header)];
        let mut visited = FxHashSet::default();
        visited.insert(loop_node.header.as_usize());
        self.dfs_intra_loop_paths(
            loop_id,
            loop_node.header,
            target,
            callsite_id,
            &body,
            &mut visited,
            &mut stack,
            &mut results,
            PATH_LIMIT,
        );
        results
    }

    /// Depth-first search restricted to one loop body.
    ///
    /// Successors leaving the loop are ignored because this routine is only for
    /// internal callsites.  Exit-port paths are handled by `dfs_entry_paths`
    /// when the target callsite is outside the loop.
    fn dfs_intra_loop_paths(
        &self,
        loop_id: LoopId,
        current: BasicBlock,
        target: BasicBlock,
        callsite_id: UnsafeCallsiteId,
        body: &FxHashSet<usize>,
        visited: &mut FxHashSet<usize>,
        stack: &mut Vec<PathItem>,
        results: &mut Vec<VerifyPath>,
        limit: usize,
    ) {
        if results.len() >= limit {
            return;
        }
        if current == target {
            stack.push(PathItem::InternalLoopCallsite {
                loop_id,
                callsite: callsite_id,
            });
            results.push(VerifyPath {
                callsite: callsite_id,
                kind: PathKind::LoopHeaderToCallsite { loop_id },
                items: stack.clone(),
            });
            stack.pop();
            return;
        }

        for &next in self.cfg.successors(current) {
            let next_idx = next.as_usize();
            if !body.contains(&next_idx) || visited.contains(&next_idx) {
                continue;
            }
            stack.push(PathItem::Block(next));
            visited.insert(next_idx);
            self.dfs_intra_loop_paths(
                loop_id,
                next,
                target,
                callsite_id,
                body,
                visited,
                stack,
                results,
                limit,
            );
            visited.remove(&next_idx);
            stack.pop();
        }
    }
}

/// Return true when `block` contains another unsafe callsite.
///
/// Entry-to-callsite paths stop at the target callsite.  This helper prevents a
/// path for one callsite from accidentally passing through a different unsafe
/// callsite first, which would blur the verification unit boundary.
fn contains_other_callsite(
    block: BasicBlock,
    target_callsite: UnsafeCallsiteId,
    by_block: &FxHashMap<usize, Vec<UnsafeCallsiteId>>,
) -> bool {
    by_block
        .get(&block.as_usize())
        .map(|ids| ids.iter().any(|id| *id != target_callsite))
        .unwrap_or(false)
}

/// Detect MIR loops using SCCs and expose them as `LoopNode`s.
///
/// A component is treated as a loop when it contains more than one block or a
/// single block with a self-edge.  The returned map associates each loop body
/// block with the corresponding loop id, allowing path construction to replace
/// loop bodies with abstract exit-port items.
fn detect_loops(cfg: &MirCfg) -> (Vec<LoopNode>, FxHashMap<usize, LoopId>) {
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

        let id = loops.len();
        let header = BasicBlock::from_usize(component[0]);
        let body_set: FxHashSet<usize> = component.iter().copied().collect();
        let mut exits = Vec::new();
        let mut backedges = Vec::new();

        for &block_idx in &component {
            let block = BasicBlock::from_usize(block_idx);
            for &succ in cfg.successors(block) {
                let succ_idx = succ.as_usize();
                if body_set.contains(&succ_idx) {
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
            block_to_loop.insert(block_idx, id);
        }

        loops.push(LoopNode {
            id,
            header,
            body: component.into_iter().map(BasicBlock::from_usize).collect(),
            exits,
            backedges,
            internal_callsites: Vec::new(),
            transfer: LoopTransfer::Unknown,
        });
    }

    (loops, block_to_loop)
}

/// Compute MIR successor blocks for one terminator.
///
/// The extractor includes normal successors and cleanup successors so the
/// skeleton reflects all CFG edges that can affect reachability.  Later phases
/// may decide whether a cleanup path is relevant to a particular obligation.
fn terminator_successors(kind: &TerminatorKind<'_>) -> Vec<BasicBlock> {
    let mut successors = Vec::new();
    match kind {
        TerminatorKind::Goto { target } => successors.push(*target),
        TerminatorKind::SwitchInt { targets, .. } => {
            successors.extend(targets.all_targets().iter().copied());
        }
        TerminatorKind::Drop { target, unwind, .. }
        | TerminatorKind::Assert { target, unwind, .. } => {
            successors.push(*target);
            push_unwind_target(unwind, &mut successors);
        }
        TerminatorKind::Call { target, unwind, .. } => {
            if let Some(target) = target {
                successors.push(*target);
            }
            push_unwind_target(unwind, &mut successors);
        }
        TerminatorKind::Yield { resume, drop, .. } => {
            successors.push(*resume);
            if let Some(drop) = drop {
                successors.push(*drop);
            }
        }
        TerminatorKind::FalseEdge { real_target, .. } => successors.push(*real_target),
        TerminatorKind::FalseUnwind {
            real_target,
            unwind,
        } => {
            successors.push(*real_target);
            push_unwind_target(unwind, &mut successors);
        }
        TerminatorKind::InlineAsm {
            targets, unwind, ..
        } => {
            successors.extend(targets.iter().copied());
            push_unwind_target(unwind, &mut successors);
        }
        TerminatorKind::Return
        | TerminatorKind::Unreachable
        | TerminatorKind::UnwindResume
        | TerminatorKind::UnwindTerminate(_)
        | TerminatorKind::CoroutineDrop
        | TerminatorKind::TailCall { .. } => {}
    }
    successors.sort_unstable_by_key(|bb| bb.as_usize());
    successors.dedup();
    successors
}

/// Append a cleanup unwind target when one exists.
fn push_unwind_target(unwind: &UnwindAction, successors: &mut Vec<BasicBlock>) {
    if let UnwindAction::Cleanup(target) = unwind {
        successors.push(*target);
    }
}

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
