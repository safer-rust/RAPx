//! Path extraction for verification targets.
//!
//! This module builds finite paths from a function CFG to each unsafe callsite.
//! Cyclic SCC regions are kept finite by treating an SCC as a single step through
//! one of its exits when the target callsite is outside that SCC. If the target
//! callsite is inside an SCC, the path records both the entry-to-representative prefix and the
//! representative-to-callsite body path. This preserves facts established before the
//! SCC region without unrolling cyclic control flow.

use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def_id::DefId;
use rustc_middle::{mir::BasicBlock, ty::TyCtxt};

use crate::graphs::scc::collect_scc_components;

use super::helpers::{CFG, Callsite, CallsiteLocation};

const PATH_LIMIT: usize = 1024;

/// Extracts SCC-aware paths for one function body.
pub struct PathExtractor<'tcx> {
    cfg: CFG,
    callsites: Vec<Callsite<'tcx>>,
    scc_regions: Vec<SccRegion>,
    block_to_scc: FxHashMap<BasicBlock, BasicBlock>,
    paths: FxHashMap<CallsiteLocation, Vec<Path>>,
}

impl<'tcx> PathExtractor<'tcx> {
    /// Create a path extractor for `def_id` and the callsites found in that body.
    pub fn new(tcx: TyCtxt<'tcx>, def_id: DefId, callsites: Vec<Callsite<'tcx>>) -> Self {
        Self {
            cfg: CFG::new(tcx, def_id),
            callsites,
            scc_regions: Vec::new(),
            block_to_scc: FxHashMap::default(),
            paths: FxHashMap::default(),
        }
    }

    /// Run SCC-region detection and path extraction, then return path metadata.
    pub fn run(mut self) -> FunctionPaths<'tcx> {
        self.find_scc_regions();
        self.find_paths();
        FunctionPaths {
            scc_regions: SccRegions::new(self.scc_regions),
            callsite_paths: CallsitePaths::new(self.callsites, self.paths),
        }
    }

    /// Detect SCC regions in the function CFG and store their block-to-SCC map.
    fn find_scc_regions(&mut self) {
        let (scc_regions, block_to_scc) = find_scc_regions(&self.cfg);
        self.scc_regions = scc_regions;
        self.block_to_scc = block_to_scc;
    }

    /// Extract paths for every callsite owned by this extractor.
    fn find_paths(&mut self) {
        for index in 0..self.callsites.len() {
            let callsite = self.callsites[index].clone();
            let paths = self.find_paths_for_callsite(&callsite);
            self.paths.insert(callsite.location(), paths);
        }
    }

    /// Extract paths for one callsite according to whether it is inside an SCC region.
    fn find_paths_for_callsite(&self, callsite: &Callsite<'tcx>) -> Vec<Path> {
        let target = callsite.location();
        if let Some(representative) = self.block_to_scc.get(&callsite.block).copied() {
            self.find_scc_internal_paths(representative, target, callsite.block)
        } else {
            self.find_entry_paths(target, callsite.block)
        }
    }

    /// Enumerate finite paths from function entry to a callsite outside SCC regions.
    ///
    /// The search does not expand SCC internals. When a successor enters an SCC
    /// that does not contain the target callsite, the path records one SCC-exit
    /// step and continues from the exit destination.
    fn find_entry_paths(&self, target: CallsiteLocation, target_block: BasicBlock) -> Vec<Path> {
        let mut results = Vec::new();
        let mut stack = vec![PathStep::Block(self.cfg.entry)];
        let mut visited = FxHashSet::default();
        visited.insert(self.cfg.entry);
        self.dfs_entry_paths(
            self.cfg.entry,
            target,
            target_block,
            &mut visited,
            &mut stack,
            &mut results,
            PATH_LIMIT,
        );
        results
    }

    /// Search from the current block to an outside-SCC target callsite.
    ///
    /// Normal blocks are recorded directly. Entering an SCC records a
    /// `PathStep::SccExit` for each SCC exit rather than visiting SCC-internal
    /// blocks, which keeps the produced paths finite.
    fn dfs_entry_paths(
        &self,
        current: BasicBlock,
        target: CallsiteLocation,
        target_block: BasicBlock,
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
                entry_prefix: Vec::new(),
                steps: stack.clone(),
            });
            stack.pop();
            return;
        }

        for &next in self.cfg.successors(current) {
            if results.len() >= limit {
                break;
            }

            if let Some(representative) = self.block_to_scc.get(&next).copied() {
                if self.block_to_scc.get(&target_block).copied() == Some(representative) {
                    continue;
                }
                self.follow_scc_exits(
                    representative,
                    target,
                    target_block,
                    visited,
                    stack,
                    results,
                    limit,
                );
                continue;
            }

            if visited.contains(&next) {
                continue;
            }

            stack.push(PathStep::Block(next));
            visited.insert(next);
            self.dfs_entry_paths(
                next,
                target,
                target_block,
                visited,
                stack,
                results,
                limit,
            );
            visited.remove(&next);
            stack.pop();
        }
    }

    /// Continue an entry path through every exit of an SCC region.
    ///
    /// This routine is used only when the target callsite is outside the SCC region.
    /// It records the selected exit and resumes the DFS at the exit destination.
    fn follow_scc_exits(
        &self,
        representative: BasicBlock,
        target: CallsiteLocation,
        target_block: BasicBlock,
        visited: &mut FxHashSet<BasicBlock>,
        stack: &mut Vec<PathStep>,
        results: &mut Vec<Path>,
        limit: usize,
    ) {
        let Some(scc_info) = self.scc_by_representative(representative) else {
            return;
        };
        for exit in &scc_info.exits {
            if results.len() >= limit {
                break;
            }
            if visited.contains(&exit.to) {
                continue;
            }

            stack.push(PathStep::SccExit {
                representative,
                from: exit.from,
                to: exit.to,
            });
            stack.push(PathStep::Block(exit.to));
            visited.insert(exit.to);
            self.dfs_entry_paths(
                exit.to,
                target,
                target_block,
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

    /// Enumerate paths from an SCC representative to a callsite inside that SCC.
    ///
    /// These paths represent one possible iteration reaching the callsite.  The
    /// number of earlier iterations is intentionally not encoded in the path;
    /// later verification stages should use SCC facts to describe the representative
    /// state.
    fn find_scc_internal_paths(
        &self,
        representative: BasicBlock,
        target: CallsiteLocation,
        target_block: BasicBlock,
    ) -> Vec<Path> {
        let Some(scc_info) = self.scc_by_representative(representative) else {
            return Vec::new();
        };
        let scc_blocks: FxHashSet<BasicBlock> = scc_info.blocks.iter().copied().collect();
        let entry_prefixes = self.find_entry_prefixes(representative, PATH_LIMIT);
        let mut results = Vec::new();
        let mut stack = vec![PathStep::Block(scc_info.representative)];
        let mut visited = FxHashSet::default();
        visited.insert(scc_info.representative);
        self.dfs_scc_internal_paths(
            representative,
            scc_info.representative,
            target,
            target_block,
            &scc_blocks,
            &entry_prefixes,
            &mut visited,
            &mut stack,
            &mut results,
            PATH_LIMIT,
        );
        results
    }

    /// Enumerate finite entry-to-representative prefixes for an SCC-internal callsite.
    ///
    /// SCC-internal paths still need facts established before the first iteration
    /// such as `ptr = slice.as_ptr()`. The returned prefix excludes
    /// `representative` itself because the SCC-internal body path already starts there.
    fn find_entry_prefixes(&self, representative: BasicBlock, limit: usize) -> Vec<Vec<PathStep>> {
        if self.cfg.entry == representative {
            return vec![Vec::new()];
        }

        let mut results = Vec::new();
        let mut stack = vec![PathStep::Block(self.cfg.entry)];
        let mut visited = FxHashSet::default();
        visited.insert(self.cfg.entry);
        self.dfs_entry_prefixes(
            self.cfg.entry,
            representative,
            &mut visited,
            &mut stack,
            &mut results,
            limit,
        );

        if results.is_empty() {
            vec![Vec::new()]
        } else {
            results
        }
    }

    /// Search from function entry to the selected SCC representative.
    ///
    /// Other SCC regions are crossed through their exits, but the target SCC itself
    /// is not expanded. This keeps the prefix finite while preserving pre-SCC
    /// definitions that the SCC-internal path may use.
    fn dfs_entry_prefixes(
        &self,
        current: BasicBlock,
        representative: BasicBlock,
        visited: &mut FxHashSet<BasicBlock>,
        stack: &mut Vec<PathStep>,
        results: &mut Vec<Vec<PathStep>>,
        limit: usize,
    ) {
        if results.len() >= limit {
            return;
        }

        for &next in self.cfg.successors(current) {
            if results.len() >= limit {
                break;
            }

            if next == representative {
                results.push(stack.clone());
                continue;
            }

            if let Some(scc_representative) = self.block_to_scc.get(&next).copied() {
                if scc_representative == representative {
                    continue;
                }
                self.follow_scc_exits_for_prefix(
                    scc_representative,
                    representative,
                    visited,
                    stack,
                    results,
                    limit,
                );
                continue;
            }

            if visited.contains(&next) {
                continue;
            }

            stack.push(PathStep::Block(next));
            visited.insert(next);
            self.dfs_entry_prefixes(next, representative, visited, stack, results, limit);
            visited.remove(&next);
            stack.pop();
        }
    }

    /// Continue an entry prefix through every exit of an unrelated SCC region.
    fn follow_scc_exits_for_prefix(
        &self,
        scc_representative: BasicBlock,
        target_representative: BasicBlock,
        visited: &mut FxHashSet<BasicBlock>,
        stack: &mut Vec<PathStep>,
        results: &mut Vec<Vec<PathStep>>,
        limit: usize,
    ) {
        let Some(scc_info) = self.scc_by_representative(scc_representative) else {
            return;
        };
        for exit in &scc_info.exits {
            if results.len() >= limit {
                break;
            }
            if visited.contains(&exit.to) {
                continue;
            }

            stack.push(PathStep::SccExit {
                representative: scc_representative,
                from: exit.from,
                to: exit.to,
            });
            stack.push(PathStep::Block(exit.to));
            visited.insert(exit.to);
            self.dfs_entry_prefixes(
                exit.to,
                target_representative,
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

    /// Search inside one SCC region from its representative to an internal callsite.
    ///
    /// Successors that leave the SCC are ignored because outside-SCC paths are
    /// represented by SCC exits. This search only describes how one iteration
    /// reaches a callsite located in the SCC region.
    fn dfs_scc_internal_paths(
        &self,
        representative: BasicBlock,
        current: BasicBlock,
        target: CallsiteLocation,
        target_block: BasicBlock,
        scc_blocks: &FxHashSet<BasicBlock>,
        entry_prefixes: &[Vec<PathStep>],
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
            for entry_prefix in entry_prefixes {
                results.push(Path {
                    target,
                    start: PathStart::SccRepresentative { representative },
                    entry_prefix: entry_prefix.clone(),
                    steps: stack.clone(),
                });
                if results.len() >= limit {
                    break;
                }
            }
            stack.pop();
            return;
        }

        for &next in self.cfg.successors(current) {
            if !scc_blocks.contains(&next) || visited.contains(&next) {
                continue;
            }
            stack.push(PathStep::Block(next));
            visited.insert(next);
            self.dfs_scc_internal_paths(
                representative,
                next,
                target,
                target_block,
                scc_blocks,
                entry_prefixes,
                visited,
                stack,
                results,
                limit,
            );
            visited.remove(&next);
            stack.pop();
        }
    }

    /// Return the detected SCC region whose representative is `representative`.
    fn scc_by_representative(&self, representative: BasicBlock) -> Option<&SccRegion> {
        self.scc_regions
            .iter()
            .find(|scc_info| scc_info.representative == representative)
    }
}

/// Path metadata produced by a completed extraction run.
///
/// This is the path-level view of a function CFG: SCC-region information describes
/// cyclic regions, while callsite path information maps unsafe callsites to the
/// finite paths that reach them.
pub struct FunctionPaths<'tcx> {
    scc_regions: SccRegions,
    callsite_paths: CallsitePaths<'tcx>,
}

impl<'tcx> FunctionPaths<'tcx> {
    /// Return SCC-region metadata for this function.
    pub fn scc_info(&self) -> &SccRegions {
        &self.scc_regions
    }

    /// Return callsite-to-path metadata for this function.
    pub fn callsite_paths(&self) -> &CallsitePaths<'tcx> {
        &self.callsite_paths
    }

    /// Return all callsites used during path extraction.
    pub fn callsites(&self) -> &[Callsite<'tcx>] {
        self.callsite_paths.callsites()
    }

    /// Return all SCC regions detected in the function CFG.
    pub fn scc_regions(&self) -> &[SccRegion] {
        self.scc_regions.scc_regions()
    }

    /// Return the paths extracted for one callsite location.
    pub fn paths_for(&self, location: CallsiteLocation) -> &[Path] {
        self.callsite_paths.paths_for(location)
    }
}

/// Metadata for SCC regions discovered in a function CFG.
pub struct SccRegions {
    scc_regions: Vec<SccRegion>,
}

impl SccRegions {
    /// Create SCC-region metadata from detected SCC regions.
    fn new(scc_regions: Vec<SccRegion>) -> Self {
        Self { scc_regions }
    }

    /// Return all detected SCC regions.
    pub fn scc_regions(&self) -> &[SccRegion] {
        &self.scc_regions
    }

    /// Return the number of detected SCC regions.
    pub fn len(&self) -> usize {
        self.scc_regions.len()
    }

    /// Return true when no SCC regions were detected.
    pub fn is_empty(&self) -> bool {
        self.scc_regions.is_empty()
    }
}

/// Metadata that maps unsafe callsites to finite verification paths.
pub struct CallsitePaths<'tcx> {
    callsites: Vec<Callsite<'tcx>>,
    paths_by_callsite: FxHashMap<CallsiteLocation, Vec<Path>>,
}

impl<'tcx> CallsitePaths<'tcx> {
    /// Create callsite path metadata from callsites and extracted paths.
    fn new(
        callsites: Vec<Callsite<'tcx>>,
        paths_by_callsite: FxHashMap<CallsiteLocation, Vec<Path>>,
    ) -> Self {
        Self {
            callsites,
            paths_by_callsite,
        }
    }

    /// Return all callsites used during path extraction.
    pub fn callsites(&self) -> &[Callsite<'tcx>] {
        &self.callsites
    }

    /// Return the paths extracted for one callsite location.
    pub fn paths_for(&self, location: CallsiteLocation) -> &[Path] {
        self.paths_by_callsite
            .get(&location)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }
}

/// A finite verification path reaching one callsite.
#[derive(Clone, Debug)]
pub struct Path {
    /// Callsite reached by this path.
    pub target: CallsiteLocation,
    /// Where the path starts.
    pub start: PathStart,
    /// Blocks and SCC exits from function entry to this path's start.
    ///
    /// This is currently non-empty for SCC-internal callsites. It preserves
    /// definitions established before the SCC representative without unrolling
    /// SCC-internal control flow.
    pub entry_prefix: Vec<PathStep>,
    /// Ordered steps from the start point to the target callsite.
    pub steps: Vec<PathStep>,
}

impl Path {
    /// Render this path as a compact string for diagnostics.
    pub fn describe(&self) -> String {
        let body = self
            .steps
            .iter()
            .map(describe_step)
            .collect::<Vec<_>>()
            .join(" -> ");

        if self.entry_prefix.is_empty() {
            return body;
        }

        format!("entry: {} | body: {}", self.describe_entry_prefix(), body)
    }

    /// Render the entry prefix and append the SCC representative when applicable.
    pub fn describe_entry_prefix(&self) -> String {
        let mut parts = self
            .entry_prefix
            .iter()
            .map(describe_step)
            .collect::<Vec<_>>();
        if let PathStart::SccRepresentative { representative } = self.start {
            parts.push(format!("bb{}", representative.as_usize()));
        }
        parts.join(" -> ")
    }

    /// Render only the path body from the start point to the callsite.
    pub fn describe_body(&self) -> String {
        self.steps
            .iter()
            .map(describe_step)
            .collect::<Vec<_>>()
            .join(" -> ")
    }
}

/// Render one path step.
fn describe_step(step: &PathStep) -> String {
    match step {
        PathStep::Block(bb) => format!("bb{}", bb.as_usize()),
        PathStep::SccExit {
            representative,
            from,
            to,
        } => {
            format!(
                "SccRegion(bb{}).exit(bb{} -> bb{})",
                representative.as_usize(),
                from.as_usize(),
                to.as_usize()
            )
        }
        PathStep::Callsite(location) => {
            format!("callsite(bb{})", location.block.as_usize())
        }
    }
}

/// Start point for a finite verification path.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PathStart {
    /// The path starts at the function entry block.
    FunctionEntry,
    /// The path starts at the representative of an SCC containing the target callsite.
    SccRepresentative { representative: BasicBlock },
}

/// One step in a finite verification path.
#[derive(Clone, Debug)]
pub enum PathStep {
    /// A normal MIR basic block.
    Block(BasicBlock),
    /// An abstract step that enters an SCC and leaves through one exit edge.
    SccExit {
        representative: BasicBlock,
        from: BasicBlock,
        to: BasicBlock,
    },
    /// The target callsite that terminates the path.
    Callsite(CallsiteLocation),
}

/// A cyclic SCC region used as one finite-path abstraction unit.
#[derive(Clone, Debug)]
pub struct SccRegion {
    /// Stable representative block used as the key for this SCC region.
    pub representative: BasicBlock,
    /// Blocks that belong to the SCC region.
    pub blocks: Vec<BasicBlock>,
    /// Edges that leave the SCC region.
    pub exits: Vec<SccExit>,
    /// Edges inside the SCC region that go back to an earlier block or the representative.
    pub backedges: Vec<(BasicBlock, BasicBlock)>,
}

/// An edge that leaves a detected SCC region.
#[derive(Clone, Debug)]
pub struct SccExit {
    /// Source block inside the SCC region.
    pub from: BasicBlock,
    /// Destination block outside the SCC region.
    pub to: BasicBlock,
}

/// Detect cyclic SCC regions in a CFG.
fn find_scc_regions(cfg: &CFG) -> (Vec<SccRegion>, FxHashMap<BasicBlock, BasicBlock>) {
    let successors: Vec<Vec<usize>> = cfg
        .successors
        .iter()
        .map(|nexts| nexts.iter().map(|bb| bb.as_usize()).collect())
        .collect();
    let components = collect_scc_components(&successors);

    let mut scc_regions = Vec::new();
    let mut block_to_scc = FxHashMap::default();
    for mut component in components {
        component.sort_unstable();
        let has_self_edge = component.len() == 1
            && cfg.successors[component[0]]
                .iter()
                .any(|succ| succ.as_usize() == component[0]);
        if component.len() <= 1 && !has_self_edge {
            continue;
        }

        let representative = BasicBlock::from_usize(component[0]);
        let block_set: FxHashSet<usize> = component.iter().copied().collect();
        let mut exits = Vec::new();
        let mut backedges = Vec::new();

        for &block_idx in &component {
            let block = BasicBlock::from_usize(block_idx);
            for &succ in cfg.successors(block) {
                let succ_idx = succ.as_usize();
                if block_set.contains(&succ_idx) {
                    if succ_idx <= block_idx || succ == representative {
                        backedges.push((block, succ));
                    }
                } else {
                    exits.push(SccExit {
                        from: block,
                        to: succ,
                    });
                }
            }
        }

        for &block_idx in &component {
            block_to_scc.insert(BasicBlock::from_usize(block_idx), representative);
        }

        scc_regions.push(SccRegion {
            representative,
            blocks: component.into_iter().map(BasicBlock::from_usize).collect(),
            exits,
            backedges,
        });
    }

    (scc_regions, block_to_scc)
}
