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

use crate::graphs::scc::{SccRegion, find_scc_regions};

use super::helpers::{CFG, Callsite, CallsiteLocation};

const PATH_LIMIT: usize = 1024;

/// Shared DFS state for entry-path search (target callsite outside SCC regions).
struct EntrySearchCtx<'a> {
    visited: &'a mut FxHashSet<BasicBlock>,
    stack: &'a mut Vec<PathStep>,
    results: &'a mut Vec<Path>,
    limit: usize,
    target: CallsiteLocation,
    target_block: BasicBlock,
}

/// Shared DFS state for entry-prefix search (to an SCC representative).
struct PrefixSearchCtx<'a> {
    visited: &'a mut FxHashSet<BasicBlock>,
    stack: &'a mut Vec<PathStep>,
    results: &'a mut Vec<Vec<PathStep>>,
    limit: usize,
    representative: BasicBlock,
}

/// Shared DFS state for SCC-internal path search.
struct SccInternalCtx<'a> {
    visited: &'a mut FxHashSet<BasicBlock>,
    stack: &'a mut Vec<PathStep>,
    results: &'a mut Vec<Path>,
    limit: usize,
    target: CallsiteLocation,
    target_block: BasicBlock,
    representative: BasicBlock,
    scc_blocks: &'a FxHashSet<BasicBlock>,
    entry_prefixes: &'a [Vec<PathStep>],
}

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
        let (scc_regions, block_to_scc) = find_scc_regions(&self.cfg.successors);
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

    // ── entry-path search (target outside SCC) ──────────────────────────

    fn find_entry_paths(&self, target: CallsiteLocation, target_block: BasicBlock) -> Vec<Path> {
        let mut results = Vec::new();
        let mut stack = vec![PathStep::Block(self.cfg.entry)];
        let mut visited = FxHashSet::default();
        visited.insert(self.cfg.entry);
        let mut ctx = EntrySearchCtx {
            visited: &mut visited,
            stack: &mut stack,
            results: &mut results,
            limit: PATH_LIMIT,
            target,
            target_block,
        };
        self.dfs_entry_paths(self.cfg.entry, &mut ctx);
        results
    }

    fn dfs_entry_paths(&self, current: BasicBlock, ctx: &mut EntrySearchCtx<'_>) {
        if ctx.results.len() >= ctx.limit {
            return;
        }

        if current == ctx.target_block {
            ctx.stack.push(PathStep::Callsite(ctx.target));
            ctx.results.push(Path {
                target: ctx.target,
                start: PathStart::FunctionEntry,
                entry_prefix: Vec::new(),
                steps: ctx.stack.clone(),
            });
            ctx.stack.pop();
            return;
        }

        for &next in self.cfg.successors(current) {
            if ctx.results.len() >= ctx.limit {
                break;
            }

            if let Some(representative) = self.block_to_scc.get(&next).copied() {
                if self.block_to_scc.get(&ctx.target_block).copied() == Some(representative) {
                    continue;
                }
                self.follow_scc_exits(next, representative, ctx);
                continue;
            }

            if ctx.visited.contains(&next) {
                continue;
            }

            ctx.stack.push(PathStep::Block(next));
            ctx.visited.insert(next);
            self.dfs_entry_paths(next, ctx);
            ctx.visited.remove(&next);
            ctx.stack.pop();
        }
    }

    fn follow_scc_exits(
        &self,
        entry: BasicBlock,
        representative: BasicBlock,
        ctx: &mut EntrySearchCtx<'_>,
    ) {
        let Some(scc_info) = self.scc_by_representative(representative) else {
            return;
        };
        let scc_blocks: FxHashSet<BasicBlock> = scc_info.blocks.iter().copied().collect();

        for exit in &scc_info.exits {
            if ctx.results.len() >= ctx.limit {
                break;
            }
            if ctx.visited.contains(&exit.to) {
                continue;
            }

            let internal_paths =
                self.find_scc_paths_to(&scc_blocks, entry, exit.from, ctx.limit);

            for internal_path in &internal_paths {
                if ctx.results.len() >= ctx.limit {
                    break;
                }

                let mut pushed: Vec<BasicBlock> = Vec::new();
                for &block in internal_path {
                    ctx.stack.push(PathStep::Block(block));
                    ctx.visited.insert(block);
                    pushed.push(block);
                }

                if ctx.visited.contains(&exit.to) {
                    for &block in pushed.iter().rev() {
                        ctx.visited.remove(&block);
                        ctx.stack.pop();
                    }
                    continue;
                }

                ctx.stack.push(PathStep::Block(exit.to));
                ctx.visited.insert(exit.to);
                self.dfs_entry_paths(exit.to, ctx);
                ctx.visited.remove(&exit.to);
                ctx.stack.pop();

                for &block in pushed.iter().rev() {
                    ctx.visited.remove(&block);
                    ctx.stack.pop();
                }
            }
        }
    }

    // ── entry-prefix search (to SCC representative) ─────────────────────

    fn find_entry_prefixes(&self, representative: BasicBlock, limit: usize) -> Vec<Vec<PathStep>> {
        if self.cfg.entry == representative {
            return vec![Vec::new()];
        }

        let mut results = Vec::new();
        let mut stack = vec![PathStep::Block(self.cfg.entry)];
        let mut visited = FxHashSet::default();
        visited.insert(self.cfg.entry);
        let mut ctx = PrefixSearchCtx {
            visited: &mut visited,
            stack: &mut stack,
            results: &mut results,
            limit,
            representative,
        };
        self.dfs_entry_prefixes(self.cfg.entry, &mut ctx);

        if results.is_empty() {
            vec![Vec::new()]
        } else {
            results
        }
    }

    fn dfs_entry_prefixes(&self, current: BasicBlock, ctx: &mut PrefixSearchCtx<'_>) {
        if ctx.results.len() >= ctx.limit {
            return;
        }

        for &next in self.cfg.successors(current) {
            if ctx.results.len() >= ctx.limit {
                break;
            }

            if next == ctx.representative {
                ctx.results.push(ctx.stack.clone());
                continue;
            }

            if let Some(scc_representative) = self.block_to_scc.get(&next).copied() {
                if scc_representative == ctx.representative {
                    continue;
                }
                self.follow_scc_exits_for_prefix(next, scc_representative, ctx);
                continue;
            }

            if ctx.visited.contains(&next) {
                continue;
            }

            ctx.stack.push(PathStep::Block(next));
            ctx.visited.insert(next);
            self.dfs_entry_prefixes(next, ctx);
            ctx.visited.remove(&next);
            ctx.stack.pop();
        }
    }

    fn follow_scc_exits_for_prefix(
        &self,
        entry: BasicBlock,
        scc_representative: BasicBlock,
        ctx: &mut PrefixSearchCtx<'_>,
    ) {
        let Some(scc_info) = self.scc_by_representative(scc_representative) else {
            return;
        };
        let scc_blocks: FxHashSet<BasicBlock> = scc_info.blocks.iter().copied().collect();

        for exit in &scc_info.exits {
            if ctx.results.len() >= ctx.limit {
                break;
            }
            if ctx.visited.contains(&exit.to) {
                continue;
            }

            let internal_paths =
                self.find_scc_paths_to(&scc_blocks, entry, exit.from, ctx.limit);

            for internal_path in &internal_paths {
                if ctx.results.len() >= ctx.limit {
                    break;
                }

                let mut pushed: Vec<BasicBlock> = Vec::new();
                for &block in internal_path {
                    ctx.stack.push(PathStep::Block(block));
                    ctx.visited.insert(block);
                    pushed.push(block);
                }

                if ctx.visited.contains(&exit.to) {
                    for &block in pushed.iter().rev() {
                        ctx.visited.remove(&block);
                        ctx.stack.pop();
                    }
                    continue;
                }

                ctx.stack.push(PathStep::Block(exit.to));
                ctx.visited.insert(exit.to);
                self.dfs_entry_prefixes(exit.to, ctx);
                ctx.visited.remove(&exit.to);
                ctx.stack.pop();

                for &block in pushed.iter().rev() {
                    ctx.visited.remove(&block);
                    ctx.stack.pop();
                }
            }
        }
    }

    // ── SCC-internal path search ────────────────────────────────────────

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
        let mut ctx = SccInternalCtx {
            visited: &mut visited,
            stack: &mut stack,
            results: &mut results,
            limit: PATH_LIMIT,
            target,
            target_block,
            representative,
            scc_blocks: &scc_blocks,
            entry_prefixes: &entry_prefixes,
        };
        self.dfs_scc_internal_paths(scc_info.representative, &mut ctx);
        results
    }

    fn dfs_scc_internal_paths(&self, current: BasicBlock, ctx: &mut SccInternalCtx<'_>) {
        if ctx.results.len() >= ctx.limit {
            return;
        }

        if current == ctx.target_block {
            ctx.stack.push(PathStep::Callsite(ctx.target));
            for entry_prefix in ctx.entry_prefixes {
                ctx.results.push(Path {
                    target: ctx.target,
                    start: PathStart::SccRepresentative {
                        representative: ctx.representative,
                    },
                    entry_prefix: entry_prefix.clone(),
                    steps: ctx.stack.clone(),
                });
                if ctx.results.len() >= ctx.limit {
                    break;
                }
            }
            ctx.stack.pop();
            return;
        }

        for &next in self.cfg.successors(current) {
            if !ctx.scc_blocks.contains(&next) || ctx.visited.contains(&next) {
                continue;
            }
            ctx.stack.push(PathStep::Block(next));
            ctx.visited.insert(next);
            self.dfs_scc_internal_paths(next, ctx);
            ctx.visited.remove(&next);
            ctx.stack.pop();
        }
    }

    /// Return the detected SCC region whose representative is `representative`.
    fn scc_by_representative(&self, representative: BasicBlock) -> Option<&SccRegion> {
        self.scc_regions
            .iter()
            .find(|scc_info| scc_info.representative == representative)
    }

    /// Find all simple paths from `from` to `to` within `scc_blocks` (endpoints included).
    fn find_scc_paths_to(
        &self,
        scc_blocks: &FxHashSet<BasicBlock>,
        from: BasicBlock,
        to: BasicBlock,
        limit: usize,
    ) -> Vec<Vec<BasicBlock>> {
        if from == to {
            return vec![vec![from]];
        }
        let mut results = Vec::new();
        let mut visited = FxHashSet::default();
        let mut stack = vec![from];
        visited.insert(from);
        self.dfs_scc_paths_to(scc_blocks, from, to, limit, &mut visited, &mut stack, &mut results);
        results
    }

    fn dfs_scc_paths_to(
        &self,
        scc_blocks: &FxHashSet<BasicBlock>,
        current: BasicBlock,
        target: BasicBlock,
        limit: usize,
        visited: &mut FxHashSet<BasicBlock>,
        stack: &mut Vec<BasicBlock>,
        results: &mut Vec<Vec<BasicBlock>>,
    ) {
        if results.len() >= limit {
            return;
        }

        for &next in self.cfg.successors(current) {
            if results.len() >= limit {
                break;
            }

            if next == target {
                let mut path = stack.clone();
                path.push(next);
                results.push(path);
                continue;
            }

            if !scc_blocks.contains(&next) || visited.contains(&next) {
                continue;
            }

            stack.push(next);
            visited.insert(next);
            self.dfs_scc_paths_to(scc_blocks, next, target, limit, visited, stack, results);
            visited.remove(&next);
            stack.pop();
        }
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
    /// Blocks from function entry to this path's start.
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
    /// The target callsite that terminates the path.
    Callsite(CallsiteLocation),
}
