//! Path extraction for verification targets.
//!
//! This module builds finite, acyclic paths from a function CFG to each unsafe callsite
//! so that the verifier can reason about pointer properties along concrete execution
//! traces without unrolling loops or recursive cycles.
//!
//! # Path reachability
//!
//! Each path is validated against a `PathGraph` (an SCC-aware path enumeration
//! structure) to ensure the computed block sequence is actually reachable. Paths
//! that fail this check are silently discarded.
//!
//! # Path limit
//!
//! To prevent exponential blow-up, path enumeration is capped at `PATH_LIMIT`
//! (currently 1024) per search. Searches stop producing new paths once the limit
//! is reached.

use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def_id::DefId;
use rustc_middle::{mir::BasicBlock, ty::TyCtxt};

use crate::analysis::path_analysis::graph::PathGraph;

use super::helpers::{Callsite, CallsiteLocation};

pub(crate) const PATH_LIMIT: usize = 1024;

/// Extracts finite verification paths for one function body.
///
/// Uses `PathGraph` for SCC-aware path enumeration, then filters
/// whole-CFG paths to those reaching each callsite.
pub struct PathExtractor<'tcx> {
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    callsites: Vec<Callsite<'tcx>>,
    paths: FxHashMap<CallsiteLocation, Vec<Path>>,
    path_graph: Option<PathGraph<'tcx>>,
    allow_repeat: usize,
}

impl<'tcx> PathExtractor<'tcx> {
    /// Create a path extractor for `def_id` and the callsites found in that body.
    ///
    /// This initializes the CFG and stores callsites. SCC detection and path
    /// extraction are deferred until [`run`] is called.
    ///
    /// `allow_repeat` controls how many times a repeated SCC postfix segment
    /// is allowed beyond the first occurrence. Default is 0 (no extra repeats).
    pub fn new(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        callsites: Vec<Callsite<'tcx>>,
        allow_repeat: usize,
    ) -> Self {
        Self {
            tcx,
            def_id,
            callsites,
            paths: FxHashMap::default(),
            path_graph: None,
            allow_repeat,
        }
    }

    /// Get (or create) the PathGraph for this function's path enumeration.
    fn path_graph(&mut self) -> &mut PathGraph<'tcx> {
        self.path_graph.get_or_insert_with(|| {
            let mut pg = PathGraph::new(self.tcx, self.def_id);
            pg.find_scc();
            pg
        })
    }

    /// Run path extraction, consuming the extractor.
    ///
    /// Returns a `FunctionPaths` value with per-callsite path vectors.
    pub fn run(mut self) -> FunctionPaths<'tcx> {
        // Ensure PathGraph is initialized (also builds SCC info internally).
        self.path_graph();
        self.find_paths();
        FunctionPaths {
            callsite_paths: CallsitePaths::new(self.callsites, self.paths),
        }
    }

    /// Extract paths for every callsite owned by this extractor.
    ///
    /// Iterates over all callsites and delegates to [`find_paths_for_callsite`]
    /// for each one. Results are stored in `self.paths` keyed by callsite location.
    fn find_paths(&mut self) {
        for index in 0..self.callsites.len() {
            let callsite = self.callsites[index].clone();
            let paths = self.find_paths_for_callsite(&callsite);
            self.paths.insert(callsite.location(), paths);
        }
    }

    /// Extract paths for one callsite by filtering pre-enumerated whole-function paths.
    ///
    /// Uses `PathGraph::enumerate_paths_repeat()` to get all flattened CFG paths,
    /// then filters to those containing the target callsite block and passing
    /// reachability. Paths are truncated at the target block.
    fn find_paths_for_callsite(&mut self, callsite: &Callsite<'tcx>) -> Vec<Path> {
        let target = callsite.location();
        let target_block = callsite.block.as_usize();
        let callee_name = callsite.callee_name(self.tcx);
        let allow_repeat = self.allow_repeat;
        let pg = self.path_graph();

        let all_paths = pg.enumerate_paths_repeat(allow_repeat);

        rap_debug!(
            "Callsite at bb{} -> {}: {} whole-cfg paths",
            target_block,
            callee_name,
            all_paths.len()
        );

        let mut results = Vec::new();
        let mut seen_prefixes = FxHashSet::default();
        for (idx, path) in all_paths.iter().enumerate() {
            if results.len() >= PATH_LIMIT {
                break;
            }
            let Some(pos) = path.iter().position(|&b| b == target_block) else {
                continue;
            };
            let prefix: Vec<usize> = path[..=pos].to_vec();
            if !seen_prefixes.insert(prefix.clone()) {
                continue;
            }
            let reachable = pg.is_path_reachable(&prefix);
            rap_debug!(
                "  verify path {}: {:?} | {}",
                idx,
                prefix,
                if reachable {
                    "reachable"
                } else {
                    "unreachable"
                }
            );
            if !reachable {
                continue;
            }
            results.push(Path {
                target,
                start: PathStart::FunctionEntry,
                steps: prefix
                    .into_iter()
                    .map(|b| PathStep::Block(BasicBlock::from(b)))
                    .chain(std::iter::once(PathStep::Callsite(target)))
                    .collect(),
            });
        }
        results
    }
}

/// Result of path extraction for one function.
pub struct FunctionPaths<'tcx> {
    callsite_paths: CallsitePaths<'tcx>,
}

impl<'tcx> FunctionPaths<'tcx> {
    pub fn paths_for(&self, location: CallsiteLocation) -> &[Path] {
        self.callsite_paths.paths_for(location)
    }

    pub fn callsites(&self) -> &[Callsite<'tcx>] {
        self.callsite_paths.callsites()
    }
}

pub struct CallsitePaths<'tcx> {
    callsites: Vec<Callsite<'tcx>>,
    paths_by_callsite: FxHashMap<CallsiteLocation, Vec<Path>>,
}

impl<'tcx> CallsitePaths<'tcx> {
    fn new(
        callsites: Vec<Callsite<'tcx>>,
        paths_by_callsite: FxHashMap<CallsiteLocation, Vec<Path>>,
    ) -> Self {
        Self {
            callsites,
            paths_by_callsite,
        }
    }

    pub fn callsites(&self) -> &[Callsite<'tcx>] {
        &self.callsites
    }

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
    /// Ordered steps from the start point to the target callsite.
    pub steps: Vec<PathStep>,
}

impl Path {
    /// Render this path as a compact string for diagnostics.
    pub fn describe(&self) -> String {
        self.describe_body()
    }

    /// Render only the path body from the start point to the callsite.
    pub fn describe_body(&self) -> String {
        self.steps
            .iter()
            .filter_map(|step| match step {
                PathStep::Block(bb) => Some(format!("{}", bb.as_usize())),
                PathStep::Callsite(_) => None,
            })
            .collect::<Vec<_>>()
            .join(" -> ")
    }

    /// Render this path as a compact array of block indices.
    pub fn describe_indices(&self) -> String {
        let mut indices: Vec<usize> = Vec::new();
        for step in &self.steps {
            match step {
                PathStep::Block(b) => indices.push(b.as_usize()),
                PathStep::Callsite(l) => {
                    let bb = l.block.as_usize();
                    if indices.last() != Some(&bb) {
                        indices.push(bb);
                    }
                }
            }
        }
        format!("{:?}", indices)
    }
}

/// Start point for a finite verification path.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PathStart {
    /// The path starts at the function entry block.
    FunctionEntry,
}

/// One step in a finite verification path.
#[derive(Clone, Debug)]
pub enum PathStep {
    /// A normal MIR basic block.
    Block(BasicBlock),
    /// The target callsite that terminates the path.
    Callsite(CallsiteLocation),
}
