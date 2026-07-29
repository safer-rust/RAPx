//! Path extraction for verification targets.
//!
//! This module builds finite, acyclic paths from a function CFG to each unsafe checkpoint
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

use crate::compat::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::{mir::BasicBlock, ty::TyCtxt};

use crate::analysis::path_analysis::{
    PathTree,
    graph::{PathEnumerator, PathGraph},
};

use crate::helpers::mir_scan::{Checkpoint, CheckpointLocation};

pub(crate) const PATH_LIMIT: usize = 1024;

/// Enumerates finite, SCC-aware verification paths from the function entry
/// to each unsafe checkpoint in a single function body.
///
/// `PathExtractor` is the **first stage** of the verification pipeline.  It
/// takes a function's MIR control-flow graph and a list of unsafe checkpoints,
/// then produces a [`CheckpointPaths`] value that maps every checkpoint to a set
/// of acyclic block-level paths reaching it.
///
/// # Pipeline role
///
/// ```text
/// PathExtractor ──► BackwardSlicer ──► ForwardVerifier ──► SmtChecker
///    (paths)          (relevant items)    (abstract facts)    (satisfiability)
/// ```
///
/// The paths produced here determine *which* MIR instructions the slicer
/// will inspect and in what order, so path quality directly affects
/// verification precision.
///
/// # SCC handling
///
/// Loops (strongly connected components) are detected and collapsed by
/// [`PathGraph`].  The `allow_repeat` parameter controls how many extra
/// iterations of each SCC postfix are appended beyond the first — useful
/// for modeling loop-carried effects without unrolling indefinitely.
///
/// # Path limit
///
/// Per-checkpoint path count is capped at [`PATH_LIMIT`] (1024) to prevent
/// exponential blow-up in functions with many branches.
pub struct PathExtractor<'tcx> {
    /// Compiler type context used for MIR access and name resolution.
    tcx: TyCtxt<'tcx>,
    /// The function whose MIR body is being analyzed.
    def_id: DefId,
    /// Unsafe checkpoints (call terminators, raw-ptr derefs, static mut accesses)
    /// discovered in the function's MIR body.
    checkpoints: Vec<Checkpoint<'tcx>>,
    /// Number of extra SCC postfix repetitions allowed (default 0).
    allow_repeat: usize,
}

impl<'tcx> PathExtractor<'tcx> {
    /// Create a path extractor for `def_id` and the checkpoints found in that body.
    ///
    /// Path extraction (SCC detection, enumeration, filtering) is deferred
    /// until [`run`] is called.
    ///
    /// `allow_repeat` controls how many times a repeated SCC postfix segment
    /// is allowed beyond the first occurrence. Default is 0 (no extra repeats).
    pub fn new(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        checkpoints: Vec<Checkpoint<'tcx>>,
        allow_repeat: usize,
    ) -> Self {
        Self {
            tcx,
            def_id,
            checkpoints,
            allow_repeat,
        }
    }

    /// Run path extraction, consuming the extractor.
    ///
    /// Returns a `Vec<CallGroup>` — one entry per unique callee DefId.
    /// Checkpoints that target the same callee share a single `PathTree`,
    /// avoiding redundant subtree construction.
    pub fn run(self) -> Vec<CallGroup<'tcx>> {
        let mut graph = PathGraph::new(self.tcx, self.def_id);
        graph.find_scc();
        let tree = {
            let mut enumerator = PathEnumerator::new(&graph);
            enumerator.enumerate_paths_repeat(self.allow_repeat)
        };
        group_by_callee(self.checkpoints, &tree)
    }
}

/// Checkpoints targeting the same callee, grouped for shared path analysis.
///
/// One `CallGroup` is produced per unique callee `DefId` in the function.
/// All checkpoints in the group share the same `PathTree`; individual paths
/// are filtered by `checkpoint.block` at query time.
pub struct CallGroup<'tcx> {
    /// Shared full-CFG prefix tree, built once for all checkpoints in the group.
    pub tree: PathTree,
    /// Checkpoints that target this callee.
    pub checkpoints: Vec<Checkpoint<'tcx>>,
}

fn group_by_callee<'tcx>(
    checkpoints: Vec<Checkpoint<'tcx>>,
    _tree: &PathTree,
) -> Vec<CallGroup<'tcx>> {
    let mut groups: FxHashMap<Option<DefId>, Vec<Checkpoint<'tcx>>> = FxHashMap::default();
    for cs in checkpoints {
        groups.entry(cs.callee).or_default().push(cs);
    }
    groups
        .into_iter()
        .map(|(_callee, checkpoints)| CallGroup {
            tree: _tree.clone(),
            checkpoints,
        })
        .collect()
}

/// One finite, acyclic execution trace from the function entry to a target
/// checkpoint, represented as an ordered sequence of MIR basic blocks.
///
/// A `Path` is the core currency flowing through the verification pipeline.
/// It is produced by [`PathExtractor`], then consumed by the
/// [`BackwardSlicer`](super::slicer::BackwardSlicer) to determine which MIR
/// instructions are relevant to the safety property being checked.
///
/// # Structure
///
/// Each path consists of:
/// - **`target`** — the [`CheckpointLocation`] identifying the specific call
///   terminator (or synthetic checkpoint) this path reaches.  Redundant
///   with the final step but stored separately for fast lookup.
/// - **`steps`** — an ordered list of [`PathStep`] values.  Intermediate
///   steps are MIR basic blocks; the final step is always
///   `PathStep::Checkpoint(target)`.  The path always starts at function
///   entry (block `bb0`).
///
/// # Reachability
///
/// Every `Path` returned by `PathExtractor` is guaranteed to be *reachable*
/// in the function's CFG.  Paths that cannot be validated against the
/// SCC-aware [`PathGraph`] are silently discarded during extraction.
///
/// # Example (compact notation)
///
/// ```text
/// bb2 -> bb3 -> bb4 -> checkpoint@bb5::unsafe_fn
/// ```
///
/// In the path above, blocks 2, 3, and 4 are intermediate MIR blocks;
/// block 5 contains the unsafecall terminator that the path targets.
#[derive(Clone, Debug)]
pub struct Path {
    /// The checkpoint location (function + basic block) reached by this path.
    pub target: CheckpointLocation,
    /// Ordered sequence of basic blocks from function entry to `target`,
    /// terminated by a `PathStep::Checkpoint`.
    pub steps: Vec<PathStep>,
}

impl Path {
    /// Render this path as a compact string for diagnostics.
    pub fn describe(&self) -> String {
        self.describe_body()
    }

    /// Render only the path body from the start point to the checkpoint.
    pub fn describe_body(&self) -> String {
        self.steps
            .iter()
            .filter_map(|step| match step {
                PathStep::Block(bb) => Some(format!("{}", bb.as_usize())),
                PathStep::Checkpoint(_) => None,
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
                PathStep::Checkpoint(l) => {
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

/// One step in a finite verification path.
#[derive(Clone, Debug)]
pub enum PathStep {
    /// A normal MIR basic block.
    Block(BasicBlock),
    /// The target checkpoint that terminates the path.
    Checkpoint(CheckpointLocation),
}
