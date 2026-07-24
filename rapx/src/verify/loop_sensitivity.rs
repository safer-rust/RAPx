//! Loop-sensitivity planning for the staged verifier.
//!
//! The planner runs before path extraction in `verify --postfix-repeat auto`.
//! It keeps the decision about loop depth separate from individual safety-tag
//! checkers: tags still describe what must hold, while this module decides
//! whether the checked value depends on loop-carried MIR state.
//!
//! # Pipeline role
//!
//! ```text
//! VerifyTargetCollector ──► LoopSensitivityAnalyzer ──► VerifyDriver
//!        (sinks)                 (repeat plan)             (paths + checks)
//! ```
//!
//! The normal verifier is path-bounded: `PathExtractor` receives a numeric
//! `allow_repeat` and enumerates only that many extra SCC postfix repetitions.
//! In auto mode, this module chooses that number from MIR structure instead of
//! from an already-failed tag-specific retry loop.
//!
//! # Current abstraction
//!
//! The planner now has two internal hint streams:
//!
//! - `DataflowDistanceHint`: a sink depends on loop-carried state, and the
//!   planner estimates how many loop backedges are needed for that state to
//!   reach the sink.
//! - `NumericRangeHint`: a numeric/index obligation depends on induction-style
//!   state, and the planner estimates the first iteration that can witness a
//!   range violation.
//!
//! `RepeatPlan` is the single product consumed by the driver.  It calibrates
//! both hint kinds into the `PathEnumerator`'s `allow_repeat` budget and picks
//! the maximum, so detector-specific details stay inside this module.

use crate::analysis::path_analysis::graph::PathGraph;
use crate::compat::{FxHashMap, FxHashSet};
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{
        BasicBlock, BinOp, Body, Local, Operand, Place, ProjectionElem, Rvalue, StatementKind,
        TerminatorKind,
    },
    ty::{TyCtxt, TyKind, TypingEnv},
};

use super::{
    contract::{ContractExpr, NumericPredicate, Property, PropertyArg, PropertyKind, RelOp},
    def_use::{RelevantPlaces, bind_callsite_roots},
    helpers::{Checkpoint, CheckpointKind, CheckpointLocation},
    report::CheckResult,
    target::FunctionTarget,
};

/// Upper bound for repeat selected by auto mode.
pub(crate) const MAX_AUTO_REPEAT: usize = 16;

/// Fallback loop-carried distance used when a sink is loop-sensitive but the
/// local transfer graph is too imprecise to calculate a better distance.
///
/// Three backedges calibrates to `allow_repeat = 2`, which is the first depth
/// needed by the delayed pointer/state cases in `loop_repeat_threshold`.
const DEFAULT_LOOP_CARRIED_BACKEDGES: usize = 3;

/// Conservative first numeric witness when an index obligation is known to be
/// induction-sensitive but the current summary cannot yet recover a concrete
/// symbolic bound.
const DEFAULT_NUMERIC_WITNESS_ITERATION: usize = 4;

/// The first repeat depth that reliably exposes the existing delayed
/// loop-carried pointer/state fixtures.
const MIN_DATAFLOW_REPEAT: usize = 2;

/// Backedge budget used when an internally branched SCC has loop-carried
/// assignments into a checked sink.
///
/// This calibrates to `allow_repeat = 2`, which is enough to cover the shallow
/// branch-sensitive SCC fixtures without pushing the enumerator into a large
/// repeat where path limits may hide lower-depth witnesses.
const BRANCH_SENSITIVE_BACKEDGES: usize = DEFAULT_LOOP_CARRIED_BACKEDGES;

/// User-selected policy for SCC postfix repetition.
///
/// `Fixed(n)` preserves the explicit CLI behavior: the driver checks all
/// rounds `0..=n`.  `Auto` delegates the upper bound to this module and checks
/// `0..=plan.repeat`, because the current SCC path enumerator is not strictly
/// monotonic across repeat depths when path limits and branch order interact.
#[derive(Clone, Copy, Debug)]
pub enum RepeatStrategy {
    /// Let `LoopSensitivityAnalyzer` choose a repeat count from MIR structure.
    Auto,
    /// Use the concrete repeat count supplied by `--postfix-repeat N`.
    Fixed(usize),
}

/// Unified product of the auto loop-sensitivity pass for one function target.
///
/// `repeat` is the only field consumed by the current driver.  The two hint
/// lists keep detector-specific evidence available internally while preserving
/// one compact scheduling decision for `VerifyRun`.
#[derive(Clone, Debug, Default)]
pub(crate) struct RepeatPlan<'tcx> {
    /// Repeat count that should be passed to `VerifyDriver::new_with_repeat`.
    pub repeat: usize,
    /// Loop-carried dataflow hints, calibrated through `needed_backedges`.
    #[allow(dead_code)]
    pub dataflow_hints: Vec<DataflowDistanceHint>,
    /// Numeric/index hints, calibrated through `witness_iteration`.
    #[allow(dead_code)]
    pub numeric_hints: Vec<NumericRangeHint>,
    /// Future direct findings from loop summaries such as affine range proofs.
    #[allow(dead_code)]
    pub summary_findings: Vec<LoopSummaryFinding<'tcx>>,
}

impl<'tcx> RepeatPlan<'tcx> {
    /// Merge both detector streams into the path-enumerator repeat budget.
    fn from_hints(
        dataflow_hints: Vec<DataflowDistanceHint>,
        numeric_hints: Vec<NumericRangeHint>,
        summary_findings: Vec<LoopSummaryFinding<'tcx>>,
    ) -> Self {
        let repeat = dataflow_hints
            .iter()
            .map(DataflowDistanceHint::calibrated_repeat)
            .chain(
                numeric_hints
                    .iter()
                    .map(NumericRangeHint::calibrated_repeat),
            )
            .max()
            .unwrap_or(0)
            .min(MAX_AUTO_REPEAT);

        Self {
            repeat,
            dataflow_hints,
            numeric_hints,
            summary_findings,
        }
    }
}

/// A loop-carried dataflow hint.
///
/// `needed_backedges` is measured in loop backedge traversals between the first
/// loop iteration where a source can be produced and the first iteration where
/// that source can reach the sink.  It is converted to `allow_repeat` by
/// [`repeat_for_backedges`].
#[derive(Clone, Debug)]
#[allow(dead_code)]
pub(crate) struct DataflowDistanceHint {
    /// Estimated number of loop backedges required for propagation.
    pub needed_backedges: usize,
    /// Entry block of the loop SCC that affects the sink.
    pub scc_entry: usize,
    /// Basic block containing the unsafe checkpoint or synthetic checkpoint.
    pub checkpoint_block: usize,
    /// Safety property whose argument depends on loop state.
    pub property_kind: PropertyKind,
    /// Short internal explanation for developer-facing diagnostics.
    pub reason: String,
}

impl DataflowDistanceHint {
    /// Convert this hint into the path enumerator's repeat budget.
    fn calibrated_repeat(&self) -> usize {
        repeat_for_backedges(self.needed_backedges)
    }
}

/// A numeric/index range hint.
///
/// `witness_iteration` is the first loop-body execution that may violate the
/// property under the simple numeric model.  For example, `value += 1` followed
/// by `ValidNum(value < 100)` yields witness iteration 100 when `value` starts
/// at zero.
#[derive(Clone, Debug)]
#[allow(dead_code)]
pub(crate) struct NumericRangeHint {
    /// First loop-body execution that can witness a violation.
    pub witness_iteration: usize,
    /// Entry block of the loop SCC that affects the sink.
    pub scc_entry: usize,
    /// Basic block containing the unsafe checkpoint or synthetic checkpoint.
    pub checkpoint_block: usize,
    /// Safety property whose argument depends on induction/range state.
    pub property_kind: PropertyKind,
    /// Short internal explanation for developer-facing diagnostics.
    pub reason: String,
}

impl NumericRangeHint {
    /// Convert this hint into the path enumerator's repeat budget.
    fn calibrated_repeat(&self) -> usize {
        repeat_for_witness_iteration(self.witness_iteration)
    }
}

/// Placeholder for future loop-summary results.
///
/// Some future detectors can prove that a loop violates a numeric/index
/// obligation without asking `PathEnumerator` to materialize the exact failing
/// iteration.  Such findings can be appended to `VerificationReport` through
/// this structure.  The current implementation only selects repeat depth.
#[derive(Clone, Debug)]
#[allow(dead_code)]
pub(crate) struct LoopSummaryFinding<'tcx> {
    /// Checkpoint at which the summarized violation should be reported.
    pub checkpoint: CheckpointLocation,
    /// Stable checkpoint index used by existing summary grouping.
    pub checkpoint_index: usize,
    /// Property index within the checkpoint's property list.
    pub property_index: usize,
    /// Property proved unsafe or inconclusive by the summary.
    pub property: Property<'tcx>,
    /// Result to surface, usually `Unknown` or `Failed`.
    pub result: CheckResult,
    /// Synthetic path label for the summarized loop witness.
    pub path_description: String,
    /// Callee/checkpoint name used by the existing report printer.
    pub callee_name: String,
    /// Internal diagnostic text for the summarized reason.
    pub diagnostic: String,
}

/// One safety obligation whose arguments have been bound to caller MIR locals.
///
/// A sink starts as a `Property` written in the callee's namespace, for example
/// `NonNull(_ptr)`.  `bind_callsite_roots` rewrites the initial relevance roots
/// so they point at the caller locals passed into the unsafe checkpoint.  The
/// loop planner can then ask whether those caller locals depend on loop state.
struct SafetySink<'target, 'tcx> {
    /// Position among checkpoints with properties, kept for future findings.
    #[allow(dead_code)]
    checkpoint_index: usize,
    /// Unsafe call, raw pointer dereference, or static mut synthetic checkpoint.
    checkpoint: &'target Checkpoint<'tcx>,
    /// Position of this property inside the checkpoint's property list.
    #[allow(dead_code)]
    property_index: usize,
    /// Safety property checked at this sink.
    property: &'target Property<'tcx>,
    /// Caller-side MIR locals and places relevant to `property`.
    roots: RelevantPlaces,
}

/// Computes the repeat plan for one verification target.
///
/// The analyzer is intentionally target-local.  It does not cache across
/// functions because MIR bodies, SCCs, and property roots are small enough for
/// the current auto pass, and keeping the state local prevents stale repeat
/// choices when the same function is checked under a virtual target.
pub(crate) struct LoopSensitivityAnalyzer<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> LoopSensitivityAnalyzer<'tcx> {
    /// Create an analyzer over the current compiler type context.
    pub(crate) fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self { tcx }
    }

    /// Build a loop-sensitivity repeat plan for `target`.
    ///
    /// The algorithm is:
    ///
    /// 1. Collect all safety sinks and bind their roots to caller locals.
    /// 2. Build an SCC-aware `PathGraph` for the target function.
    /// 3. Build a whole-function local dependency index.
    /// 4. Produce dataflow-distance hints from loop-carried local transfers.
    /// 5. Produce numeric-range hints from simple induction-sensitive sinks.
    /// 6. Calibrate both hint streams into one repeat budget.
    ///
    /// This is a conservative planner: it may choose a deeper repeat for loops
    /// that turn out to be safe, but it avoids adding tag-specific verifier
    /// reruns or new user-visible output.
    pub(crate) fn analyze(&self, target: &FunctionTarget<'tcx>) -> RepeatPlan<'tcx> {
        if !self.tcx.is_mir_available(target.def_id) {
            return RepeatPlan::default();
        }

        let sinks = self.collect_sinks(target);
        if sinks.is_empty() {
            return RepeatPlan::default();
        }

        let mut graph = PathGraph::new(self.tcx, target.def_id);
        graph.find_scc();
        let body = self.tcx.optimized_mir(target.def_id);
        let dependencies = LocalDependencyIndex::new(self.tcx, target.def_id);
        let component_summaries: Vec<_> = loop_components(&graph)
            .into_iter()
            .map(|component| {
                let local_summary = LoopLocalSummary::new(body, &component);
                let numeric_summary =
                    LoopNumericSummary::new(self.tcx, target.def_id, body, &graph, &component);
                (component, local_summary, numeric_summary)
            })
            .collect();

        let dataflow_hints =
            self.dataflow_distance_hints(&sinks, &graph, &dependencies, &component_summaries);
        let numeric_hints =
            self.numeric_range_hints(&sinks, &graph, &dependencies, &component_summaries);

        RepeatPlan::from_hints(dataflow_hints, numeric_hints, Vec::new())
    }

    /// Compute loop-carried dataflow hints for every safety sink.
    ///
    /// This detector is tag-agnostic: it only asks whether the sink's caller
    /// locals depend on state locals that are redefined across an SCC.  The
    /// concrete safety checker remains responsible for deciding whether the
    /// propagated value is actually invalid once the deeper path is enumerated.
    fn dataflow_distance_hints<'target>(
        &self,
        sinks: &[SafetySink<'target, 'tcx>],
        graph: &PathGraph<'_>,
        dependencies: &LocalDependencyIndex,
        component_summaries: &[(LoopComponent, LoopLocalSummary, LoopNumericSummary)],
    ) -> Vec<DataflowDistanceHint> {
        let mut hints = Vec::new();

        for sink in sinks {
            if matches!(sink.property.kind, PropertyKind::Unknown | PropertyKind::Or) {
                continue;
            }
            let root_closure = dependencies.closure_from(&sink.roots.locals);
            if root_closure.is_empty() {
                continue;
            }

            for (component, local_summary, _) in component_summaries {
                if !component_reaches_checkpoint(graph, component, sink.checkpoint.block) {
                    continue;
                }
                if root_closure
                    .iter()
                    .any(|local| local_summary.assigned_inside.contains(local))
                {
                    let distance_backedges = estimate_dataflow_backedges(
                        dependencies,
                        &sink.roots.locals,
                        local_summary,
                    )
                    .unwrap_or(DEFAULT_LOOP_CARRIED_BACKEDGES);
                    let branch_backedges = estimate_branch_sensitive_backedges(
                        graph,
                        component,
                        dependencies,
                        &root_closure,
                        local_summary,
                    )
                    .unwrap_or(0);
                    let needed_backedges = distance_backedges.max(branch_backedges);
                    hints.push(DataflowDistanceHint {
                        needed_backedges,
                        scc_entry: component.entry,
                        checkpoint_block: sink.checkpoint.block.as_usize(),
                        property_kind: sink.property.kind.clone(),
                        reason: format!(
                            "safety sink depends on loop-carried state; estimated {needed_backedges} backedge(s)"
                        ),
                    });
                    break;
                }
            }
        }

        hints
    }

    /// Compute numeric/index range hints for induction-sensitive sinks.
    ///
    /// This is intentionally small but already separates numeric planning from
    /// generic dataflow.  `ValidNum` tries to recover a concrete violating
    /// iteration for positive affine increments; `InBound` currently marks the
    /// first iteration missed by shallow unrolling when the pointer/index root
    /// depends on an induction variable.
    fn numeric_range_hints<'target>(
        &self,
        sinks: &[SafetySink<'target, 'tcx>],
        graph: &PathGraph<'_>,
        dependencies: &LocalDependencyIndex,
        component_summaries: &[(LoopComponent, LoopLocalSummary, LoopNumericSummary)],
    ) -> Vec<NumericRangeHint> {
        let mut hints = Vec::new();

        for sink in sinks {
            if !is_numeric_range_property(&sink.property.kind) {
                continue;
            }
            let root_closure = dependencies.closure_from(&sink.roots.locals);
            if root_closure.is_empty() {
                continue;
            }

            for (component, local_summary, numeric_summary) in component_summaries {
                if !component_reaches_checkpoint(graph, component, sink.checkpoint.block) {
                    continue;
                }
                if !root_closure
                    .iter()
                    .any(|local| local_summary.assigned_inside.contains(local))
                {
                    continue;
                }

                let witness_iteration = match sink.property.kind {
                    PropertyKind::ValidNum => {
                        estimate_valid_num_witness(sink.property, &root_closure, numeric_summary)
                    }
                    PropertyKind::InBound => {
                        estimate_inbound_witness(&root_closure, numeric_summary)
                    }
                    _ => None,
                };

                if let Some(witness_iteration) = witness_iteration {
                    hints.push(NumericRangeHint {
                        witness_iteration,
                        scc_entry: component.entry,
                        checkpoint_block: sink.checkpoint.block.as_usize(),
                        property_kind: sink.property.kind.clone(),
                        reason: format!(
                            "numeric/index sink depends on induction state; first witness iteration {witness_iteration}"
                        ),
                    });
                    break;
                }
            }
        }

        hints
    }

    /// Collect caller-side sinks from all checkpoint kinds in a target.
    ///
    /// This mirrors `VerifyDriver::properties_for_callsite` so the planner and
    /// verifier operate on the same obligations.  Keeping it here avoids
    /// constructing a `VerifyDriver` only to learn whether a deeper repeat is
    /// needed before path extraction.
    fn collect_sinks<'target>(
        &self,
        target: &'target FunctionTarget<'tcx>,
    ) -> Vec<SafetySink<'target, 'tcx>> {
        let mut sinks = Vec::new();
        let mut checkpoint_index = 0usize;

        for checkpoint in all_checkpoints(target) {
            let properties = properties_for_checkpoint(target, checkpoint);
            if properties.is_empty() {
                continue;
            }

            for (property_index, property) in properties.iter().enumerate() {
                let mut roots = RelevantPlaces::from_property(property);
                bind_callsite_roots(self.tcx, &mut roots, checkpoint);
                if roots.locals.is_empty() {
                    continue;
                }
                sinks.push(SafetySink {
                    checkpoint_index,
                    checkpoint,
                    property_index,
                    property,
                    roots,
                });
            }

            checkpoint_index += 1;
        }

        sinks
    }
}

/// Return every checkpoint that can carry safety properties.
///
/// Real unsafe calls live in `target.checkpoints`; raw pointer dereferences and
/// static mut accesses are represented as synthetic checkpoints but participate
/// in planning exactly the same way.
fn all_checkpoints<'target, 'tcx>(
    target: &'target FunctionTarget<'tcx>,
) -> Vec<&'target Checkpoint<'tcx>> {
    target
        .checkpoints
        .iter()
        .chain(
            target
                .raw_ptr_deref_checks
                .iter()
                .map(|(checkpoint, _)| checkpoint),
        )
        .chain(
            target
                .static_mut_checks
                .iter()
                .map(|(checkpoint, _)| checkpoint),
        )
        .collect()
}

/// Look up the properties associated with a checkpoint.
///
/// The three checkpoint kinds store their properties in different fields on
/// `FunctionTarget`, so this helper centralizes the dispatch for the planner.
fn properties_for_checkpoint<'target, 'tcx>(
    target: &'target FunctionTarget<'tcx>,
    checkpoint: &'target Checkpoint<'tcx>,
) -> &'target [Property<'tcx>] {
    let loc = checkpoint.location();
    match checkpoint.kind {
        CheckpointKind::RawPtrDeref => target
            .raw_ptr_deref_checks
            .iter()
            .find(|(candidate, _)| candidate.location() == loc)
            .map(|(_, properties)| properties.as_slice())
            .unwrap_or(&[]),
        CheckpointKind::StaticMutAccess => target
            .static_mut_checks
            .iter()
            .find(|(candidate, _)| candidate.location() == loc)
            .map(|(_, properties)| properties.as_slice())
            .unwrap_or(&[]),
        CheckpointKind::UnsafeCall => checkpoint
            .callee
            .and_then(|callee| target.callee_requires.get(&callee))
            .map(Vec::as_slice)
            .unwrap_or(&[]),
    }
}

/// A non-trivial SCC in the MIR control-flow graph.
///
/// `PathGraph` records SCC members under the entry/root block.  This wrapper
/// stores the entry and a complete member set including that entry.
#[derive(Clone, Debug)]
struct LoopComponent {
    entry: usize,
    blocks: FxHashSet<usize>,
}

/// Extract loop SCCs from `PathGraph`.
///
/// Single-block non-cyclic components are ignored because they do not produce
/// loop-carried state and therefore do not need extra postfix repetition.
fn loop_components(graph: &PathGraph<'_>) -> Vec<LoopComponent> {
    let mut components = Vec::new();
    for block in &graph.cfg.blocks {
        let scc = &block.scc;
        if block.index != scc.enter || scc.nodes.is_empty() {
            continue;
        }
        let mut blocks = scc.nodes.clone();
        blocks.insert(scc.enter);
        components.push(LoopComponent {
            entry: scc.enter,
            blocks,
        });
    }
    components
}

/// Return whether a loop SCC can reach a given checkpoint block.
///
/// The planner only deepens loops that can actually influence a checked sink.
/// Reachability is checked on the CFG from the component's blocks outward.
fn component_reaches_checkpoint(
    graph: &PathGraph<'_>,
    component: &LoopComponent,
    checkpoint: BasicBlock,
) -> bool {
    let target = checkpoint.as_usize();
    if component.blocks.contains(&target) {
        return true;
    }

    let mut stack: Vec<usize> = component.blocks.iter().copied().collect();
    let mut seen = FxHashSet::default();
    while let Some(block) = stack.pop() {
        if block == target {
            return true;
        }
        if !seen.insert(block) {
            continue;
        }
        if block >= graph.cfg.blocks.len() {
            continue;
        }
        for next in &graph.cfg.block(block).next {
            stack.push(*next);
        }
    }
    false
}

/// Local assignment and transfer summary for one loop SCC.
///
/// The planner uses this for two related questions:
///
/// - Did a sink dependency get redefined inside this SCC?
/// - If so, how many loop-carried state locals are on the dependency path from
///   the sink back to an earlier source?
struct LoopLocalSummary {
    /// Locals directly assigned inside the SCC.
    assigned_inside: FxHashSet<Local>,
    /// Locals that have both an incoming value and an SCC update.
    state_locals: FxHashSet<Local>,
}

impl LoopLocalSummary {
    /// Build local assignment sets for `component`.
    fn new(body: &Body<'_>, component: &LoopComponent) -> Self {
        let mut assigned_inside = FxHashSet::default();
        let mut assigned_outside = FxHashSet::default();

        for (block, data) in body.basic_blocks.iter_enumerated() {
            let assigned = collect_assigned_locals(data);
            if component.blocks.contains(&block.as_usize()) {
                assigned_inside.extend(assigned);
            } else {
                assigned_outside.extend(assigned);
            }
        }

        let mut state_locals = FxHashSet::default();
        for local in &assigned_inside {
            if assigned_outside.contains(local) || local_is_argument(*local, body) {
                state_locals.insert(*local);
            }
        }

        Self {
            assigned_inside,
            state_locals,
        }
    }
}

/// Small numeric term language for loop guards.
#[derive(Clone, Copy, Debug)]
enum NumericTerm {
    /// MIR local.
    Local(Local),
    /// Concrete integer constant.
    Const(i128),
}

/// A MIR comparison that feeds a boolean branch.
#[derive(Clone, Copy, Debug)]
struct ComparisonFact {
    /// Comparison operator.
    op: BinOp,
    /// Left-hand side.
    lhs: NumericTerm,
    /// Right-hand side.
    rhs: NumericTerm,
}

/// Numeric induction summary for one loop SCC.
///
/// This pass currently recognizes the small affine fragment needed by the
/// threshold tests and by common counter loops:
///
/// - `x = const` before the loop.
/// - `x = x + c`, `x = x - c`, or the checked-overflow form
///   `tmp = x + c; x = tmp.0` inside the loop.
struct LoopNumericSummary {
    /// Constants assigned before entering this SCC.
    initial_constants: FxHashMap<Local, i128>,
    /// Per-iteration affine step for locals recognized as induction variables.
    steps: FxHashMap<Local, i128>,
    /// Loop guard upper bounds, for example `i < len`.
    guard_upper_bounds: FxHashMap<Local, NumericTerm>,
    /// Lower bounds known on paths that enter this SCC, for example
    /// `if len < 10 { return }` gives `len >= 10`.
    entry_lower_bounds: FxHashMap<Local, i128>,
}

impl LoopNumericSummary {
    /// Build a numeric summary for `component`.
    fn new<'tcx>(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        body: &Body<'tcx>,
        graph: &PathGraph<'_>,
        component: &LoopComponent,
    ) -> Self {
        let mut initial_constants = FxHashMap::default();
        let mut tuple_steps: FxHashMap<Local, (Local, i128)> = FxHashMap::default();
        let mut steps = FxHashMap::default();
        let mut copy_sources = FxHashMap::default();
        let mut comparisons = FxHashMap::default();

        for (block, data) in body.basic_blocks.iter_enumerated() {
            let in_component = component.blocks.contains(&block.as_usize());
            for statement in &data.statements {
                let StatementKind::Assign(assign) = &statement.kind else {
                    continue;
                };
                let (place, rvalue) = &**assign;
                if place_is_indirect_write(place) {
                    continue;
                }

                if let Some(source) = plain_copy_source(rvalue) {
                    copy_sources.insert(place.local, source);
                }
                if let Some(comparison) = comparison_fact(tcx, def_id, rvalue) {
                    comparisons.insert(place.local, comparison);
                }

                if !in_component {
                    if let Some(value) = rvalue_const_i128(tcx, def_id, rvalue) {
                        initial_constants.insert(place.local, value);
                    }
                    continue;
                }

                if let Some((source, step)) = increment_source_and_step(tcx, def_id, rvalue) {
                    if source == place.local {
                        steps.insert(place.local, step);
                    } else {
                        tuple_steps.insert(place.local, (source, step));
                    }
                }
            }
        }

        for block in &component.blocks {
            let data = &body.basic_blocks[BasicBlock::from(*block)];
            for statement in &data.statements {
                let StatementKind::Assign(assign) = &statement.kind else {
                    continue;
                };
                let (place, rvalue) = &**assign;
                if place_is_indirect_write(place) {
                    continue;
                }
                let Some(source_temp) = rvalue_projection_source(rvalue, 0) else {
                    continue;
                };
                let Some((source, step)) = tuple_steps.get(&source_temp).copied() else {
                    continue;
                };
                if source == place.local {
                    steps.insert(place.local, step);
                }
            }
        }

        let guard_upper_bounds =
            collect_loop_guard_upper_bounds(&steps, &copy_sources, &comparisons);
        let entry_lower_bounds =
            collect_entry_lower_bounds(graph, component, &copy_sources, &comparisons);

        Self {
            initial_constants,
            steps,
            guard_upper_bounds,
            entry_lower_bounds,
        }
    }
}

/// Collect locals directly redefined by statements or call destinations.
///
/// Assignments through a dereference, such as `*p = value`, mutate pointed-to
/// memory but do not redefine the pointer local `p`; those writes are ignored
/// here so the local-dependency heuristic stays focused on local state.
fn collect_assigned_locals(data: &rustc_middle::mir::BasicBlockData<'_>) -> FxHashSet<Local> {
    let mut locals = FxHashSet::default();
    for statement in &data.statements {
        let StatementKind::Assign(assign) = &statement.kind else {
            continue;
        };
        let (place, _) = &**assign;
        if !place_is_indirect_write(place) {
            locals.insert(place.local);
        }
    }
    if let TerminatorKind::Call { destination, .. } = &data.terminator().kind {
        locals.insert(destination.local);
    }
    locals
}

/// Collect loop-guard upper bounds for induction locals.
fn collect_loop_guard_upper_bounds(
    steps: &FxHashMap<Local, i128>,
    copy_sources: &FxHashMap<Local, Local>,
    comparisons: &FxHashMap<Local, ComparisonFact>,
) -> FxHashMap<Local, NumericTerm> {
    let mut bounds = FxHashMap::default();
    for comparison in comparisons.values() {
        let lhs = resolve_numeric_term(comparison.lhs, copy_sources);
        let rhs = resolve_numeric_term(comparison.rhs, copy_sources);
        match (comparison.op, lhs, rhs) {
            (BinOp::Lt | BinOp::Le, NumericTerm::Local(local), bound)
                if steps.contains_key(&local) =>
            {
                bounds.insert(local, bound);
            }
            (BinOp::Gt | BinOp::Ge, bound, NumericTerm::Local(local))
                if steps.contains_key(&local) =>
            {
                bounds.insert(local, bound);
            }
            _ => {}
        }
    }
    bounds
}

/// Collect numeric lower bounds that hold on paths entering this SCC.
fn collect_entry_lower_bounds(
    graph: &PathGraph<'_>,
    component: &LoopComponent,
    copy_sources: &FxHashMap<Local, Local>,
    comparisons: &FxHashMap<Local, ComparisonFact>,
) -> FxHashMap<Local, i128> {
    let mut bounds: FxHashMap<Local, i128> = FxHashMap::default();

    for block in &graph.cfg.blocks {
        if component.blocks.contains(&block.index) {
            continue;
        }
        let Some(terminator) = graph.cfg.terminator(block.index) else {
            continue;
        };
        let TerminatorKind::SwitchInt { discr, targets } = &terminator.kind else {
            continue;
        };
        let Some(discr_local) = operand_plain_local(discr) else {
            continue;
        };
        let discr_local = resolve_local_copy(discr_local, copy_sources);
        let Some(comparison) = comparisons.get(&discr_local).copied() else {
            continue;
        };

        for successor in switch_successors(targets) {
            if !block_reaches_component(graph, successor.block, component) {
                continue;
            }
            let Some((local, lower_bound)) =
                lower_bound_from_branch(comparison, successor.value, copy_sources)
            else {
                continue;
            };
            bounds
                .entry(local)
                .and_modify(|existing| *existing = (*existing).max(lower_bound))
                .or_insert(lower_bound);
        }
    }

    bounds
}

/// Switch successor annotated with the boolean value that selects it.
#[derive(Clone, Copy)]
struct SwitchSuccessor {
    block: usize,
    value: u128,
}

/// Return all explicit and `otherwise` successors of a bool-like switch.
fn switch_successors(targets: &rustc_middle::mir::SwitchTargets) -> Vec<SwitchSuccessor> {
    let explicit: Vec<_> = targets.iter().collect();
    let mut successors: Vec<_> = explicit
        .iter()
        .map(|(value, target)| SwitchSuccessor {
            block: target.as_usize(),
            value: *value,
        })
        .collect();
    let otherwise_value = if explicit.iter().any(|(value, _)| *value == 0) {
        1
    } else {
        0
    };
    successors.push(SwitchSuccessor {
        block: targets.otherwise().as_usize(),
        value: otherwise_value,
    });
    successors
}

/// Return whether `start` can reach any block in `component`.
fn block_reaches_component(graph: &PathGraph<'_>, start: usize, component: &LoopComponent) -> bool {
    let mut stack = vec![start];
    let mut seen = FxHashSet::default();
    while let Some(block) = stack.pop() {
        if component.blocks.contains(&block) {
            return true;
        }
        if !seen.insert(block) || block >= graph.cfg.blocks.len() {
            continue;
        }
        for next in &graph.cfg.block(block).next {
            stack.push(*next);
        }
    }
    false
}

/// Estimate extra budget needed when a loop-carried sink is controlled by
/// internal SCC branches.
///
/// This is still a dataflow hint: the sink depends on a local that is assigned
/// inside the SCC.  The extra budget accounts for a separate limitation of the
/// path extractor, where the unsafe source may live on a branch combination
/// that is not reached by the shortest value-dependency chain alone.
fn estimate_branch_sensitive_backedges(
    graph: &PathGraph<'_>,
    component: &LoopComponent,
    dependencies: &LocalDependencyIndex,
    root_closure: &FxHashSet<Local>,
    local_summary: &LoopLocalSummary,
) -> Option<usize> {
    if !component_has_internal_branch(graph, component) {
        return None;
    }

    let sink_state_reassigned = root_closure
        .iter()
        .any(|local| local_summary.state_locals.contains(local));
    let multi_source_assignment = root_closure.iter().any(|local| {
        local_summary.assigned_inside.contains(local)
            && dependencies
                .sources_by_dest
                .get(local)
                .is_some_and(|sources| sources.len() > 1)
    });

    (sink_state_reassigned || multi_source_assignment).then_some(BRANCH_SENSITIVE_BACKEDGES)
}

/// Return true when a component contains a real in-loop branch.
///
/// The ordinary loop guard usually has one successor back into the SCC and one
/// successor to the exit.  That shape alone does not need the expensive branch
/// budget.  We only count branch points where two or more successors remain
/// inside the SCC, such as `if`/`match` choices in the loop body.
fn component_has_internal_branch(graph: &PathGraph<'_>, component: &LoopComponent) -> bool {
    component.blocks.iter().any(|block| {
        graph
            .cfg
            .block(*block)
            .next
            .iter()
            .filter(|next| component.blocks.contains(next))
            .take(2)
            .count()
            >= 2
    })
}

/// Infer a local lower bound from taking one boolean branch of a comparison.
fn lower_bound_from_branch(
    comparison: ComparisonFact,
    branch_value: u128,
    copy_sources: &FxHashMap<Local, Local>,
) -> Option<(Local, i128)> {
    let is_true = branch_value != 0;
    let lhs = resolve_numeric_term(comparison.lhs, copy_sources);
    let rhs = resolve_numeric_term(comparison.rhs, copy_sources);
    match (is_true, comparison.op, lhs, rhs) {
        (false, BinOp::Lt, NumericTerm::Local(local), NumericTerm::Const(bound)) => {
            Some((local, bound))
        }
        (false, BinOp::Le, NumericTerm::Local(local), NumericTerm::Const(bound)) => {
            Some((local, bound.checked_add(1)?))
        }
        (false, BinOp::Gt, NumericTerm::Const(bound), NumericTerm::Local(local)) => {
            Some((local, bound))
        }
        (false, BinOp::Ge, NumericTerm::Const(bound), NumericTerm::Local(local)) => {
            Some((local, bound.checked_add(1)?))
        }
        (true, BinOp::Ge, NumericTerm::Local(local), NumericTerm::Const(bound)) => {
            Some((local, bound))
        }
        (true, BinOp::Gt, NumericTerm::Local(local), NumericTerm::Const(bound)) => {
            Some((local, bound.checked_add(1)?))
        }
        (true, BinOp::Le, NumericTerm::Const(bound), NumericTerm::Local(local)) => {
            Some((local, bound))
        }
        (true, BinOp::Lt, NumericTerm::Const(bound), NumericTerm::Local(local)) => {
            Some((local, bound.checked_add(1)?))
        }
        _ => None,
    }
}

/// Convert loop backedge distance to `PathEnumerator::allow_repeat`.
///
/// With the current SCC postfix encoding, `allow_repeat = 1` reaches the first
/// shallow repeated postfix paths, while the delayed threshold fixtures require
/// three loop backedges and are first exposed at `allow_repeat = 2`.
fn repeat_for_backedges(needed_backedges: usize) -> usize {
    if needed_backedges == 0 {
        0
    } else {
        needed_backedges
            .saturating_sub(1)
            .max(MIN_DATAFLOW_REPEAT)
            .min(MAX_AUTO_REPEAT)
    }
}

/// Convert a 1-based loop-body witness iteration to `allow_repeat`.
///
/// The existing threshold fixtures document the calibration point:
/// witness iteration 4 is first visible at `--postfix-repeat 2`.
fn repeat_for_witness_iteration(witness_iteration: usize) -> usize {
    witness_iteration.saturating_sub(2).min(MAX_AUTO_REPEAT)
}

/// Estimate how far loop-carried state must travel before reaching a sink.
///
/// This uses the whole-function local dependency graph, but only increments the
/// distance when the dependency path crosses a state local for the current SCC.
/// Temporaries introduced by calls/casts/projections therefore do not inflate
/// the estimate.
fn estimate_dataflow_backedges(
    dependencies: &LocalDependencyIndex,
    roots: &FxHashSet<Local>,
    local_summary: &LoopLocalSummary,
) -> Option<usize> {
    let mut best_state_distance = 0usize;
    for root in roots {
        let mut visited = FxHashSet::default();
        best_state_distance = best_state_distance.max(max_state_distance_from(
            dependencies,
            *root,
            local_summary,
            0,
            &mut visited,
        ));
    }

    if best_state_distance == 0 {
        None
    } else {
        Some(best_state_distance)
    }
}

/// DFS over dependency edges, counting only loop-carried state locals.
fn max_state_distance_from(
    dependencies: &LocalDependencyIndex,
    local: Local,
    local_summary: &LoopLocalSummary,
    distance: usize,
    visited: &mut FxHashSet<Local>,
) -> usize {
    if !visited.insert(local) {
        return distance;
    }

    let mut best = distance;
    if let Some(sources) = dependencies.sources_by_dest.get(&local) {
        for source in sources {
            let next_distance = distance + usize::from(local_summary.state_locals.contains(source));
            let mut branch_visited = visited.clone();
            best = best.max(max_state_distance_from(
                dependencies,
                *source,
                local_summary,
                next_distance,
                &mut branch_visited,
            ));
        }
    }
    best
}

/// Return true for properties whose proof obligation is fundamentally numeric
/// or index-range based.
fn is_numeric_range_property(kind: &PropertyKind) -> bool {
    matches!(kind, PropertyKind::ValidNum | PropertyKind::InBound)
}

/// Estimate the first violating iteration for a simple `ValidNum` sink.
fn estimate_valid_num_witness(
    property: &Property<'_>,
    root_closure: &FxHashSet<Local>,
    numeric_summary: &LoopNumericSummary,
) -> Option<usize> {
    let violation_value = valid_num_violation_value(property)?;
    root_closure
        .iter()
        .filter_map(|local| {
            let init = numeric_summary.initial_constants.get(local).copied()?;
            let step = numeric_summary.steps.get(local).copied()?;
            witness_iteration_for_threshold(init, step, violation_value)
        })
        .min()
}

/// Estimate an index-range witness for `InBound`.
///
/// The current implementation recognizes that a checked pointer/index depends
/// on an induction variable.  It returns the first loop-body count that is not
/// covered by `--postfix-repeat 1`; a later affine summary can replace this
/// fallback with a symbolic `i in [0, len)` proof and a concrete witness.
fn estimate_inbound_witness(
    root_closure: &FxHashSet<Local>,
    numeric_summary: &LoopNumericSummary,
) -> Option<usize> {
    let mut fallback = false;
    let mut best = None;

    for local in root_closure {
        let Some(init) = numeric_summary.initial_constants.get(local).copied() else {
            continue;
        };
        let Some(step) = numeric_summary.steps.get(local).copied() else {
            continue;
        };
        if step == 0 {
            continue;
        }
        fallback = true;

        let Some(guard_bound) = numeric_summary.guard_upper_bounds.get(local).copied() else {
            continue;
        };
        let Some(bound_lower) = numeric_term_lower_bound(guard_bound, numeric_summary) else {
            continue;
        };
        let Some(witness) = witness_iteration_for_threshold(init, step, bound_lower) else {
            continue;
        };
        best = Some(best.map_or(witness, |current: usize| current.min(witness)));
    }

    best.or_else(|| fallback.then_some(DEFAULT_NUMERIC_WITNESS_ITERATION))
}

/// Extract the lowest value that violates a simple upper-bound `ValidNum`.
fn valid_num_violation_value(property: &Property<'_>) -> Option<i128> {
    if !matches!(property.kind, PropertyKind::ValidNum) {
        return None;
    }
    let Some(PropertyArg::Predicates(predicates)) = property.args.first() else {
        return None;
    };
    predicates
        .iter()
        .filter_map(simple_upper_bound_violation_value)
        .min()
}

/// Match `x < C`, `x <= C`, and their constant-on-left equivalents.
fn simple_upper_bound_violation_value(predicate: &NumericPredicate<'_>) -> Option<i128> {
    match (&predicate.lhs, predicate.op, &predicate.rhs) {
        (lhs, RelOp::Lt, rhs) if expr_is_place(lhs) => expr_const_i128(rhs),
        (lhs, RelOp::Le, rhs) if expr_is_place(lhs) => expr_const_i128(rhs)?.checked_add(1),
        (lhs, RelOp::Gt, rhs) if expr_is_place(rhs) => expr_const_i128(lhs),
        (lhs, RelOp::Ge, rhs) if expr_is_place(rhs) => expr_const_i128(lhs)?.checked_add(1),
        _ => None,
    }
}

/// Return true when a contract expression is a plain numeric place.
fn expr_is_place(expr: &ContractExpr<'_>) -> bool {
    matches!(expr, ContractExpr::Place(_))
}

/// Extract a contract integer constant small enough for the planner model.
fn expr_const_i128(expr: &ContractExpr<'_>) -> Option<i128> {
    match expr {
        ContractExpr::Const(value) if *value <= i128::MAX as u128 => Some(*value as i128),
        _ => None,
    }
}

/// Resolve a known lower bound for a numeric term.
fn numeric_term_lower_bound(term: NumericTerm, summary: &LoopNumericSummary) -> Option<i128> {
    match term {
        NumericTerm::Const(value) => Some(value),
        NumericTerm::Local(local) => summary.entry_lower_bounds.get(&local).copied(),
    }
}

/// Compute the first 1-based iteration where `init + step * iteration` reaches
/// `violation_value`.
fn witness_iteration_for_threshold(init: i128, step: i128, violation_value: i128) -> Option<usize> {
    if step <= 0 {
        return None;
    }
    if init >= violation_value {
        return Some(0);
    }
    let delta = violation_value.checked_sub(init)?;
    usize::try_from(ceil_div_i128(delta, step)).ok()
}

/// Integer ceil-div for positive operands.
fn ceil_div_i128(lhs: i128, rhs: i128) -> i128 {
    debug_assert!(lhs >= 0);
    debug_assert!(rhs > 0);
    (lhs + rhs - 1) / rhs
}

/// Return true if `local` is a function argument local.
fn local_is_argument(local: Local, body: &Body<'_>) -> bool {
    let index = local.as_usize();
    index > 0 && index <= body.arg_count
}

/// Extract a direct constant assignment from an rvalue.
fn rvalue_const_i128<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    rvalue: &Rvalue<'tcx>,
) -> Option<i128> {
    match rvalue {
        Rvalue::Use(operand, ..) | Rvalue::Cast(_, operand, _) => {
            operand_const_i128(tcx, def_id, operand)
        }
        _ => None,
    }
}

/// Return the source local for a plain local copy/move rvalue.
fn plain_copy_source(rvalue: &Rvalue<'_>) -> Option<Local> {
    let Rvalue::Use(Operand::Copy(place) | Operand::Move(place), ..) = rvalue else {
        return None;
    };
    place.projection.is_empty().then_some(place.local)
}

/// Extract a simple comparison from an rvalue.
fn comparison_fact<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    rvalue: &Rvalue<'tcx>,
) -> Option<ComparisonFact> {
    let Rvalue::BinaryOp(op, operands) = rvalue else {
        return None;
    };
    if !matches!(
        op,
        BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::Eq | BinOp::Ne
    ) {
        return None;
    }
    Some(ComparisonFact {
        op: *op,
        lhs: numeric_term_from_operand(tcx, def_id, &operands.0)?,
        rhs: numeric_term_from_operand(tcx, def_id, &operands.1)?,
    })
}

/// Convert a MIR operand into the planner's small numeric term language.
fn numeric_term_from_operand<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    operand: &Operand<'tcx>,
) -> Option<NumericTerm> {
    operand_plain_local(operand)
        .map(NumericTerm::Local)
        .or_else(|| operand_const_i128(tcx, def_id, operand).map(NumericTerm::Const))
}

/// Follow plain copy chains for a local.
fn resolve_local_copy(local: Local, copy_sources: &FxHashMap<Local, Local>) -> Local {
    let mut current = local;
    let mut seen = FxHashSet::default();
    while seen.insert(current) {
        let Some(next) = copy_sources.get(&current).copied() else {
            break;
        };
        current = next;
    }
    current
}

/// Follow copy chains inside a numeric term.
fn resolve_numeric_term(term: NumericTerm, copy_sources: &FxHashMap<Local, Local>) -> NumericTerm {
    match term {
        NumericTerm::Local(local) => NumericTerm::Local(resolve_local_copy(local, copy_sources)),
        NumericTerm::Const(value) => NumericTerm::Const(value),
    }
}

/// Extract `local +/- const` from an arithmetic rvalue.
fn increment_source_and_step<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    rvalue: &Rvalue<'tcx>,
) -> Option<(Local, i128)> {
    let Rvalue::BinaryOp(op, operands) = rvalue else {
        return None;
    };
    let lhs_local = operand_plain_local(&operands.0);
    let rhs_local = operand_plain_local(&operands.1);
    let lhs_const = operand_const_i128(tcx, def_id, &operands.0);
    let rhs_const = operand_const_i128(tcx, def_id, &operands.1);

    match op {
        BinOp::Add | BinOp::AddWithOverflow | BinOp::AddUnchecked => match (lhs_local, rhs_local) {
            (Some(local), None) => Some((local, rhs_const?)),
            (None, Some(local)) => Some((local, lhs_const?)),
            _ => None,
        },
        BinOp::Sub | BinOp::SubWithOverflow | BinOp::SubUnchecked => match (lhs_local, rhs_const) {
            (Some(local), Some(value)) => Some((local, -value)),
            _ => None,
        },
        _ => None,
    }
}

/// Return the source temp for `tmp.field_index`.
fn rvalue_projection_source(rvalue: &Rvalue<'_>, field_index: usize) -> Option<Local> {
    let Rvalue::Use(Operand::Copy(place) | Operand::Move(place), ..) = rvalue else {
        return None;
    };
    (first_field_projection(place) == Some(field_index)).then_some(place.local)
}

/// Return the local used by an operand when the operand is a plain local place.
fn operand_plain_local(operand: &Operand<'_>) -> Option<Local> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
            Some(place.local)
        }
        Operand::Copy(_) | Operand::Move(_) | Operand::Constant(_) => None,
        #[cfg(rapx_rustc_ge_196)]
        Operand::RuntimeChecks(_) => None,
    }
}

/// Extract an integer constant from an operand.
fn operand_const_i128<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    operand: &Operand<'tcx>,
) -> Option<i128> {
    let Operand::Constant(constant) = operand else {
        return None;
    };
    let typing_env = TypingEnv::post_analysis(tcx, def_id);
    match constant.const_.ty().kind() {
        TyKind::Bool => constant
            .const_
            .try_eval_bool(tcx, typing_env)
            .map(|value| if value { 1 } else { 0 }),
        TyKind::Int(_) | TyKind::Uint(_) => constant
            .const_
            .try_eval_bits(tcx, typing_env)
            .and_then(|bits| {
                if bits <= i128::MAX as u128 {
                    Some(bits as i128)
                } else {
                    None
                }
            }),
        _ => None,
    }
}

/// Return the first field projected from a place.
fn first_field_projection(place: &Place<'_>) -> Option<usize> {
    for projection in place.projection.iter() {
        if let ProjectionElem::Field(field, _) = projection {
            return Some(field.as_usize());
        }
    }
    None
}

/// Whole-function local dependency index.
///
/// The map is intentionally directioned from destination to source:
/// `sources_by_dest[x] = {y, z}` means the value of local `x` may have been
/// assigned from `y` or `z`.  Starting from a sink root, a reverse closure over
/// this map finds all locals that may flow into the checked argument.
struct LocalDependencyIndex {
    sources_by_dest: FxHashMap<Local, FxHashSet<Local>>,
}

impl LocalDependencyIndex {
    /// Build dependency edges from MIR assignments and call arguments.
    ///
    /// Calls are approximated by connecting their destination to all argument
    /// locals.  That is coarse but useful for wrappers such as
    /// `ptr.wrapping_add(offset)`: the resulting pointer local depends on both
    /// the base pointer and the offset local.
    fn new(tcx: TyCtxt<'_>, def_id: DefId) -> Self {
        let body = tcx.optimized_mir(def_id);
        let mut sources_by_dest: FxHashMap<Local, FxHashSet<Local>> = FxHashMap::default();

        for data in body.basic_blocks.iter() {
            for statement in &data.statements {
                let StatementKind::Assign(assign) = &statement.kind else {
                    continue;
                };
                let (place, rvalue) = &**assign;
                if place_is_indirect_write(place) {
                    continue;
                }
                let mut sources = FxHashSet::default();
                collect_rvalue_sources(rvalue, &mut sources);
                if !sources.is_empty() {
                    sources_by_dest
                        .entry(place.local)
                        .or_default()
                        .extend(sources);
                }
            }

            if let TerminatorKind::Call {
                args, destination, ..
            } = &data.terminator().kind
            {
                let mut sources = FxHashSet::default();
                for arg in args {
                    collect_operand_sources(&arg.node, &mut sources);
                }
                if !sources.is_empty() {
                    sources_by_dest
                        .entry(destination.local)
                        .or_default()
                        .extend(sources);
                }
            }
        }

        Self { sources_by_dest }
    }

    /// Compute all locals that may flow into `roots`.
    ///
    /// This deliberately ignores statement order; the planner only decides
    /// whether extra loop depth may be useful.  The ordinary verifier remains
    /// responsible for path-ordered proof or failure once the deeper paths are
    /// enumerated.
    fn closure_from(&self, roots: &FxHashSet<Local>) -> FxHashSet<Local> {
        let mut closure = FxHashSet::default();
        let mut stack: Vec<Local> = roots.iter().copied().collect();
        while let Some(local) = stack.pop() {
            if !closure.insert(local) {
                continue;
            }
            if let Some(sources) = self.sources_by_dest.get(&local) {
                for source in sources {
                    stack.push(*source);
                }
            }
        }
        closure
    }
}

/// Add local operands referenced by an rvalue to `out`.
///
/// This is a shallow syntactic dependency extractor.  It does not try to
/// classify whether the dependency is pointer provenance, numeric dataflow, or
/// a guard value; those distinctions belong in future precise summaries.
fn collect_rvalue_sources(rvalue: &Rvalue<'_>, out: &mut FxHashSet<Local>) {
    match rvalue {
        Rvalue::Use(operand, ..) => collect_operand_sources(operand, out),
        Rvalue::Repeat(operand, _) => collect_operand_sources(operand, out),
        Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) | Rvalue::Discriminant(place) => {
            out.insert(place.local);
        }
        Rvalue::Cast(_, operand, _) | Rvalue::UnaryOp(_, operand) => {
            collect_operand_sources(operand, out);
        }
        Rvalue::BinaryOp(_, operands) => {
            collect_operand_sources(&operands.0, out);
            collect_operand_sources(&operands.1, out);
        }
        Rvalue::Aggregate(_, operands) => {
            for operand in operands {
                collect_operand_sources(operand, out);
            }
        }
        Rvalue::CopyForDeref(place) => {
            out.insert(place.local);
        }
        #[cfg(not(rapx_rustc_ge_196))]
        Rvalue::ShallowInitBox(operand, _) => collect_operand_sources(operand, out),
        Rvalue::ThreadLocalRef(_) | Rvalue::NullaryOp(..) => {}
        _ => {}
    }
}

/// Add the local read by a MIR operand, if any.
fn collect_operand_sources(operand: &Operand<'_>, out: &mut FxHashSet<Local>) {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => {
            out.insert(place.local);
        }
        Operand::Constant(_) => {}
        #[cfg(rapx_rustc_ge_196)]
        Operand::RuntimeChecks(_) => {}
    }
}

/// Return true when an assignment writes through a pointer/reference.
///
/// Such a statement changes memory reachable from a local rather than the local
/// itself, so it is not a local redefinition for this planner.
fn place_is_indirect_write(place: &Place<'_>) -> bool {
    place
        .projection
        .iter()
        .any(|projection| matches!(projection, ProjectionElem::Deref))
}
