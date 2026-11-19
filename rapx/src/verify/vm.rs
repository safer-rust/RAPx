//! Symbolic VM state and execution rules.

pub(crate) mod alias;
pub(crate) mod alias_hazard;
pub(crate) mod alias_tree;
mod arithmetic;
mod call_contracts;
pub(crate) mod container;
pub(crate) mod contract_eval;
pub(crate) mod contract_facts;
pub(crate) mod contracts;
pub(crate) mod diagnostics;
pub(crate) mod display;
pub(crate) mod exec;
pub(crate) mod inline;
mod iterator;
pub(crate) mod materialize;
pub(crate) mod memory;
pub(crate) mod method_cache;
mod mir_rules;
pub(crate) mod parameters;
pub(crate) mod query;
pub(crate) mod range;
pub(crate) mod region;
pub(crate) mod state;

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{Body, Local},
    ty::TyCtxt,
};
use z3::{Context, ast::Int};

use crate::compat::{FxHashMap, FxHashSet};

use self::{
    diagnostics::Diagnostics,
    method_cache::CachedMethodResult,
    state::{
        AllocId, Constraints, FrameState, InlineCtx, MemoryUnit, OwnershipTransfer,
        SafeDropEventLog, SavedCallerFrame,
    },
};

/// The full symbolic execution state at a program point.
///
/// Accumulates the name → allocation bindings, allocations, and solver
/// constraints as the VM steps through retained MIR items. The Z3 context is
/// borrowed so a single context can be reused across property checks.
#[derive(Clone)]
pub(crate) struct VmState<'z3, 'tcx> {
    /// Function being verified, retained while inlined callee frames execute.
    target_def_id: DefId,
    /// Target MIR instantiated with a selected trait-bound implementor when an
    /// unresolved, unmodeled generic trait call needs a concrete method target.
    /// `None` uses the original optimized MIR, even for generic functions.
    instantiated_target_body: Option<&'tcx Body<'tcx>>,
    /// Shared Z3 context.
    pub(crate) z3_ctx: &'z3 Context,
    /// Compiler type context.
    pub(crate) tcx: TyCtxt<'tcx>,
    /// Currently executing MIR frame and its local allocation bindings.
    pub(crate) current_frame: FrameState<'tcx>,
    /// Caller frames saved by path-replay inlining.
    caller_frames: Vec<SavedCallerFrame<'z3, 'tcx>>,
    /// Allocation units indexed by `AllocId`.
    units: Vec<MemoryUnit<'z3, 'tcx>>,
    /// Ownership transfers shared by copies of the same raw pointer.
    ownership_transfers: Vec<OwnershipTransfer>,
    /// Stable allocation for each static across MIR locals and frames.
    static_allocs: FxHashMap<DefId, AllocId>,
    /// Path conditions and term caches.
    pub(crate) constraints: Constraints<'z3, 'tcx>,
    /// Scratch state for recursive inlining.
    pub(crate) inline: InlineCtx<'z3, 'tcx>,
    /// Stable `&self` results reused by contracts only when the method, caller,
    /// receiver allocation and offset, fields, and slice length still match.
    method_result_cache: Vec<CachedMethodResult<'z3, 'tcx>>,
    /// Allocation roots licensed by declared `Alias` contract sources.
    alias_hazard_allocs: FxHashSet<AllocId>,
    /// Slice and index terms with their originating MIR locals.
    pub(crate) index_access_facts: Vec<(Int<'z3>, Int<'z3>, Local, Local)>,
    /// Optional SafeDrop log of drops, use-after-free, and dangling pointers.
    pub(crate) safedrop_events: SafeDropEventLog,
    /// Path diagnostics and the MIR location used to attribute new records.
    pub(crate) diagnostics: Diagnostics,
}

impl<'z3, 'tcx> VmState<'z3, 'tcx> {
    /// Create a fresh VM state for executing a path.
    pub(crate) fn new(
        z3_ctx: &'z3 Context,
        tcx: TyCtxt<'tcx>,
        target_def_id: DefId,
        instantiated_target_body: Option<&'tcx Body<'tcx>>,
    ) -> Self {
        // The `UNINIT` sentinel is created once and shared by every byte array:
        // an unwritten offset reads it back, so `select != UNINIT` decides
        // whether a byte was written.
        let mut constraints = Constraints::default();
        let uninit = Int::fresh_const(z3_ctx, "uninit_byte");
        constraints.term_caches.uninit_byte = Some(uninit.clone());
        constraints.assertions.push(uninit.ge(&Int::from_u64(z3_ctx, 256)));
        Self {
            target_def_id,
            instantiated_target_body,
            z3_ctx,
            tcx,
            current_frame: FrameState {
                current_def_id: target_def_id,
                instantiated_body: instantiated_target_body,
                local_alloc: FxHashMap::default(),
                pending_enum_fields: FxHashMap::default(),
            },
            caller_frames: Vec::default(),
            units: Vec::default(),
            ownership_transfers: Vec::new(),
            static_allocs: FxHashMap::default(),
            constraints,
            inline: InlineCtx::default(),
            method_result_cache: Vec::default(),
            alias_hazard_allocs: FxHashSet::default(),
            index_access_facts: Vec::new(),
            safedrop_events: SafeDropEventLog::default(),
            diagnostics: Diagnostics::default(),
        }
    }
}
