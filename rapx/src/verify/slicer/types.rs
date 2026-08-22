//! Data types for the path-refinement layer.
//!
//! These structures are produced by the backward visitor and consumed by the
//! forward visitor, engine, and diagnostic formatting.  `ContractFact` is the
//! only variant never produced by the backward visitor itself — it is injected
//! by the engine before the forward visit.

use crate::verify::{
    contract,
    def_use::RelevantPlaces,
    path_extractor::{Path, PathStep},
};
use crate::helpers::mir_scan::CheckpointLocation;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::{BasicBlock, Local};

/// A proof goal for one `(checkpoint, path, property)` item: the set of
/// relevant items plus the context needed to verify that property.
#[derive(Clone, Debug)]
pub struct ProofGoal<'tcx> {
    /// Unsafe checkpoint whose obligation is being checked.
    pub checkpoint: CheckpointLocation,
    /// Required property that determines the relevance roots.
    pub property: contract::Property<'tcx>,
    /// Path being visited.
    pub path: Path,
    /// Items kept from the path.
    pub items: Vec<RelevantItem<'tcx>>,
    /// Initial roots extracted from the property.
    pub roots: RelevantPlaces,
}

impl<'tcx> ProofGoal<'tcx> {
    /// Append one kept item to the visited path.
    pub fn push(&mut self, item: RelevantItem<'tcx>) {
        self.items.push(item);
    }

    /// Return true when no MIR/path item has been kept yet.
    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }
}

/// One relevant item kept from the backward slice.
#[derive(Clone, Debug)]
pub enum RelevantItem<'tcx> {
    /// A MIR statement retained from a basic block.
    Statement {
        block: BasicBlock,
        statement_index: usize,
        kind: KeepReason,
    },
    /// A MIR terminator retained from a basic block.
    Terminator { block: BasicBlock, kind: KeepReason },
    /// A path-level step retained as structural context.
    PathStep { step: PathStep, kind: KeepReason },
    /// A contract fact injected by the engine before the forward visit.
    /// Never produced by the backward visitor itself.
    ContractFact { property: contract::Property<'tcx> },
    /// A conservative loss of precision for relevant state.
    Forget { reason: ForgetReason },
    /// Enter a callee's MIR body. Subsequent Statement/Terminator items
    /// are interpreted in the callee's context until `CalleeExit`.
    /// `args` holds the caller's Local indices for each callee parameter
    /// (arg 0 → callee local_1, arg 1 → callee local_2, ...).
    CalleeEntry {
        callee: DefId,
        args: Vec<Local>,
    },
    /// Return from a callee's MIR body. Writes `local_0` (callee return)
    /// to the caller's `dest` local. Restores the caller's function context.
    CalleeExit {
        dest: Local,
    },
}

/// Why a retained item is relevant.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum KeepReason {
    /// The item defines a relevant place.
    Definition,
    /// The item contributes a branch/path condition.
    PathCondition,
    /// The item contributes pointer provenance or pointer arithmetic.
    PointerFlow,
    /// The item refines state through a runtime check.
    RuntimeCheck,
    /// The item is the unsafe checkpoint being checked.
    Checkpoint,
    /// The item represents a loop summary or loop exit.
    LoopExit,
    /// The item may invalidate a relevant fact.
    Invalidation,
    /// The item may affect relevant state but is not modeled precisely yet.
    UnknownEffect,
}

/// Reason for conservatively forgetting relevant state.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ForgetReason {
    /// A call may modify relevant state but has no summary yet.
    UnknownCall,
    /// An unsupported call that can only mutate *contents* reachable through
    /// its reference arguments — it takes no raw pointers and no concrete
    /// owning containers, so it cannot change any slice's length or base
    /// address, reallocate, or free memory.  Such a call invalidates
    /// content facts (Init) but leaves address/length/layout facts intact.
    OpaqueContentCall,
    /// An SCC region may modify relevant state but has no summary yet.
    SccWithoutSummary,
    /// A write may alias relevant state.
    MayAliasWrite,
    /// A relevant statement or terminator is not supported yet.
    UnsupportedEffect,
}
