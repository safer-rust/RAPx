//! Data types for the path-refinement layer.
//!
//! These structures are produced by the backward visitor and consumed by the
//! forward visitor, engine, and diagnostic formatting.  `ContractFact` is the
//! only variant never produced by the backward visitor itself — it is injected
//! by the engine before the forward visit.

use crate::verify::{
    contract,
    path_extractor::Path,
};
use rustc_hir::def_id::DefId;
use rustc_middle::mir::{BasicBlock, Local};

/// A proof goal for one `(checkpoint, path)` item: the set of relevant items
/// plus the path context needed to verify the target property.
#[derive(Clone, Debug)]
pub struct ProofGoal<'tcx> {
    /// Path being visited; `path.target` identifies the checkpoint.
    pub path: Path,
    /// Items kept from the path.
    pub items: Vec<RelevantItem<'tcx>>,
}

/// One relevant item kept from the backward slice.
#[derive(Clone, Debug)]
pub enum RelevantItem<'tcx> {
    /// A MIR statement retained from a basic block.
    Statement {
        block: BasicBlock,
        statement_index: usize,
    },
    /// A MIR terminator retained from a basic block.
    Terminator { block: BasicBlock },
    /// A contract fact injected by the engine before the forward visit.
    /// Never produced by the backward visitor itself.
    ContractFact { property: contract::Property<'tcx> },
    /// A conservative loss of precision for relevant state (an unsupported
    /// call whose effects are not modeled).
    Forget,
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
