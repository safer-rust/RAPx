//! Data types for the path-refinement layer.
//!
//! These structures are produced by the backward visitor and consumed by the
//! forward visitor, engine, and diagnostic formatting.  `ContractFact` is the
//! only variant never produced by the backward visitor itself — it is injected
//! by the engine before the forward visit.

use crate::verify::{contract, path_extractor::Path};
use rustc_hir::def_id::DefId;
use rustc_middle::mir::BasicBlock;

/// A proof goal for one `(checkpoint, path)` item: the set of relevant items
/// plus the path context needed to verify the target property.
#[derive(Clone, Debug)]
pub(crate) struct ProofGoal<'tcx> {
    /// Path being visited; `path.target` identifies the checkpoint.
    pub path: Path,
    /// Items kept from the path.
    pub items: Vec<RelevantItem<'tcx>>,
    /// Per-global-block function ownership `(def_id, local_index)`, populated
    /// for inlined multi-function paths. Empty for single-function goals.
    pub block_fn: Vec<(DefId, usize)>,
}

/// One relevant item kept from the backward slice.
#[derive(Clone, Debug)]
pub(crate) enum RelevantItem<'tcx> {
    /// A MIR statement retained from a basic block. `def_id` identifies the
    /// function owning `block` (differs from the caller for inlined callees).
    Statement {
        def_id: DefId,
        block: BasicBlock,
        statement_index: usize,
    },
    /// A MIR terminator retained from a basic block.
    Terminator { def_id: DefId, block: BasicBlock },
    /// Enter an inlined callee: bind the caller's argument locals to the callee
    /// parameters. `args` holds the caller's argument local indices.
    CalleeEntry { callee: DefId, args: Vec<usize> },
    /// Return from an inlined callee: write the callee's `_0` to the caller's
    /// destination local.
    CalleeExit { dest: usize },
    /// A contract fact injected by the engine before the forward visit.
    /// Never produced by the backward visitor itself.
    ContractFact { property: contract::Property<'tcx> },
    /// A conservative loss of precision for relevant state (an unsupported
    /// call whose effects are not modeled).
    Forget,
}
