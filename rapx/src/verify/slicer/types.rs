//! Data types for the path-refinement layer.
//!
//! These structures are produced by the backward visitor and consumed by the
//! forward visitor, engine, and diagnostic formatting.  `ContractFact` is the
//! only variant never produced by the backward visitor itself — it is injected
//! by the engine before the forward visit.

use crate::verify::{contract, path_extractor::Path};
use rustc_hir::def_id::DefId;
use rustc_middle::mir::BasicBlock;
use rustc_middle::mir::Body;

/// A proof goal for one `(checkpoint, path)` item: the set of relevant items
/// plus the path context needed to verify the target property.
#[derive(Clone, Debug)]
pub(crate) struct ProofGoal<'tcx> {
    /// Path being visited; `path.target` identifies the checkpoint.
    pub path: Path,
    /// Items kept from the path.
    pub items: Vec<RelevantItem<'tcx>>,
}

/// One relevant item kept from the backward slice.
#[derive(Clone, Debug)]
pub(crate) enum RelevantItem<'tcx> {
    /// A MIR statement retained from a basic block. `def_id` identifies the
    /// function owning `block` (differs from the caller for inlined callees).
    Statement {
        def_id: DefId,
        block: BasicBlock,
        global_block: Option<usize>,
        statement_index: usize,
    },
    /// A MIR terminator retained from a basic block.  For a `SwitchInt`, `block`
    /// is the switch block and `switch_succ` is the successor taken along this
    /// path (so the VM need not re-resolve it from the path); for any other
    /// terminator — or when the path ends at the checkpoint — `switch_succ` is
    /// `None`.
    Terminator {
        def_id: DefId,
        block: BasicBlock,
        global_block: Option<usize>,
        switch_succ: Option<BasicBlock>,
    },
    /// Enter an inlined callee: bind the caller's argument locals to the callee
    /// parameters. `args` holds the caller's argument local indices; `consts`
    /// holds `(param, value)` for `Const` arguments with no local;
    /// `field_offsets` holds callee parameters bound to an `offset_of!` const.
    CalleeEntry {
        callee: DefId,
        body: Option<&'tcx Body<'tcx>>,
        args: Vec<usize>,
        consts: Vec<(usize, crate::analysis::path::CallConstArg)>,
        field_offsets: Vec<usize>,
    },
    /// Return from an inlined callee: write the callee's `_0` to the caller's
    /// destination local.
    CalleeExit { dest: usize },
    /// A contract fact injected by the engine before the forward visit.
    /// Never produced by the backward visitor itself.
    ContractFact { property: contract::Property<'tcx> },
}

impl RelevantItem<'_> {
    pub(crate) fn set_global_block(&mut self, global_block: usize) {
        match self {
            Self::Statement {
                global_block: slot, ..
            }
            | Self::Terminator {
                global_block: slot, ..
            } => *slot = Some(global_block),
            _ => {}
        }
    }
}
