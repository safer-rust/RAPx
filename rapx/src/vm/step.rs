//! MIR items retained by the backward slicer for VM execution.

use crate::contract;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::{BasicBlock, Body};

/// One relevant item kept from the backward slice.
#[derive(Clone, Debug)]
pub(crate) enum RelevantItem<'tcx> {
    /// A MIR statement retained from a basic block. `def_id` identifies the
    /// function owning `block` (differs from the caller for inlined callees).
    Statement {
        def_id: DefId,
        block: BasicBlock,
        global_block: Option<usize>,
        stmt_index: usize,
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
    /// Enter an inlined callee: bind each argument to its parameter position.
    CalleeEntry {
        callee: DefId,
        body: Option<&'tcx Body<'tcx>>,
        args: Vec<crate::analysis::path::CallArg>,
    },
    /// Return from an inlined callee: write the callee's `_0` to the caller's
    /// destination local.
    CalleeExit { dest: usize },
    /// A contract fact injected by the function verifier before VM execution.
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
