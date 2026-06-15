//! Data types for the path-refinement layer.
//!
//! These structures are produced by the backward visitor and consumed by the
//! forward visitor, engine, and diagnostic formatting.  `ContractFact` is the
//! only variant never produced by the backward visitor itself — it is injected
//! by the engine before the forward visit.

use crate::verify::{
    contract,
    def_use::RelevantPlaces,
    helpers::CallsiteLocation,
    path::{Path, PathStep},
};
use rustc_middle::mir::BasicBlock;

/// MIR items relevant to one `(callsite, path, property)` item.
#[derive(Clone, Debug)]
pub struct RelevantMirItems<'tcx> {
    /// Unsafe callsite whose obligation is being checked.
    pub callsite: CallsiteLocation,
    /// Required property that determines the relevance roots.
    pub property: contract::Property<'tcx>,
    /// Path being visited.
    pub path: Path,
    /// Items kept from the path.
    pub items: Vec<BackwardItem<'tcx>>,
    /// Initial roots extracted from the property.
    pub roots: RelevantPlaces,
}

impl<'tcx> RelevantMirItems<'tcx> {
    /// Append one kept item to the visited path.
    pub fn push(&mut self, item: BackwardItem<'tcx>) {
        self.items.push(item);
    }

    /// Return true when no MIR/path item has been kept yet.
    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }
}

/// One item kept while walking a path backward.
#[derive(Clone, Debug)]
pub enum BackwardItem<'tcx> {
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
    /// The item is the unsafe callsite being checked.
    Callsite,
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
    /// An SCC region may modify relevant state but has no summary yet.
    SccWithoutSummary,
    /// A write may alias relevant state.
    MayAliasWrite,
    /// A relevant statement or terminator is not supported yet.
    UnsupportedEffect,
}
