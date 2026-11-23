//! Property-independent MIR effects used by backward slicing.

use std::ops::Deref;

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{Body, Local, Operand, StatementKind, TerminatorKind},
    ty::{Ty, TyCtxt, TypeFlags, TypeVisitableExt, TypingEnv},
};

use crate::compat::FxHashMap;
use crate::contract::{PropertyKind, json::query_json_contracts};
use crate::def_ids::other_api;
use crate::util::mir_utils::dep_callee_def_id;

use super::{DataflowGraph, graph::build_dataflow_graph_from_body};

/// Effects of one MIR operation on state needed by a proof obligation.
#[derive(Clone, Copy, Default)]
pub(crate) struct MirEffects {
    /// An operation that changes the memory state relevant to lifetime checks.
    pub(crate) memory_state: bool,
    /// A definition of a `needs_drop` value retained for owner provenance.
    pub(crate) owner_source: bool,
}

/// Value flow plus effect definitions, constructed once for each selected MIR body.
pub(crate) struct SlicingGraph {
    flow: DataflowGraph,
    effects: FxHashMap<(usize, usize), MirEffects>,
}

impl SlicingGraph {
    pub(crate) fn new<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, body: &Body<'tcx>) -> Self {
        let flow = build_dataflow_graph_from_body(def_id, body);
        let mut effects = FxHashMap::default();
        for (block_index, block) in body.basic_blocks.iter().enumerate() {
            for (stmt_index, statement) in block.statements.iter().enumerate() {
                let effect = match &statement.kind {
                    StatementKind::StorageLive(..) | StatementKind::StorageDead(..) =>
                        MirEffects { memory_state: true, ..Default::default() },
                    StatementKind::Assign(assign) => MirEffects {
                        owner_source: may_need_drop(tcx, def_id, body.local_decls[assign.0.local].ty),
                        ..Default::default()
                    },
                    _ => MirEffects::default(),
                };
                if effect.memory_state || effect.owner_source {
                    effects.insert((block_index, stmt_index), effect);
                }
            }
            let Some(terminator) = &block.terminator else { continue };
            let effect = match &terminator.kind {
                TerminatorKind::Drop { .. } => MirEffects { memory_state: true, ..Default::default() },
                TerminatorKind::Call { func, destination, .. } => MirEffects {
                    memory_state: call_changes_memory_state(tcx, func),
                    owner_source: may_need_drop(tcx, def_id, body.local_decls[destination.local].ty),
                },
                TerminatorKind::TailCall { func, .. } => MirEffects {
                    memory_state: call_changes_memory_state(tcx, func),
                    owner_source: may_need_drop(tcx, def_id, body.local_decls[Local::from_usize(0)].ty),
                },
                _ => MirEffects::default(),
            };
            if effect.memory_state || effect.owner_source {
                effects.insert((block_index, block.statements.len()), effect);
            }
        }
        Self { flow, effects }
    }

    pub(crate) fn effects_at(&self, block: usize, stmt_index: usize) -> MirEffects {
        self.effects.get(&(block, stmt_index)).copied().unwrap_or_default()
    }
}

impl Deref for SlicingGraph {
    type Target = DataflowGraph;

    fn deref(&self) -> &Self::Target { &self.flow }
}

fn may_need_drop<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, ty: Ty<'tcx>) -> bool {
    // Generic consts and placeholders can make rustc's `needs_drop` query fail.
    ty.has_type_flags(TypeFlags::HAS_CT_PARAM)
        || ty.has_non_region_placeholders()
        || ty.has_escaping_bound_vars()
        || ty.needs_drop(tcx, TypingEnv::post_analysis(tcx, def_id))
}

fn call_changes_memory_state(tcx: TyCtxt<'_>, func: &Operand<'_>) -> bool {
    dep_callee_def_id(func).is_some_and(|callee| {
        other_api::is_drop_fn(tcx, callee)
            || query_json_contracts(tcx, callee).iter().any(|property| property.kind() == Some(PropertyKind::RefCountShare))
    })
}
