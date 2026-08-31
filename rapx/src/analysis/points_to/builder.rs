use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, Ty, TyCtxt, TypingEnv};

use crate::analysis::alias::default::types::{is_not_drop, kind};

use super::graph::PtsGraph;
use super::slot::Slot;

const MAX_FIELD_DEPTH: usize = 5;
const MAX_DEREF_DEPTH: usize = 3;

/// Build a PtsGraph from a MIR body, pre-registering all locals and their
/// type-determined field slots up to depth limits.
pub fn from_body<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> PtsGraph {
    let body = tcx.optimized_mir(def_id);
    let mut graph = PtsGraph::new();
    let ty_env = TypingEnv::post_analysis(tcx, def_id);

    for (local, local_decl) in body.local_decls.iter_enumerated() {
        let ty = local_decl.ty;
        let need_drop = ty.needs_drop(tcx, ty_env);
        let may_drop = !is_not_drop(tcx, ty);

        let slot = Slot::new(local.as_usize());
        let slot_idx = graph.ensure_slot(slot.clone(), may_drop, need_drop);
        graph.set_slot_kind(slot_idx, kind(ty));

        register_field_slots(tcx, ty, &slot, slot_idx, &mut graph, 0, 0, ty_env);
    }

    graph
}

// ── Field slot registration ────────────────────────────────────────

fn register_field_slots<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    base_slot: &Slot,
    _base_idx: usize,
    graph: &mut PtsGraph,
    field_depth: usize,
    deref_depth: usize,
    ty_env: TypingEnv<'tcx>,
) {
    if field_depth >= MAX_FIELD_DEPTH || deref_depth >= MAX_DEREF_DEPTH {
        return;
    }

    match ty.kind() {
        ty::Ref(_, inner_ty, _) | ty::RawPtr(inner_ty, _) => {
            register_field_slots(
                tcx,
                *inner_ty,
                base_slot,
                _base_idx,
                graph,
                field_depth,
                deref_depth + 1,
                ty_env,
            );
        }
        ty::Adt(adt_def, substs) => {
            for (field_idx, field) in adt_def.all_fields().enumerate() {
                let field_slot = base_slot.project(field_idx);
                let field_ty = crate::helpers::mir_utils::field_ty(tcx, field, substs);
                let need_drop = field_ty.needs_drop(tcx, ty_env);
                let may_drop = if deref_depth > 0 {
                    true
                } else {
                    !is_not_drop(tcx, field_ty)
                };
                let field_idx_global = graph.ensure_slot(field_slot.clone(), may_drop, need_drop);
                graph.set_slot_kind(field_idx_global, kind(field_ty));
                register_field_slots(
                    tcx,
                    field_ty,
                    &field_slot,
                    field_idx_global,
                    graph,
                    field_depth + 1,
                    deref_depth,
                    ty_env,
                );
            }
        }
        ty::Tuple(fields) => {
            for (field_idx, field_ty) in fields.iter().enumerate() {
                let field_slot = base_slot.project(field_idx);
                let may_drop = if deref_depth > 0 {
                    true
                } else {
                    !is_not_drop(tcx, field_ty)
                };
                let need_drop = field_ty.needs_drop(tcx, ty_env);
                let field_idx_global = graph.ensure_slot(field_slot.clone(), may_drop, need_drop);
                graph.set_slot_kind(field_idx_global, kind(field_ty));
                register_field_slots(
                    tcx,
                    field_ty,
                    &field_slot,
                    field_idx_global,
                    graph,
                    field_depth + 1,
                    deref_depth,
                    ty_env,
                );
            }
        }
        _ => {}
    }
}
