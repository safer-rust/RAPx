//! Recognize raw pointers that retain or reconstruct shared ownership.

use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::ty::{TyCtxt, TyKind, TypingEnv};

use super::pointer_flow::{return_source_arg, single_block_without_effects};

pub(crate) fn shared_raw_owner_type(tcx: TyCtxt<'_>, callee: DefId) -> Option<DefId> {
    if !matches!(tcx.def_kind(callee), DefKind::Fn | DefKind::AssocFn) {
        return None;
    }
    let arg = return_source_arg(tcx, callee)?;
    if !single_block_without_effects(tcx.optimized_mir(callee)) {
        return None;
    }
    let inputs = tcx.fn_sig(callee).skip_binder().inputs().skip_binder();
    let ty = *inputs.get(arg)?;
    let TyKind::Adt(adt, _) = ty.kind() else {
        return None;
    };
    if !has_ref_count_share_reconstruction(tcx, adt.did()) {
        return None;
    }
    ty.needs_drop(tcx, TypingEnv::non_body_analysis(tcx, callee))
        .then_some(adt.did())
}

pub(crate) fn has_ref_count_share_reconstruction(tcx: TyCtxt<'_>, owner: DefId) -> bool {
    tcx.inherent_impls(owner).iter().any(|impl_id| {
        tcx.associated_item_def_ids(*impl_id).iter().any(|item| {
            matches!(tcx.def_kind(*item), DefKind::Fn | DefKind::AssocFn)
                && crate::verify::contract::json::query_json_contracts(tcx, *item)
                    .iter()
                    .any(|property| {
                        property.kind()
                            == Some(crate::verify::contract::PropertyKind::RefCountShare)
                    })
                && crate::verify::vm::alias_hazard::reconstructed_owner(tcx, *item)
                    .is_some_and(|(_, reconstructed)| reconstructed == owner)
        })
    })
}
