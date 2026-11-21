//! Trait-method and foreign-call postcondition lookup.

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

use super::{Property, attr::collect_properties_from_named_attrs};

pub(crate) fn get_trait_method_ensures<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> Vec<Property<'tcx>> {
    let trait_item_def_id = tcx
        .opt_associated_item(def_id)
        .and_then(|item| item.trait_item_def_id())
        .unwrap_or(def_id);
    if tcx.trait_of_assoc(trait_item_def_id).is_none() {
        return Vec::new();
    }
    let mut ensures = if trait_item_def_id.is_local() {
        collect_properties_from_named_attrs(
            tcx,
            crate::compat::get_all_attrs(tcx, trait_item_def_id),
            trait_item_def_id,
            "trait ensures",
            "ensures",
        )
    } else {
        Vec::new()
    };
    if ensures.is_empty() {
        ensures = super::json::query_trait_method_ensures(tcx, def_id);
    }
    for property in &mut ensures {
        property.set_contract_kind(super::ContractKind::Postcond);
    }
    ensures
}

pub(crate) fn get_call_ensures<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> Vec<Property<'tcx>> {
    if !tcx.is_foreign_item(def_id) {
        return get_trait_method_ensures(tcx, def_id);
    }
    let mut ensures = collect_properties_from_named_attrs(
        tcx,
        crate::compat::get_all_attrs(tcx, def_id),
        def_id,
        "foreign function ensures",
        "ensures",
    );
    for property in &mut ensures {
        property.set_contract_kind(super::ContractKind::Postcond);
    }
    ensures
}

pub(crate) fn has_slice_offset_ensures(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    get_trait_method_ensures(tcx, def_id)
        .iter()
        .any(|property| property.kind() == Some(super::PropertyKind::SliceOffset))
}
