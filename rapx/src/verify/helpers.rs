use rustc_abi::FieldIdx;
use rustc_hir::{
    ItemKind,
    def_id::{DefId, LocalDefId},
};
use rustc_middle::{
    mir::{BasicBlock, TerminatorKind},
    ty::{ConstKind, GenericArgKind, Ty, TyCtxt, TyKind},
};
use rustc_span::Symbol;
use syn::Expr;

use crate::helpers::fn_info::{FnKind, get_type};

pub use crate::helpers::fn_info::parse_expr_into_number;
pub use crate::helpers::mir_scan::{
    Checkpoint, CheckpointKind, CheckpointLocation, collect_unsafe_callsites,
};
pub use crate::helpers::name::{
    access_ident_recursive, get_cleaned_def_path_name, get_struct_self_ty, match_ty_with_ident,
    parse_signature,
};

/// Collect all return basic block indices for a function body.
pub fn collect_return_block_indices(tcx: TyCtxt<'_>, def_id: DefId) -> Vec<BasicBlock> {
    let mut blocks = Vec::new();
    if !tcx.is_mir_available(def_id) {
        return blocks;
    }
    let body = tcx.optimized_mir(def_id);
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        if matches!(data.terminator().kind, TerminatorKind::Return) {
            blocks.push(bb);
        }
    }
    blocks
}

pub fn parse_expr_into_local_and_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    expr: &Expr,
) -> Option<(usize, Vec<(usize, Ty<'tcx>)>, Ty<'tcx>)> {
    if let Some((base_ident, fields)) = access_ident_recursive(expr) {
        let (param_names, param_tys) = parse_signature(tcx, def_id);
        if param_names[0] != "0" {
            if let Some(param_index) = param_names.iter().position(|name| name == &base_ident) {
                return resolve_projection_from_base_ident(
                    tcx,
                    base_ident,
                    fields,
                    param_index + 1,
                    param_tys[param_index],
                );
            }
        }

        if let Some(struct_ty) = get_struct_self_ty(tcx, def_id) {
            return resolve_projection_from_struct_ident(
                tcx, def_id, base_ident, fields, struct_ty,
            );
        }
    }
    None
}

/// Return the callee argument index represented by a MIR local.
///
/// Contract annotations written with parameter names are parsed in the callee's
/// local namespace.  MIR local `_0` is the return place and argument locals are
/// `_1..=_arg_count`, so callee local `_1` denotes checkpoint argument `0`.
pub fn callee_param_index_for_local(tcx: TyCtxt<'_>, callee: DefId, local: usize) -> Option<usize> {
    if local == 0 {
        return None;
    }

    let arg_count = if tcx.is_mir_available(callee) {
        tcx.optimized_mir(callee).arg_count
    } else {
        tcx.fn_sig(callee)
            .skip_binder()
            .inputs()
            .skip_binder()
            .len()
    };

    (local <= arg_count).then_some(local - 1)
}

pub fn is_std_crate_def_id(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    matches!(
        tcx.crate_name(def_id.krate).as_str(),
        "core" | "std" | "alloc"
    )
}

pub fn is_trait_unsafe(tcx: TyCtxt<'_>, trait_def_id: DefId) -> bool {
    let Some(local_id) = trait_def_id.as_local() else {
        return false;
    };
    let item = tcx.hir_expect_item(local_id);

    #[cfg(not(rapx_rustc_ge_198))]
    if let ItemKind::Trait(_, _, unsafety, _, _, _, _) = &item.kind {
        return matches!(unsafety, rustc_hir::Safety::Unsafe);
    }
    #[cfg(rapx_rustc_ge_198)]
    if let ItemKind::Trait { safety, .. } = &item.kind {
        return matches!(safety, rustc_hir::Safety::Unsafe);
    }

    false
}

pub fn resolve_impl_self_ty_def_id(item: &rustc_hir::Item<'_>) -> Option<DefId> {
    let ItemKind::Impl(rustc_hir::Impl { self_ty, .. }) = &item.kind else {
        return None;
    };
    match &self_ty.kind {
        rustc_hir::TyKind::Path(rustc_hir::QPath::Resolved(_, path)) => match path.res {
            rustc_hir::def::Res::Def(
                rustc_hir::def::DefKind::Struct
                | rustc_hir::def::DefKind::Enum
                | rustc_hir::def::DefKind::Union,
                def_id,
            ) => Some(def_id),
            _ => None,
        },
        _ => None,
    }
}

pub fn has_rapx_verify_attr(tcx: TyCtxt<'_>, def_id: LocalDefId) -> bool {
    let hir_id = tcx.local_def_id_to_hir_id(def_id);

    let rapx = Symbol::intern("rapx");
    let verify = Symbol::intern("verify");

    let attrs = tcx.hir_attrs(hir_id);

    attrs.iter().any(|attr| {
        #[cfg(rapx_rustc_ge_193)]
        if attr.is_doc_comment().is_some() {
            return false;
        }
        #[cfg(not(rapx_rustc_ge_193))]
        if attr.is_doc_comment() {
            return false;
        }

        let path = attr.path();

        path.len() == 2 && path[0] == rapx && path[1] == verify
    })
}

pub fn get_owner_struct_def_id(tcx: TyCtxt<'_>, def_id: DefId) -> Option<DefId> {
    let assoc_item = tcx.opt_associated_item(def_id)?;
    let impl_id = assoc_item.impl_container(tcx)?;
    let self_ty = tcx.type_of(impl_id).skip_binder();

    match self_ty.kind() {
        TyKind::Adt(adt_def, _) => Some(adt_def.did()),
        _ => None,
    }
}

fn resolve_projection_from_base_ident<'tcx>(
    tcx: TyCtxt<'tcx>,
    base_ident: String,
    fields: Vec<String>,
    base_local: usize,
    base_ty: Ty<'tcx>,
) -> Option<(usize, Vec<(usize, Ty<'tcx>)>, Ty<'tcx>)> {
    let mut current_ty = base_ty;
    let mut field_indices = Vec::new();
    for field_name in fields {
        let Some((field_idx, field_ty)) = resolve_next_field(tcx, current_ty, &field_name) else {
            return if field_indices.is_empty() && base_ident.is_empty() {
                None
            } else {
                None
            };
        };
        current_ty = field_ty;
        field_indices.push((field_idx, current_ty));
    }
    Some((base_local, field_indices, current_ty))
}

fn resolve_projection_from_struct_ident<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    base_ident: String,
    fields: Vec<String>,
    struct_ty: Ty<'tcx>,
) -> Option<(usize, Vec<(usize, Ty<'tcx>)>, Ty<'tcx>)> {
    let Some((field_idx, field_ty)) = resolve_next_field(tcx, struct_ty, &base_ident) else {
        return None;
    };

    let mut current_ty = field_ty;
    let mut field_indices = vec![(field_idx, current_ty)];
    for field_name in fields {
        let Some((next_field_idx, next_field_ty)) =
            resolve_next_field(tcx, current_ty, &field_name)
        else {
            return None;
        };
        current_ty = next_field_ty;
        field_indices.push((next_field_idx, current_ty));
    }

    let base_local = if get_type(tcx, def_id) == FnKind::Constructor {
        0
    } else {
        1
    };

    Some((base_local, field_indices, current_ty))
}

fn resolve_next_field<'tcx>(
    tcx: TyCtxt<'tcx>,
    base_ty: Ty<'tcx>,
    field_name: &str,
) -> Option<(usize, Ty<'tcx>)> {
    let peeled_ty = base_ty.peel_refs();
    if let TyKind::Adt(adt_def, arg_list) = *peeled_ty.kind() {
        if !adt_def.is_struct() && !adt_def.is_union() {
            return None;
        }
        let variant = adt_def.non_enum_variant();
        if let Ok(field_idx) = field_name.parse::<usize>() {
            if field_idx < variant.fields.len() {
                #[cfg(not(rapx_rustc_ge_198))]
                let field_ty = variant.fields[FieldIdx::from_usize(field_idx)].ty(tcx, arg_list);
                #[cfg(rapx_rustc_ge_198)]
                let field_ty = variant.fields[FieldIdx::from_usize(field_idx)]
                    .ty(tcx, arg_list)
                    .skip_norm_wip();
                return Some((field_idx, field_ty));
            }
        }
        if let Some((idx, _)) = variant
            .fields
            .iter()
            .enumerate()
            .find(|(_, f)| f.ident(tcx).name.to_string() == field_name)
        {
            #[cfg(not(rapx_rustc_ge_198))]
            let field_ty = variant.fields[FieldIdx::from_usize(idx)].ty(tcx, arg_list);
            #[cfg(rapx_rustc_ge_198)]
            let field_ty = variant.fields[FieldIdx::from_usize(idx)]
                .ty(tcx, arg_list)
                .skip_norm_wip();
            return Some((idx, field_ty));
        }
    }
    None
}

/// True when a type transitively contains a const-generic parameter or
/// an associated type alias (which may be layout-ambiguous).
pub(crate) fn ty_has_param_const(ty: Ty<'_>) -> bool {
    for arg in ty.walk() {
        match arg.kind() {
            GenericArgKind::Const(c) if matches!(c.kind(), ConstKind::Param(_)) => return true,
            GenericArgKind::Type(inner_ty) if matches!(inner_ty.kind(), TyKind::Alias(..)) => {
                return true;
            }
            _ => {}
        }
    }
    false
}
