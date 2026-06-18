use rustc_abi::FieldIdx;
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{BasicBlock, TerminatorKind},
    ty::{Ty, TyCtxt, TyKind},
};
use syn::Expr;

pub use crate::helpers::fn_info::parse_expr_into_number;
pub use crate::helpers::mir_scan::{Callsite, CallsiteLocation, collect_unsafe_callsites};
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
            return resolve_projection_from_struct_ident(tcx, base_ident, fields, struct_ty);
        }
    }
    None
}

/// Return the callee argument index represented by a MIR local.
///
/// Contract annotations written with parameter names are parsed in the callee's
/// local namespace.  MIR local `_0` is the return place and argument locals are
/// `_1..=_arg_count`, so callee local `_1` denotes callsite argument `0`.
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

    Some((1, field_indices, current_ty))
}

fn resolve_next_field<'tcx>(
    tcx: TyCtxt<'tcx>,
    base_ty: Ty<'tcx>,
    field_name: &str,
) -> Option<(usize, Ty<'tcx>)> {
    let peeled_ty = base_ty.peel_refs();
    if let TyKind::Adt(adt_def, arg_list) = *peeled_ty.kind() {
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
