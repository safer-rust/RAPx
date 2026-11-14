//! Conservative dependencies for a generic callable with no concrete body.
//!
//! Rust-call bundles the callable's arguments in a tuple. Inspect the actual
//! call operands rather than the generic `FnMut::call_mut` signature so nested
//! `&mut T` arguments are included. The forward VM models supported scalar
//! returns separately and keeps unresolved argument shapes as UNKNOWN.

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{Body, Operand},
    ty::{Mutability, Ty, TyCtxt, TyKind},
};

use crate::compat::Spanned;
use crate::def_ids::lang_api;
use crate::verify::api_classify;

use super::CallDependencySummary;

pub(crate) fn supports_result(ty: Ty<'_>) -> bool {
    matches!(ty.kind(), TyKind::Bool)
        || matches!(ty.kind(), TyKind::Adt(def, _) if api_classify::is_std_ordering(def.did()))
}

pub(super) fn estimate<'tcx>(
    tcx: TyCtxt<'tcx>,
    callee: DefId,
    args: &[Spanned<Operand<'tcx>>],
    body: &Body<'tcx>,
) -> Option<CallDependencySummary> {
    if tcx.is_mir_available(callee) {
        return None;
    }
    let trait_id = tcx.trait_of_assoc(callee)?;
    if !lang_api::is_fn_trait(tcx, trait_id) {
        return None;
    }

    // Fn can reach shared interior-mutable captures, FnMut can mutate its
    // captures, and FnOnce can consume them. Keep the receiver in every case.
    // Other arguments may expose mutable or interior-mutable storage,
    // including references nested in rust-call's tuple argument.
    let write_args: Vec<_> = args
        .iter()
        .enumerate()
        .filter_map(|(index, arg)| {
            (index == 0 || operand_ty(tcx, body, &arg.node).is_none_or(may_write_reachable))
                .then_some(index)
        })
        .collect();
    let all_args: Vec<_> = (0..args.len()).collect();
    Some(CallDependencySummary {
        return_depends_on_args: all_args.clone(),
        write_args,
        write_inputs: all_args,
    })
}

fn operand_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    operand: &Operand<'tcx>,
) -> Option<Ty<'tcx>> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => Some(place.ty(&body.local_decls, tcx).ty),
        Operand::Constant(constant) => Some(constant.const_.ty()),
        Operand::RuntimeChecks(_) => None,
    }
}

fn may_write_reachable(ty: Ty<'_>) -> bool {
    match ty.kind() {
        TyKind::Ref(_, _, Mutability::Mut) | TyKind::RawPtr(..) => true,
        TyKind::Ref(_, inner, Mutability::Not) => may_contain_interior_mutability(*inner),
        TyKind::Tuple(fields) => fields.iter().any(may_write_reachable),
        TyKind::Array(inner, _) | TyKind::Slice(inner) => may_write_reachable(*inner),
        TyKind::Bool | TyKind::Char | TyKind::Int(_) | TyKind::Uint(_) | TyKind::Float(_)
        | TyKind::Never | TyKind::Str => false,
        // A generic/ADT argument can carry references or interior mutability.
        _ => true,
    }
}

fn may_contain_interior_mutability(ty: Ty<'_>) -> bool {
    match ty.kind() {
        TyKind::Bool | TyKind::Char | TyKind::Int(_) | TyKind::Uint(_) | TyKind::Float(_)
        | TyKind::Never | TyKind::Str => false,
        TyKind::Tuple(fields) => fields.iter().any(may_contain_interior_mutability),
        TyKind::Array(inner, _) | TyKind::Slice(inner) => may_contain_interior_mutability(*inner),
        TyKind::Ref(_, inner, Mutability::Not) => may_contain_interior_mutability(*inner),
        // `UnsafeCell`, generic parameters, and opaque types remain possible.
        _ => true,
    }
}
