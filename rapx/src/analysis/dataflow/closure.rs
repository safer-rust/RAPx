//! Shared classification of `Fn`/`FnMut`/`FnOnce` calls.
//!
//! Dataflow keeps their arguments as possible dependencies; the VM can
//! abstract only supported results. Concrete body resolution remains
//! in `util::resolve`.

use rustc_hir::def_id::DefId;
use rustc_middle::ty::{Ty, TyCtxt, TyKind};

use crate::def_ids::{lang_api, type_ids};

/// Whether this method is a compiler callable trait's `call*` method.
pub(crate) fn is_fn_trait_method(tcx: TyCtxt<'_>, callee: DefId) -> bool {
    tcx.trait_of_assoc(callee)
        .is_some_and(|trait_id| lang_api::is_fn_trait(tcx, trait_id))
}

/// Whether the call has no MIR body and needs conservative dependencies.
pub(crate) fn is_opaque_fn_call(tcx: TyCtxt<'_>, callee: DefId) -> bool {
    !tcx.is_mir_available(callee) && is_fn_trait_method(tcx, callee)
}

/// Results the VM can represent without executing the concrete closure body.
fn supports_opaque_result(ty: Ty<'_>) -> bool {
    ty.is_unit()
        || matches!(ty.kind(), TyKind::Bool | TyKind::Int(_) | TyKind::Uint(_))
        || matches!(ty.kind(), TyKind::Adt(def, _) if type_ids::is_std_ordering(def.did()))
}

/// Whether a `Fn*` call has a conservative VM effect model for this result type.
pub(crate) fn can_abstract_call(tcx: TyCtxt<'_>, callee: DefId, result: Ty<'_>) -> bool {
    is_fn_trait_method(tcx, callee) && supports_opaque_result(result)
}
