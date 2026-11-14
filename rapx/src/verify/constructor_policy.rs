//! Constructor inlining policy shared by path collection and the VM.

use std::sync::atomic::{AtomicU8, Ordering};

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

use crate::cli::InlineCtor;
use crate::helpers::fn_info::{self, FnKind};

static INLINE_CTOR: AtomicU8 = AtomicU8::new(2);

pub(crate) fn set_inline_ctor(mode: InlineCtor) {
    let value = match mode {
        InlineCtor::True => 1,
        InlineCtor::False => 0,
        InlineCtor::Default => 2,
    };
    INLINE_CTOR.store(value, Ordering::Relaxed);
}

/// Whether the inlining policy allows this call to use the callee's MIR.
/// A registered call summary can still take precedence unless inlining is forced.
pub(crate) fn should_inline_constructor(tcx: TyCtxt<'_>, callee: DefId) -> bool {
    if fn_info::get_type(tcx, callee) != FnKind::Constructor {
        return true;
    }
    match INLINE_CTOR.load(Ordering::Relaxed) {
        0 => false,
        1 => true,
        _ => {
            let sig = tcx.fn_sig(callee).skip_binder();
            let output = sig.output().skip_binder();
            let no_arg_nonnull = sig.inputs().skip_binder().is_empty()
                && output
                    .ty_adt_def()
                    .is_some_and(|adt| crate::verify::api_classify::is_std_nonnull(adt.did()));
            let shared_owner_without_raw_input = output.ty_adt_def().is_some_and(|adt| {
                crate::verify::call_summary::shared_owner::has_ref_count_share_reconstruction(tcx, adt.did())
            }) && sig
                .inputs()
                .skip_binder()
                .iter()
                .all(|ty| !matches!(ty.kind(), rustc_middle::ty::TyKind::RawPtr(..)));
            no_arg_nonnull
                || shared_owner_without_raw_input
                || !constructor_has_invariant(tcx, callee)
        }
    }
}

pub(crate) fn constructor_has_invariant(tcx: TyCtxt<'_>, callee: DefId) -> bool {
    let Some(owner) = fn_info::get_adt_def_id_by_adt_method(tcx, callee) else {
        return false;
    };
    let output = tcx.fn_sig(callee).skip_binder().output().skip_binder();
    Some(owner) == output.ty_adt_def().map(|adt| adt.did())
        && (crate::analysis::safety_flow::root::function_has_struct_invariant(tcx, callee)
            || crate::verify::type_invariants::has_type_invariants_for_ty(tcx, output))
}

/// Whether an explicit `--inline-ctor=true` overrides a constructor's call summary.
pub(crate) fn force_inline_constructor(tcx: TyCtxt<'_>, callee: DefId) -> bool {
    INLINE_CTOR.load(Ordering::Relaxed) == 1
        && fn_info::get_type(tcx, callee) == FnKind::Constructor
}
