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

pub(crate) fn should_inline_constructor(tcx: TyCtxt<'_>, callee: DefId) -> bool {
    if fn_info::get_type(tcx, callee) != FnKind::Constructor {
        return true;
    }
    match INLINE_CTOR.load(Ordering::Relaxed) {
        0 => false,
        1 => true,
        _ => !constructor_has_invariant(tcx, callee),
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

pub(crate) fn force_inline_constructor(tcx: TyCtxt<'_>, callee: DefId) -> bool {
    INLINE_CTOR.load(Ordering::Relaxed) == 1
        && fn_info::get_type(tcx, callee) == FnKind::Constructor
}
