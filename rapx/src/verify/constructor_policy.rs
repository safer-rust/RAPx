//! Constructor MIR selection shared by path collection and the VM.

use std::sync::atomic::{AtomicU8, Ordering};

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

use crate::cli::ConstructorMirMode;
use crate::helpers::fn_info::{self, FnKind};

static CONSTRUCTOR_MIR_MODE: AtomicU8 = AtomicU8::new(2);

pub(crate) fn set_constructor_mir_mode(mode: ConstructorMirMode) {
    let value = match mode {
        ConstructorMirMode::True => 1,
        ConstructorMirMode::False => 0,
        ConstructorMirMode::Default => 2,
    };
    CONSTRUCTOR_MIR_MODE.store(value, Ordering::Relaxed);
}

/// Whether the selected mode permits using this call's MIR.
/// Non-constructors always pass. Call model selection separately decides
/// whether to execute MIR or use a summary.
pub(crate) fn allows_mir_expansion(tcx: TyCtxt<'_>, callee: DefId) -> bool {
    if fn_info::get_type(tcx, callee) != FnKind::Constructor {
        return true;
    }
    match CONSTRUCTOR_MIR_MODE.load(Ordering::Relaxed) {
        0 => false,
        1 => true,
        _ => {
            let sig = tcx.fn_sig(callee).skip_binder();
            let output = sig.output().skip_binder();
            let shared_owner_without_raw_input = output.ty_adt_def().is_some_and(|adt| {
                crate::verify::call_summary::shared_owner::has_ref_count_share_reconstruction(
                    tcx,
                    adt.did(),
                )
            }) && sig
                .inputs()
                .skip_binder()
                .iter()
                .all(|ty| !matches!(ty.kind(), rustc_middle::ty::TyKind::RawPtr(..)));
            shared_owner_without_raw_input || !constructor_result_has_invariant(tcx, callee)
        }
    }
}

/// Whether a bare `Self` result has a struct or registered type invariant.
pub(crate) fn constructor_result_has_invariant(tcx: TyCtxt<'_>, callee: DefId) -> bool {
    let Some(owner) = fn_info::get_adt_def_id_by_adt_method(tcx, callee) else {
        return false;
    };
    let output = tcx.fn_sig(callee).skip_binder().output().skip_binder();
    Some(owner) == output.ty_adt_def().map(|adt| adt.did())
        && (crate::analysis::safety_flow::root::function_has_struct_invariant(tcx, callee)
            || crate::verify::type_invariants::has_type_invariants_for_ty(tcx, output))
}

/// Whether `--expand-ctor=true` requests constructor MIR over call models.
pub(crate) fn forces_constructor_mir(tcx: TyCtxt<'_>, callee: DefId) -> bool {
    CONSTRUCTOR_MIR_MODE.load(Ordering::Relaxed) == 1
        && fn_info::get_type(tcx, callee) == FnKind::Constructor
}
