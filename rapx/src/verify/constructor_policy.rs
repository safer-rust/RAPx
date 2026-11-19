//! Constructor MIR selection shared by path collection and the VM.
//! Both stages must make the same expansion decision for each call.
//! Callers classify the callee before applying this policy.
//!
//! # Agent Rules
//!
//! Do not change this file without human approval.

use std::sync::OnceLock;

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

use crate::analysis::safety_flow::root::has_rapx_struct_invariant;
use crate::cli::ConstructorMirMode;
use crate::helpers::fn_info::{self, FnKind};
use crate::verify::type_invariants::has_json_type_invariants;

static CONSTRUCTOR_MIR_MODE: OnceLock<ConstructorMirMode> = OnceLock::new();

/// Set the CLI mode once before path collection and VM execution.
pub(crate) fn set_constructor_mir_mode(mode: ConstructorMirMode) {
    CONSTRUCTOR_MIR_MODE.set(mode).expect("set twice");
}

/// Resolve `default` to `false` when the direct result has an invariant.
/// Otherwise retain the CLI mode: `true` prioritizes available MIR, `false`
/// skips MIR, and `default` tries call models before MIR.
pub(crate) fn effective_mir_mode(tcx: TyCtxt<'_>, callee: DefId) -> ConstructorMirMode {
    debug_assert_eq!(fn_info::get_type(tcx, callee), FnKind::Constructor);
    match CONSTRUCTOR_MIR_MODE.get().copied().unwrap_or_default() {
        ConstructorMirMode::Default if constructor_result_has_invariant(tcx, callee) => {
            ConstructorMirMode::False
        }
        mode => mode,
    }
}

/// Whether a constructor returns its owning ADT directly and that result has
/// a struct or registered type invariant. Wrapped results do not qualify.
pub(crate) fn constructor_result_has_invariant(tcx: TyCtxt<'_>, callee: DefId) -> bool {
    let Some(owner) = fn_info::get_adt_def_id_by_adt_method(tcx, callee) else {
        return false;
    };
    let output = tcx.fn_sig(callee).skip_binder().output().skip_binder();
    Some(owner) == output.ty_adt_def().map(|adt| adt.did())
        && (has_rapx_struct_invariant(tcx, owner) || has_json_type_invariants(tcx, output))
}
