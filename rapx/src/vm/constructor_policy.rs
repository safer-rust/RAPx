//! Constructor MIR selection used by the symbolic VM.

use crate::analysis::safety_flow::root::has_rapx_struct_invariant;
use crate::helpers::fn_info::{self, FnKind};
use crate::contract::type_invariants::has_json_type_invariants;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

#[derive(Debug, Clone, Copy, Default, clap::ValueEnum)]
pub enum ConstructorMirMode {
    True,
    False,
    #[default]
    Default,
}

/// Resolve `default` to `false` when the constructor's direct result has an
/// invariant. Otherwise retain the CLI mode for MIR versus call summaries.
pub(crate) fn effective_constructor_mir_mode(tcx: TyCtxt<'_>, callee: DefId, mode: ConstructorMirMode) -> ConstructorMirMode {
    debug_assert_eq!(fn_info::get_type(tcx, callee), FnKind::Constructor);
    match mode {
        ConstructorMirMode::Default if constructor_result_has_invariant(tcx, callee) => ConstructorMirMode::False,
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
