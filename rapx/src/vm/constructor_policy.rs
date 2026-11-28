//! Constructor MIR selection used by the symbolic VM.

use crate::contract::type_invariants::constructor_result_has_invariant;
use crate::def_ids::other_api;
use crate::util::fn_info::{self, FnKind};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

#[derive(Debug, Clone, Copy, Default)]
pub(crate) enum ConstructorMirMode {
    True,
    False,
    #[default]
    Default,
    /// Internal check mode: use invariants for all constructors that have them.
    InvariantFirst,
}

/// Expand constructor MIR by default; keep selected result models.
pub(crate) fn effective_constructor_mir_mode(tcx: TyCtxt<'_>, callee: DefId, mode: ConstructorMirMode) -> ConstructorMirMode {
    debug_assert_eq!(fn_info::get_type(tcx, callee), FnKind::Constructor);
    match mode {
        ConstructorMirMode::Default if tcx.is_mir_available(callee) && !uses_constructor_result_model(tcx, callee) => ConstructorMirMode::True,
        ConstructorMirMode::Default | ConstructorMirMode::InvariantFirst
            if constructor_result_has_invariant(tcx, callee) => ConstructorMirMode::False,
        ConstructorMirMode::InvariantFirst => ConstructorMirMode::Default,
        mode => mode,
    }
}

/// Constructors using registered result models under the default policy.
fn uses_constructor_result_model(tcx: TyCtxt<'_>, callee: DefId) -> bool {
    other_api::is_nonnull_dangling(tcx, callee) || other_api::is_box_new(tcx, callee)
}
