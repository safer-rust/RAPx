//! Constructor MIR selection used by the symbolic VM.

use crate::contract::type_invariants::constructor_result_has_invariant;
use crate::def_ids::other_api;
use crate::util::fn_info::{self, FnKind};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

#[derive(Debug, Clone, Copy, Default, clap::ValueEnum)]
pub enum ConstructorMirMode {
    True,
    False,
    #[default]
    Default,
    /// Internal check mode: use invariants for all constructors that have them.
    #[value(skip)]
    InvariantFirst,
}

/// Expand selected standard container constructors under `default` to retain
/// their concrete length and capacity; otherwise use a result invariant when available.
pub(crate) fn effective_constructor_mir_mode(tcx: TyCtxt<'_>, callee: DefId, mode: ConstructorMirMode) -> ConstructorMirMode {
    debug_assert_eq!(fn_info::get_type(tcx, callee), FnKind::Constructor);
    match mode {
        ConstructorMirMode::Default if tcx.is_mir_available(callee) && other_api::is_vec_string_mir_constructor(tcx, callee) => ConstructorMirMode::True,
        ConstructorMirMode::Default | ConstructorMirMode::InvariantFirst
            if constructor_result_has_invariant(tcx, callee) => ConstructorMirMode::False,
        ConstructorMirMode::InvariantFirst => ConstructorMirMode::Default,
        mode => mode,
    }
}
