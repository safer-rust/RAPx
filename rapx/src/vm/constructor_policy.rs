//! Constructor MIR selection used by the symbolic VM.

use crate::contract::type_invariants::constructor_result_has_invariant;
use crate::util::fn_info::{self, FnKind};
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
