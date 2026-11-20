//! Verification options and constructor MIR selection.

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

use crate::analysis::safety_flow::root::has_rapx_struct_invariant;
use crate::cli::{ConstructorMirMode, PostfixRepeat, VerifyArgs, VerifyMode};
use crate::helpers::fn_info::{self, FnKind};

use super::{loop_handling::RepeatStrategy, type_invariants::has_json_type_invariants};

/// Options shared by target preparation and verification.
pub(crate) struct VerifyConfig {
    pub(crate) prepare_targets: bool,
    pub(crate) repeat_strategy: RepeatStrategy,
    pub(crate) mode: VerifyMode,
    pub(crate) skip_invariant: bool,
    pub(crate) constructor_mir_mode: ConstructorMirMode,
    pub(crate) path_limit: usize,
    pub(crate) trait_impl_limit: usize,
    pub(crate) crate_filter: Option<String>,
    pub(crate) module_filter: Option<String>,
    pub(crate) debug_contracts: bool,
}

impl VerifyConfig {
    /// Normalize the CLI options once for both verification entry points.
    pub(crate) fn from_args(args: &VerifyArgs) -> Self {
        let repeat_strategy = match &args.postfix_repeat {
            PostfixRepeat::Auto => RepeatStrategy::Auto,
            PostfixRepeat::Fixed(n) => RepeatStrategy::Fixed(*n),
        };
        // Invariant-less runs need constructor MIR under the default mode.
        let constructor_mir_mode = if args.skip_invariant
            && matches!(args.constructor_mir, ConstructorMirMode::Default)
        {
            ConstructorMirMode::True
        } else {
            args.constructor_mir
        };
        Self {
            prepare_targets: args.prepare_targets,
            repeat_strategy,
            mode: args.mode,
            skip_invariant: args.skip_invariant,
            constructor_mir_mode,
            path_limit: args.path_limit.filter(|n| *n != 0).unwrap_or(crate::limit::PATH_LIMIT),
            trait_impl_limit: args.trait_impl_limit.filter(|n| *n != 0).unwrap_or(crate::limit::TRAIT_IMPL_LIMIT),
            crate_filter: args.crate_name.clone(),
            module_filter: args.module.clone(),
            debug_contracts: args.debug_contracts,
        }
    }
}

/// Resolve `default` to `false` when the constructor's direct result has an
/// invariant. Otherwise retain the CLI mode for MIR versus call summaries.
pub(crate) fn effective_constructor_mir_mode(
    tcx: TyCtxt<'_>,
    callee: DefId,
    mode: ConstructorMirMode,
) -> ConstructorMirMode {
    debug_assert_eq!(fn_info::get_type(tcx, callee), FnKind::Constructor);
    match mode {
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
