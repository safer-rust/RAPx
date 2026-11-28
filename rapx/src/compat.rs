//! Shared rustc API compatibility helpers. Keep nightly-specific `cfg` branches here.
//! Register new compiler API checks in `build.rs` and expose a stable helper here.
pub use rustc_hash::FxHashMap;
pub use rustc_hash::FxHashSet;
#[cfg(not(rapx_error_output_in_output))]
pub use rustc_session::config::ErrorOutputType;
#[cfg(rapx_error_output_in_output)]
pub use rustc_session::output::ErrorOutputType;

pub type GenericArgsRef<'tcx> = rustc_middle::ty::GenericArgs<'tcx>;

/// Access a MIR terminator across rustc versions that store it directly or in `Option`.
pub(crate) trait MirTerminatorExt<'tcx> {
    fn rapx_terminator(&self) -> &rustc_middle::mir::Terminator<'tcx>;
    fn rapx_terminator_mut(&mut self) -> &mut rustc_middle::mir::Terminator<'tcx>;
}

impl<'tcx> MirTerminatorExt<'tcx> for rustc_middle::mir::BasicBlockData<'tcx> {
    fn rapx_terminator(&self) -> &rustc_middle::mir::Terminator<'tcx> {
        #[cfg(rapx_mir_terminator_required)]
        { &self.terminator }
        #[cfg(not(rapx_mir_terminator_required))]
        { self.terminator.as_ref().expect("MIR basic block has no terminator") }
    }

    fn rapx_terminator_mut(&mut self) -> &mut rustc_middle::mir::Terminator<'tcx> {
        #[cfg(rapx_mir_terminator_required)]
        { &mut self.terminator }
        #[cfg(not(rapx_mir_terminator_required))]
        { self.terminator.as_mut().expect("MIR basic block has no terminator") }
    }
}

/// Re-export the span wrapper used by MIR call operands.
pub use rustc_span::Spanned;

use rustc_hir::def_id::DefId;
use rustc_infer::infer::{DefineOpaqueTypes, InferCtxt};
use rustc_infer::traits::ObligationCause;
#[cfg(rapx_intrinsic_enum)]
use rustc_middle::ty::Intrinsic;
use rustc_middle::ty::{self, Ty, TyCtxt, TypingEnv};
use rustc_span::Symbol;

/// Extract the name of an intrinsic across rustc's intrinsic representations.
pub(crate) fn intrinsic_symbol(tcx: TyCtxt<'_>, callee: Option<DefId>) -> Option<Symbol> {
    let intrinsic = tcx.intrinsic(callee?)?;
    #[cfg(rapx_intrinsic_enum)]
    let name = match intrinsic.name {
        Intrinsic::Rustc(name) | Intrinsic::Backend { llvm: name } => name,
    };
    #[cfg(not(rapx_intrinsic_enum))]
    let name = intrinsic.name;
    Some(name)
}

/// Unify two types using the inference API available in this rustc version.
pub(crate) fn infer_types_equal<'tcx>(
    infcx: &InferCtxt<'tcx>,
    cause: &ObligationCause<'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    lhs: Ty<'tcx>,
    rhs: Ty<'tcx>,
) -> bool {
    #[cfg(rapx_post_analysis_no_rigid_aliases)]
    { infcx.eq_raw(cause, param_env, DefineOpaqueTypes::Yes, lhs, rhs).is_ok() }
    #[cfg(not(rapx_post_analysis_no_rigid_aliases))]
    { infcx.at(cause, param_env).eq(DefineOpaqueTypes::Yes, lhs, rhs).is_ok() }
}

/// Post-analysis typing environment across rustc nightly API versions.
#[inline]
pub fn typing_env_post_analysis<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> TypingEnv<'tcx> {
    #[cfg(rapx_post_analysis_no_rigid_aliases)]
    { TypingEnv::post_analysis_no_rigid_aliases(tcx, def_id) }
    #[cfg(not(rapx_post_analysis_no_rigid_aliases))]
    { TypingEnv::post_analysis(tcx, def_id) }
}

// ── Attributes ────────────────────────────────────────────────────────

use rustc_attr_ir::Attribute;

#[allow(deprecated)]
#[inline]
pub fn get_all_attrs<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> &'tcx [Attribute] {
    tcx.get_all_attrs(def_id)
}

pub fn attribute_to_string(attr: &Attribute) -> String {
    struct Ann;
    impl rustc_hir_pretty::PpAnn for Ann {}
    rustc_hir_pretty::attribute_to_string(&Ann, attr)
}

/// Match an attribute path by pretty-printing and parsing its syntax.
pub fn attribute_path_matches(attr: &Attribute, path: &[rustc_span::Symbol]) -> bool {
    use syn::parse::Parser;

    let text = attribute_to_string(attr);
    let Ok(attrs) = syn::Attribute::parse_outer.parse_str(&text) else {
        return false;
    };
    let [attr] = attrs.as_slice() else {
        return false;
    };
    let segments = &attr.path().segments;
    segments.len() == path.len()
        && segments.iter().zip(path).all(|(segment, symbol)| {
            matches!(segment.arguments, syn::PathArguments::None)
                && segment.ident == symbol.as_str()
        })
}
