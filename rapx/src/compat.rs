/// Centralized compatibility shims for compiler API differences across nightly
/// versions.
///
/// When a type or function moves between modules or changes interface across
/// rustc versions, add a re-export here (gated by `#[cfg]`).  All other
/// modules import from this crate instead of writing their own `#[cfg]` blocks.
///
/// # How to add a new compat item
///
/// 1. Add a cfg flag in `build.rs` (e.g. `rustc_foo_moved`).
/// 2. Register it with `emit_check_cfg` in `build.rs`.
/// 3. Add the re-export below.
/// 4. Update call-sites to `use crate::compat::Foo;`.
pub use rustc_hash::FxHashMap;
pub use rustc_hash::FxHashSet;

#[cfg(not(rapx_generic_args_value))]
pub use rustc_middle::ty::GenericArgsRef;
#[cfg(rapx_generic_args_value)]
pub type GenericArgsRef<'tcx> = rustc_middle::ty::GenericArgs<'tcx>;

/// `Spanned` was moved from `rustc_span::source_map` to `rustc_span` root
/// in rustc 1.97.
pub use rustc_span::Spanned;

// ── predicates_of / clauses_of (rustc ≥ 1.100) ────────────────────────

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

/// Type alias for the return type of `predicates_of`.
#[cfg(not(rapx_ge_100))]
pub type GenericPredicatesC<'tcx> = rustc_middle::ty::GenericPredicates<'tcx>;
#[cfg(rapx_ge_100)]
pub type GenericPredicatesC<'tcx> = rustc_middle::ty::GenericClauses<'tcx>;

/// Fetch generic predicates/clauses for a definition.
#[cfg(not(rapx_ge_100))]
#[inline]
pub fn predicates_of<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> GenericPredicatesC<'tcx> {
    tcx.predicates_of(def_id)
}
#[cfg(rapx_ge_100)]
#[inline]
pub fn predicates_of<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> GenericPredicatesC<'tcx> {
    tcx.clauses_of(def_id)
}

// ── GenericArgsRef::get (Binder wrapping in rustc ≥ 1.99) ─────────────

#[cfg(not(rapx_generic_args_value))]
pub fn args_get<'tcx>(
    args: &rustc_middle::ty::Binder<'tcx, &'tcx rustc_middle::ty::GenericArgs<'tcx>>,
    index: usize,
) -> Option<rustc_middle::ty::GenericArg<'tcx>> {
    args.skip_binder().get(index).copied()
}

#[cfg(rapx_generic_args_value)]
pub fn args_get<'tcx>(
    args: &rustc_middle::ty::Binder<'tcx, rustc_middle::ty::GenericArgs<'tcx>>,
    index: usize,
) -> Option<rustc_middle::ty::GenericArg<'tcx>> {
    args.skip_binder().get(index)
}

// ── skip_norm_wip (rustc_type_ir) ──────────────────────────────────────

/// `TyKind::skip_norm_wip` was introduced to handle the `Wip` alias
/// variant.  On older toolchains that do not have `AliasRelation::Wip`,
/// the method is not needed and we provide an identity fallback.
#[cfg(not(rapx_has_skip_norm_wip))]
pub trait SkipNormWip: Sized {
    fn skip_norm_wip(self) -> Self {
        self
    }
}
#[cfg(not(rapx_has_skip_norm_wip))]
impl<T: Sized> SkipNormWip for T {}

// ── get_all_attrs (deprecated but still the only way) ───────────────────

#[cfg(rapx_has_attr_ir)]
use rustc_attr_ir::Attribute;
#[cfg(not(rapx_has_attr_ir))]
use rustc_hir::Attribute;

#[allow(deprecated)]
#[inline]
pub fn get_all_attrs<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> &'tcx [Attribute] {
    tcx.get_all_attrs(def_id)
}

pub fn attribute_to_string(_tcx: TyCtxt<'_>, attr: &Attribute) -> String {
    struct Ann;
    impl rustc_hir_pretty::PpAnn for Ann {}
    rustc_hir_pretty::attribute_to_string(&Ann, attr)
}

/// Match an attribute path through its pretty-printed syntax.  The rustc
/// attribute representation changes across nightlies, while both versions
/// expose `attribute_to_string`.
pub fn attribute_path_matches(
    tcx: TyCtxt<'_>,
    attr: &Attribute,
    path: &[rustc_span::Symbol],
) -> bool {
    use syn::parse::Parser;

    let text = attribute_to_string(tcx, attr);
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
