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

/// `Spanned` was moved from `rustc_span::source_map` to `rustc_span` root
/// in rustc 1.97.
#[cfg(rustc_spanned_at_root)]
pub use rustc_span::Spanned;
#[cfg(not(rustc_spanned_at_root))]
pub use rustc_span::source_map::Spanned;

// ── predicates_of / clauses_of (rustc ≥ 1.99 2026-07-28) ─────────────

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

/// Type alias for the return type of `predicates_of`.
#[cfg(not(rapx_rustc_ge_199))]
pub type GenericPredicatesC<'tcx> =
    rustc_middle::ty::GenericPredicates<'tcx>;
#[cfg(rapx_rustc_ge_199)]
pub type GenericPredicatesC<'tcx> =
    rustc_middle::ty::GenericClauses<'tcx>;

/// Fetch generic predicates/clauses for a definition.
#[cfg(not(rapx_rustc_ge_199))]
#[inline]
pub fn predicates_of<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> GenericPredicatesC<'tcx> {
    tcx.predicates_of(def_id)
}
#[cfg(rapx_rustc_ge_199)]
#[inline]
pub fn predicates_of<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> GenericPredicatesC<'tcx> {
    tcx.clauses_of(def_id)
}

// ── OwnerId (rustc ≥ 1.99) ────────────────────────────────────────────

#[cfg(not(rapx_rustc_ge_199))]
pub use rustc_hir::hir_id::OwnerId;
#[cfg(rapx_rustc_ge_199)]
pub use rustc_hir::OwnerId;

// ── GenericArgsRef::get (Binder wrapping in rustc ≥ 1.99) ─────────────

#[cfg(not(rapx_rustc_ge_199))]
pub fn args_get<'tcx>(
    args: &rustc_middle::ty::GenericArgsRef<'tcx>,
    index: usize,
) -> Option<&'tcx rustc_middle::ty::GenericArg<'tcx>> {
    args.get(index)
}
#[cfg(rapx_rustc_ge_199)]
pub fn args_get<'tcx>(
    args: &rustc_middle::ty::Binder<
        'tcx,
        &'tcx rustc_middle::ty::GenericArgs<'tcx>,
    >,
    index: usize,
) -> Option<rustc_middle::ty::GenericArg<'tcx>> {
    args.skip_binder().get(index).copied()
}
