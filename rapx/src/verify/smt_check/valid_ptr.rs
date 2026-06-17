//! SMT lowering for the composite `ValidPtr` safety property.
//!
//! `ValidPtr(p, T, n)` is not a primitive SMT obligation.  The verifier treats
//! it as a bundle of smaller safety properties.  This module keeps that
//! decomposition local to the `ValidPtr` SP and delegates implemented pieces to
//! the corresponding SMT modules:
//!
//! ```text
//! ValidPtr(p, T, n)
//!   -> NonNull(p)
//!   -> Align(p, T)
//!   -> Allocated(p, T, n)
//!   -> InBound(p, T, n)
//!   -> Init(p, T, n)
//!   -> Typed(p, T)         // future
//! ```
//!
//! Until all pieces are implemented, the composite result remains `Unknown`,
//! but the report shows which implemented primitive SMT obligations already
//! succeed.

use super::{
    align, allocated,
    common::{SmtCheckResult, SmtChecker},
    in_bound, init, non_null,
};
use crate::verify::{
    contract::{Property, PropertyKind},
    forward_visit::ForwardVisitResult,
    helpers::Callsite,
};

/// Check the implemented primitive pieces of `ValidPtr`.
pub(crate) fn check<'tcx>(
    checker: &SmtChecker<'tcx>,
    callsite: &Callsite<'tcx>,
    property: &Property<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
) -> SmtCheckResult {
    let non_null_property = primitive_property(property, PropertyKind::NonNull);
    let align_property = primitive_property(property, PropertyKind::Align);
    let allocated_property = primitive_property(property, PropertyKind::Allocated);
    let in_bound_property = primitive_property(property, PropertyKind::InBound);
    let init_property = primitive_property(property, PropertyKind::Init);

    let non_null = non_null::check(checker, callsite, &non_null_property, forward);
    let align = align::check(checker, callsite, &align_property, forward);
    let allocated = allocated::check(checker, callsite, &allocated_property, forward);
    let in_bound = in_bound::check(checker, callsite, &in_bound_property, forward);
    let init = init::check(checker, callsite, &init_property, forward);

    SmtCheckResult::unknown(
        "ValidPtr is decomposed, but not all primitive obligations are implemented yet",
    )
    .with_note(format!("primitive NonNull via SMT: {:?}", non_null.result))
    .with_note(format!("primitive Align via SMT: {:?}", align.result))
    .with_note(format!(
        "primitive Allocated via SMT: {:?}",
        allocated.result
    ))
    .with_note(format!("primitive InBound via SMT: {:?}", in_bound.result))
    .with_note(format!("primitive Init via SMT: {:?}", init.result))
    .with_note("missing primitive SMT lowerings: Typed")
}

/// Reuse the original arguments while checking one primitive component.
fn primitive_property<'tcx>(property: &Property<'tcx>, kind: PropertyKind) -> Property<'tcx> {
    Property {
        kind,
        args: property.args.clone(),
    }
}
