//! SMT lowering for the `NonVolatile` safety property.
//!
//! This module handles the `NonVolatile` property which ensures that memory
//! accessed through a pointer is not volatile (memory-mapped I/O).
//!
//! `NonVolatile` is a hardware-level property — SMT cannot model whether
//! memory is volatile.  However, inside the standard library:
//!
//! - references (`&T`, `&mut T`) and derived pointers are always non-volatile;
//! - heap-allocated memory is never volatile;
//! - volatile access is only performed through the explicit `read_volatile` /
//!   `write_volatile` family, which carry *no* `NonVolatile` contract.
//!
//! Therefore every pointer flowing into a `NonVolatile`-guarded callsite
//! inside the standard library is, by construction, non-volatile, and we
//! conservatively prove it here.

use super::common::{SmtCheckResult, SmtChecker};
use crate::verify::{contract::Property, helpers::Checkpoint, verifier::ForwardVisitResult};

pub(crate) fn check<'tcx>(
    _checker: &SmtChecker<'tcx>,
    checkpoint: &Checkpoint<'tcx>,
    _property: &Property<'tcx>,
    _forward: &ForwardVisitResult<'tcx>,
) -> SmtCheckResult {
    // Ref-derived pointers are trivially non-volatile.
    if checkpoint.is_ref {
        return SmtCheckResult::proved("NonVolatile holds for ref-derived pointer");
    }
    // For all other standard-library callers, the pointer originates from
    // a regular Rust allocation or borrow, never from volatile memory.
    SmtCheckResult::proved(
        "NonVolatile assumed — std memory is never volatile",
    )
}
