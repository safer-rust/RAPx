//! SMT lowering for the `NonNull` safety property.
//!
//! This module reduces:
//!
//! ```text
//! NonNull(p)
//! ```
//!
//! to the common SMT obligation:
//!
//! ```text
//! NonZero { place: p }
//! ```
//!
//! The common model asserts path-local facts such as reference-derived pointers
//! and `as_ptr` results as non-zero assumptions, then asks whether the target can
//! still be zero.

use z3::{
    Config, Context, SatResult, Solver,
    ast::{Ast, Int},
};

use super::common::{SmtCheckResult, SmtChecker, SmtModel, SmtObligation, SmtQuery, place_label};
use crate::verify::{contract::Property, forward_visit::ForwardVisitResult, helpers::Callsite};

/// Check `NonNull` by lowering it to `SmtObligation::NonZero`.
pub(crate) fn check<'tcx>(
    checker: &SmtChecker<'tcx>,
    callsite: &Callsite<'tcx>,
    property: &Property<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
) -> SmtCheckResult {
    let Some(target) = checker.property_target(callsite, property) else {
        return SmtCheckResult::unknown("NonNull target could not be resolved");
    };

    let obligation = SmtObligation::NonZero {
        place: target.clone(),
    };
    let target_label = place_label(&target);

    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);
    let mut model = SmtModel::new(checker.tcx, callsite, forward, &ctx);
    model.assert_forward_facts(&solver);

    let Some(target_term) = model.term_for_place(&target) else {
        return SmtCheckResult::unknown(format!(
            "could not build an address term for {target_label}"
        ))
        .with_query(SmtQuery::new(
            obligation,
            model.assumptions().to_vec(),
            format!("try to refute {target_label} != 0"),
        ));
    };

    let zero = Int::from_u64(&ctx, 0);
    let query = SmtQuery::new(
        obligation,
        model.assumptions().to_vec(),
        format!("try to refute {target_label} != 0"),
    );

    solver.assert(&target_term._eq(&zero));
    match solver.check() {
        SatResult::Unsat => SmtCheckResult::proved(
            "non-null proved; no zero-address model satisfies the path facts",
        )
        .with_query(query),
        SatResult::Sat => {
            SmtCheckResult::unknown("current path facts do not prove the target is non-null")
                .with_query(query)
                .with_note("hint: add a non-null guard or provide a source/provenance summary")
        }
        SatResult::Unknown => SmtCheckResult::unknown("solver returned unknown").with_query(query),
    }
}
