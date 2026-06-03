//! SMT lowering for the `Align` safety property.
//!
//! This module reduces:
//!
//! ```text
//! Align(p, T)
//! ```
//!
//! to the common SMT obligation:
//!
//! ```text
//! Aligned { place: p, align: align_of(T) }
//! ```
//!
//! The common model then proves the obligation by asking whether the path facts
//! plus the negated alignment goal are satisfiable.

use z3::{
    Config, Context, SatResult, Solver,
    ast::{Ast, Int},
};

use super::common::{SmtCheckResult, SmtChecker, SmtModel, SmtObligation, SmtQuery, place_label};
use crate::verify::{
    contract::Property, forward_visit::ForwardVisitResult, helpers::Callsite, report::CheckResult,
};

/// Check `Align` by lowering it to `SmtObligation::Aligned`.
pub(crate) fn check<'tcx>(
    checker: &SmtChecker<'tcx>,
    callsite: &Callsite<'tcx>,
    property: &Property<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
) -> SmtCheckResult {
    let Some(target) = checker.property_target(callsite, property) else {
        return SmtCheckResult::unknown("SMT Align target could not be resolved");
    };
    let Some(required_ty) = checker.property_required_ty(callsite, property) else {
        return SmtCheckResult::unknown("SMT Align type could not be resolved");
    };
    let Some((required_align, _)) = checker.type_layout(callsite.caller, required_ty) else {
        return SmtCheckResult::unknown(format!(
            "SMT Align layout unavailable for {:?}",
            required_ty
        ));
    };

    let obligation = SmtObligation::Aligned {
        place: target.clone(),
        align: required_align,
        ty_name: format!("{required_ty:?}"),
    };
    let target_label = place_label(&target);

    if required_align <= 1 {
        return SmtCheckResult {
            result: CheckResult::Proved,
            query: Some(SmtQuery::new(
                obligation,
                Vec::new(),
                format!("Align({target_label}) is trivial because required alignment is 1"),
            )),
            notes: vec![String::from("alignment requirement is trivial")],
        };
    }

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
            format!("try to refute {target_label} % {required_align} == 0"),
        ));
    };

    let zero = Int::from_u64(&ctx, 0);
    let align = Int::from_u64(&ctx, required_align);
    let goal = target_term.modulo(&align)._eq(&zero);
    let query = SmtQuery::new(
        obligation,
        model.assumptions().to_vec(),
        format!("try to refute {target_label} % {required_align} == 0"),
    );

    solver.assert(&goal.not());
    match solver.check() {
        SatResult::Unsat => {
            SmtCheckResult::proved("alignment proved; no counterexample satisfies the path facts")
                .with_query(query)
        }
        SatResult::Sat => {
            SmtCheckResult::unknown("current path facts do not prove the required alignment")
                .with_query(query)
                .with_note(
                    "hint: add an offset-alignment guard or provide a pointer-add/layout summary",
                )
        }
        SatResult::Unknown => SmtCheckResult::unknown("solver returned unknown").with_query(query),
    }
}
