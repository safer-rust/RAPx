//! Fast, conclusive checks for formulas with machine integers encoded in BV and Int.

use crate::compat::FxHashSet;
use z3::{
    AstKind, Config, Context, DeclKind, Params, SatResult, Solver, Tactic,
    ast::{Ast, Bool, Dynamic},
};

/// First try a weaker formula for a proof and a stronger, specialized
/// formula for a witness. All inconclusive attempts fall through to the
/// original solver with its usual timeout and diagnostics.
/// Callers must use only the returned status, as a fast result does not
/// populate the original solver's model or unsat core.
pub(crate) fn check<'z3>(solver: &Solver<'z3>) -> SatResult {
    let assertions = solver.get_assertions();
    let mut visited = FxHashSet::default();
    let mut pending: Vec<_> = assertions
        .iter()
        .map(|term| Dynamic::from_ast(term))
        .collect();
    let mut conversions = Vec::new();
    while let Some(term) = pending.pop() {
        match term.kind() {
            AstKind::Quantifier | AstKind::Var => return solver.check(),
            AstKind::App if visited.insert(term.clone()) => {
                if matches!(term.decl().kind(), DeclKind::BV2INT | DeclKind::INT2BV) {
                    conversions.push(term.clone());
                }
                pending.extend(term.children());
            }
            _ => {}
        }
    }
    if conversions.is_empty() {
        return solver.check();
    }

    let ctx = solver.get_context();
    let mut params = Params::new(ctx);
    // Use a deterministic work budget for each speculative solve. This also
    // avoids arming a short timeout alongside the context's existing timeout.
    params.set_u32("rlimit", 50_000);
    let relaxed = Solver::new(ctx);
    relaxed.set_params(&params);
    let replacements: Vec<_> = conversions
        .iter()
        .map(|term| Dynamic::fresh_const(ctx, "word_value", &term.get_sort()))
        .collect();
    let substitutions: Vec<_> = conversions.iter().zip(&replacements).collect();
    for assertion in &assertions {
        relaxed.assert(&assertion.substitute(&substitutions));
    }
    match relaxed.check() {
        // Every model of the original ground formula interprets each fresh
        // value as the concrete result of its corresponding conversion.
        SatResult::Unsat => return SatResult::Unsat,
        SatResult::Unknown => return solver.check(),
        SatResult::Sat => {}
    }
    let Some(model) = relaxed.get_model() else {
        return solver.check();
    };

    // Fix only inputs to the bitwise computation using the candidate model.
    // Simplification can then evaluate the bitwise computation before solving
    // the rest of the original formula. A failed candidate proves nothing.
    let mut visited = FxHashSet::default();
    let mut values = Vec::new();
    let mut pending = conversions;
    while let Some(term) = pending.pop() {
        if term.kind() != AstKind::App || !visited.insert(term.clone()) {
            continue;
        }
        if term.decl().kind() == DeclKind::UNINTERPRETED && term.num_children() == 0 {
            if let Some(value) = model.eval(&term, true)
                && (value.kind() == AstKind::Numeral
                    || value
                        .as_bool()
                        .is_some_and(|value| value.as_bool().is_some()))
            {
                values.push((term, value));
            }
        } else {
            pending.extend(term.children());
        }
    }
    if !values.is_empty() {
        let substitutions: Vec<_> = values.iter().map(|(term, value)| (term, value)).collect();
        let specialized = Solver::new(ctx);
        specialized.set_params(&params);
        for assertion in &assertions {
            specialized.assert(&assertion.substitute(&substitutions).simplify());
        }
        if specialized.check() == SatResult::Sat {
            return SatResult::Sat;
        }
    }
    solver.check()
}

/// Try another arithmetic strategy on a byte bound with a symbolic divisor.
/// Only a proof discharges the bound. The original assertions are unchanged.
pub(crate) fn prove_symbolic_division_bound<'z3>(
    solver: &Solver<'z3>,
    negated_bound: &Bool<'z3>,
) -> bool {
    let mut pending = vec![Dynamic::from_ast(negated_bound)];
    let mut visited = FxHashSet::default();
    while let Some(term) = pending.pop() {
        if term.kind() != AstKind::App || !visited.insert(term.clone()) {
            continue;
        }
        if term.decl().kind() == DeclKind::IDIV
            && term
                .nth_child(1)
                .is_some_and(|divisor| divisor.kind() != AstKind::Numeral)
        {
            // Keep the alternate strategy's search independent of earlier
            // queries in the VM context.
            let ctx = Context::new(&Config::new());
            let arithmetic = Tactic::new(&ctx, "smt").solver();
            let mut params = Params::new(&ctx);
            params.set_u32("arith.solver", 2);
            params.set_u32("rlimit", 3_000_000);
            arithmetic.set_params(&params);
            for assertion in solver.get_assertions() {
                arithmetic.assert(&assertion.translate(&ctx));
            }
            return arithmetic.check() == SatResult::Unsat;
        }
        pending.extend(term.children());
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use z3::{
        Config, Context,
        ast::{BV, Int},
    };

    #[test]
    fn tentative_results_do_not_replace_the_original_query() {
        let ctx = Context::new(&Config::new());
        let solver = Solver::new(&ctx);
        let value = Int::fresh_const(&ctx, "input");
        let bits = BV::from_int(&value, 8);
        let low_bits = bits.bvand(&BV::from_u64(&ctx, 7, 8)).to_int(false);
        let seven = Int::from_u64(&ctx, 7);
        solver.assert(&value.ge(&Int::from_u64(&ctx, 0)));
        solver.assert(&low_bits._eq(&seven));
        // The relaxed model can choose input = 0, which is insufficient for
        // the original query. Its specialization must never prove UNSAT.
        assert_eq!(check(&solver), SatResult::Sat);

        solver.push();
        solver.assert(&value._eq(&Int::from_u64(&ctx, 8)));
        // The relaxed formula can still assign low_bits = 7. That alone
        // must never be reported as a witness for the original query.
        assert_eq!(check(&solver), SatResult::Unsat);
        solver.pop(1);
        assert_eq!(check(&solver), SatResult::Sat);
    }
}
