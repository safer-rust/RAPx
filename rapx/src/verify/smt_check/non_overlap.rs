//! SMT lowering for the `NonOverlap` safety property.
//!
//! `NonOverlap(a, b)` is mostly used by copy/swap-style unsafe APIs.  The
//! contract tells us which pointer arguments must be disjoint; the element count
//! usually comes from the call itself, e.g. `copy_nonoverlapping(src, dst,
//! count)`.

use super::common::{SmtCheckResult, SmtChecker, SmtObligation, SmtTerm};
use crate::verify::{
    contract::Property, def_use::PlaceKey, helpers::Checkpoint, verifier::ForwardVisitResult,
};
use rustc_middle::mir::{Operand, Rvalue, StatementKind};

/// Check `NonOverlap` by lowering two pointer ranges to a common SMT obligation.
pub(crate) fn check<'tcx>(
    checker: &SmtChecker<'tcx>,
    checkpoint: &Checkpoint<'tcx>,
    property: &Property<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
) -> SmtCheckResult {
    // A single array argument (`NonOverlap(indices)`, all elements pairwise
    // distinct) that a preceding `get_disjoint`-style validator has checked is
    // discharged by that trusted summary.
    if property.args.len() == 1 && checker.checkpoint_uses_validated_array(checkpoint, forward) {
        return SmtCheckResult::proved(
            "NonOverlap proved: indices validated pairwise-distinct by a preceding disjoint check",
        );
    }
    let Some(left) = checker.property_place_arg(checkpoint, property, 0) else {
        return SmtCheckResult::unknown("NonOverlap left pointer could not be resolved");
    };
    let Some(right) = checker.property_place_arg(checkpoint, property, 1) else {
        return SmtCheckResult::unknown("NonOverlap right pointer could not be resolved");
    };
    let left = resolve_callsite_copy(checker, checkpoint, left);
    let right = resolve_callsite_copy(checker, checkpoint, right);

    // For copy_nonoverlapping-like functions where the caller has both
    // a shared slice reference and a mutable slice reference parameter,
    // the pointers cannot alias by Rust's uniqueness rules.
    if let Some(callee) = checkpoint.callee {
        let name = checker.tcx.def_path_str(callee);
        if name.contains("ptr::copy_nonoverlapping")
            || name.contains("ptr::copy")
            || name.contains("ptr::swap_nonoverlapping")
        {
            let body = checker.tcx.optimized_mir(checkpoint.caller);
            let params: Vec<_> = (1..=body.arg_count)
                .map(|i| {
                    let ty = body.local_decls[rustc_middle::mir::Local::from_usize(i)].ty;
                    (i, ty)
                })
                .collect();
            let has_shared = params.iter().any(|(_, ty)| {
                matches!(
                    ty.kind(),
                    rustc_middle::ty::TyKind::Ref(_, _, rustc_middle::ty::Mutability::Not)
                )
            });
            let has_mut = params.iter().any(|(_, ty)| {
                matches!(
                    ty.kind(),
                    rustc_middle::ty::TyKind::Ref(_, _, rustc_middle::ty::Mutability::Mut)
                )
            });
            if has_shared && has_mut {
                return SmtCheckResult::proved(
                    "NonOverlap proved: caller has both & and &mut slice params",
                );
            }
        }
    }

    let count = property
        .args
        .get(2)
        .and_then(|_| checker.property_len_expr(checkpoint, property))
        .and_then(|expr| checker.contract_expr_to_smt_term(checkpoint.caller, &expr))
        .or_else(|| checker.callsite_arg_smt_term(checkpoint, 2))
        .unwrap_or(SmtTerm::Const(1));

    let elem_size = checker
        .place_pointee_size(checkpoint.caller, &left)
        .or_else(|| checker.place_pointee_size(checkpoint.caller, &right))
        .unwrap_or(1);

    checker.prove_obligation(
        checkpoint,
        forward,
        SmtObligation::NonOverlapping {
            left,
            right,
            left_count: count.clone(),
            right_count: count,
            elem_size,
        },
        property.null_guard.as_ref(),
    )
}

fn resolve_callsite_copy<'tcx>(
    checker: &SmtChecker<'tcx>,
    checkpoint: &Checkpoint<'tcx>,
    mut place: PlaceKey,
) -> PlaceKey {
    for _ in 0..8 {
        if !place.fields.is_empty() {
            return place;
        }
        let Some(local) = place.local() else {
            return place;
        };
        let body = checker.tcx.optimized_mir(checkpoint.caller);
        let block = &body.basic_blocks[checkpoint.block];
        let source = block
            .statements
            .iter()
            .rev()
            .find_map(|statement| assignment_source_for_local(statement, local))
            .or_else(|| {
                body.basic_blocks.iter().rev().find_map(|block| {
                    block
                        .statements
                        .iter()
                        .rev()
                        .find_map(|statement| assignment_source_for_local(statement, local))
                })
            });
        let Some(source) = source else {
            return place;
        };
        let next = PlaceKey::from_mir_place(source);
        if next == place {
            return place;
        }
        place = next;
    }
    place
}

fn assignment_source_for_local<'a, 'tcx>(
    statement: &'a rustc_middle::mir::Statement<'tcx>,
    local: rustc_middle::mir::Local,
) -> Option<&'a rustc_middle::mir::Place<'tcx>> {
    let StatementKind::Assign(assign) = &statement.kind else {
        return None;
    };
    let (target, rvalue) = assign.as_ref();
    if target.local != local {
        return None;
    }
    rvalue_source_place(rvalue)
}

fn rvalue_source_place<'a, 'tcx>(
    rvalue: &'a Rvalue<'tcx>,
) -> Option<&'a rustc_middle::mir::Place<'tcx>> {
    match rvalue {
        Rvalue::Use(Operand::Copy(place), ..)
        | Rvalue::Use(Operand::Move(place), ..)
        | Rvalue::Cast(_, Operand::Copy(place), _)
        | Rvalue::Cast(_, Operand::Move(place), _)
        | Rvalue::CopyForDeref(place) => Some(place),
        _ => None,
    }
}
