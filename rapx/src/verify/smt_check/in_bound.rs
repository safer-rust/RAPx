//! SMT lowering for the `InBound` safety property.
//!
//! The current implementation handles the common slice pattern:
//!
//! ```text
//! ptr = slice.as_ptr()
//! current = ptr.add(index)
//! guard: index < slice.len()
//! property: InBound(current, T, n)
//! ```
//!
//! The module only lowers the property to `SmtObligation::InBounds`.  The
//! common SMT model is responsible for matching `as_ptr`, `ptr.add`, `len`, and
//! branch facts from the forward visit result.

use super::common::{SmtCheckResult, SmtChecker, SmtObligation, SmtTerm};
use crate::verify::def_use::PlaceKey;
use crate::verify::{
    contract::{ContractExpr, Property, PropertyArg},
    call_summary::fn_simulator,
    verifier::ForwardVisitResult,
};

use crate::helpers::mir_scan::Checkpoint;

/// Check `InBound` by lowering it to a common bounds obligation.
pub(crate) fn check<'tcx>(
    checker: &SmtChecker<'tcx>,
    checkpoint: &Checkpoint<'tcx>,
    property: &Property<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
) -> SmtCheckResult {
    if let Some(reason) = super::field_invariant::discharge_from_contract_fact_with_checkpoint(
        property, forward, checkpoint,
    ) {
        return SmtCheckResult::proved(format!("InBound proved: {reason}"));
    }

    // An `InBound(index_access(slice, indices))` over an array that a preceding
    // `get_disjoint`-style validator has checked is discharged by that trusted
    // summary.  Checked up front because the array-index contract does not
    // always rebind to a resolvable place at the call site.
    if property
        .args
        .iter()
        .any(|arg| matches!(arg, PropertyArg::Expr(ContractExpr::IndexAccess { .. })))
        && checker.checkpoint_uses_validated_array(checkpoint, forward)
    {
        return SmtCheckResult::proved(
            "InBound proved: indices validated in-bounds by a preceding disjoint check",
        );
    }

    if let Some(predicates) =
        checker.property_index_access_in_bound_predicates(checkpoint, property)
    {
        return checker.prove_obligation(
            checkpoint,
            forward,
            SmtObligation::Predicate { predicates },
            property.null_guard.as_ref(),
        );
    }

    let Some(target) = checker.property_target(Some(checkpoint), property) else {
        rap_debug!("  [SMT InBound] target could not be resolved");
        return SmtCheckResult::unknown("InBound target could not be resolved");
    };
    let Some(required_ty) = checker
        .property_required_ty(Some(checkpoint), property)
        .or_else(|| checker.infer_pointee_ty(checkpoint.caller, &target))
    else {
        rap_debug!("  [SMT InBound] type could not be resolved");
        return SmtCheckResult::unknown("InBound type could not be resolved");
    };
    let elem_size = checker
        .type_layout(checkpoint.caller, required_ty)
        .map(|(_, s)| s)
        .unwrap_or(0);
    let access_count = checker
        .property_len_expr(Some(checkpoint), property)
        .and_then(|expr| checker.contract_expr_to_smt_term(checkpoint.caller, &expr, None))
        .unwrap_or(SmtTerm::Const(1));

    if let Some(obligation) =
        pointer_arithmetic_obligation(checker, checkpoint, required_ty, access_count.clone())
    {
        // Direct static-backed InBound proof: when the base pointer traces
        // to a known static/const allocation, compare offset<len directly.
        if let SmtObligation::PointerRangeInBounds {
            place, upper_delta, ..
        } = &obligation
        {
            if let Some(result) =
                prove_static_backed_pointer_range(checker, checkpoint, place, upper_delta)
            {
                return result;
            }
        }
        return checker.prove_obligation(
            checkpoint,
            forward,
            obligation,
            property.null_guard.as_ref(),
        );
    }

    checker.prove_obligation(
        checkpoint,
        forward,
        SmtObligation::InBounds {
            place: target,
            ty_name: format!("{required_ty:?}"),
            elem_size,
            access_count,
        },
        property.null_guard.as_ref(),
    )
}

/// Direct check: when pointer arithmetic targets a static/const-backed
/// pointer, prove InBound by comparing the constant offset with the
/// allocation size, without involving the SMT solver.
fn prove_static_backed_pointer_range<'tcx>(
    checker: &SmtChecker<'tcx>,
    checkpoint: &Checkpoint<'tcx>,
    base_place: &PlaceKey,
    upper_delta: &SmtTerm,
) -> Option<SmtCheckResult> {
    use crate::verify::smt_check::valid_cstr::const_bytes_for_local;
    let offset = match upper_delta {
        SmtTerm::Const(n) => *n as usize,
        _ => return None,
    };
    let body = checker.tcx.optimized_mir(checkpoint.caller);
    let base_local = base_place.local()?;
    let root = {
        let parents = crate::verify::smt_check::common::body_parents(checker.tcx, body);
        let mut cur = base_local;
        let mut s = std::collections::HashSet::new();
        while s.insert(cur) {
            if let Some(n) = parents.get(&cur) { cur = *n; } else { break; }
        }
        let mut cur = cur;
        let mut s2 = std::collections::HashSet::new();
        loop {
            if !s2.insert(cur) { break; }
            let mut changed = false;
            for data in body.basic_blocks.iter() {
                for stmt in &data.statements {
                    let assign = match &stmt.kind {
                        rustc_middle::mir::StatementKind::Assign(a) => a,
                        _ => continue,
                    };
                    let (target, rvalue) = assign.as_ref();
                    if target.local != cur || !target.projection.is_empty() { continue; }
                    if let rustc_middle::mir::Rvalue::Cast(_, op, _) = rvalue {
                        match op {
                            rustc_middle::mir::Operand::Copy(p) | rustc_middle::mir::Operand::Move(p)
                                if p.projection.is_empty() => { cur = p.local; changed = true; }
                            _ => {}
                        }
                    }
                }
            }
            if !changed { break; }
        }
        cur
    };
    if let Some(bytes) = const_bytes_for_local(checker.tcx, body, root) {
        if bytes.len() > offset {
            return Some(SmtCheckResult::proved(format!(
                "InBound proved: static-backed pointer, alloc {}B, offset {offset}",
                bytes.len(),
            )));
        }
    }
    None
}

fn pointer_arithmetic_obligation<'tcx>(
    checker: &SmtChecker<'tcx>,
    checkpoint: &Checkpoint<'tcx>,
    required_ty: rustc_middle::ty::Ty<'tcx>,
    count: SmtTerm,
) -> Option<SmtObligation> {
    let callee_name = checker.tcx.def_path_str(checkpoint.callee?);
    if !fn_simulator::is_pointer_arithmetic(&callee_name) {
        return None;
    }

    let base = checker.callsite_arg_place(checkpoint, 0)?;
    let zero = SmtTerm::Const(0);
    let negative_count = SmtTerm::Sub(Box::new(zero.clone()), Box::new(count.clone()));
    let (lower_delta, upper_delta) = if fn_simulator::is_pointer_sub(&callee_name) {
        (negative_count, zero)
    } else if fn_simulator::is_signed_ptr_arith(&callee_name) {
        (count.clone(), count)
    } else {
        (zero, count)
    };

    Some(SmtObligation::PointerRangeInBounds {
        place: base,
        ty_name: format!("{required_ty:?}"),
        lower_delta,
        upper_delta,
    })
}

/// Check `InBound` at a return checkpoint for struct invariant verification.
pub(crate) fn check_for_checkpoint<'tcx>(
    checker: &SmtChecker<'tcx>,
    caller: rustc_hir::def_id::DefId,
    property: &Property<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
) -> SmtCheckResult {
    let Some(target) = checker.property_target(None, property) else {
        return SmtCheckResult::unknown("InBound target could not be resolved");
    };
    let Some(required_ty) = checker.property_required_ty(None, property) else {
        return SmtCheckResult::unknown("InBound type could not be resolved");
    };
    let elem_size = checker
        .type_layout(caller, required_ty)
        .map(|(_, s)| s)
        .unwrap_or(0);
    let Some(access_count_expr) = checker.property_len_expr(None, property) else {
        return SmtCheckResult::unknown("InBound length argument could not be resolved");
    };
    let Some(access_count) = checker.contract_expr_to_smt_term(caller, &access_count_expr, None)
    else {
        return SmtCheckResult::unknown("InBound length argument could not be lowered to SMT");
    };

    checker.prove_obligation_for_checkpoint(
        caller,
        forward,
        SmtObligation::InBounds {
            place: target,
            ty_name: format!("{required_ty:?}"),
            elem_size,
            access_count,
        },
    )
}
