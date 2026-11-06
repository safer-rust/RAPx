//! Property checks for the symbolic VM.

use crate::verify::checkpoint::Checkpoint;
use crate::verify::vm::state::VmState;
use crate::verify::{
    contract::{ContractExpr, PlaceBase, Property, PropertyArg, PropertyKind},
    report::{CheckResult, UnknownReason},
};

mod alias;
mod auto_trait;
mod bounds;
mod cstr;
mod memory;
mod numeric;
mod string;
mod transmute;
mod typed;
mod util;

pub(crate) use auto_trait::{
    atomic_update_check, contain_no_type_check, field_invariant_check, no_internal_mut_check,
    no_raw_ptr_check, ref_send_check, uni_internal_mut_check,
};

pub(crate) struct PropertyChecker;

/// Dispatch entry for a [`PropertyKind`].
pub(crate) struct PropertyRule {
    pub name: &'static str,
    pub kind: PropertyKind,
    pub apply: for<'z3, 'tcx> fn(
        &PropertyChecker,
        &VmState<'z3, 'tcx>,
        &Checkpoint<'tcx>,
        &Property<'tcx>,
    ) -> CheckResult,
}

/// `NonVolatile` is uncheckable: the VM does not model volatile access, so
/// there is nothing to disprove.  Treated as satisfied (Proved) as a documented
/// soundness assumption — analysed code is assumed not to mix volatile and
/// non-volatile access.  Revisit if volatile tracking is ever added.
fn check_non_volatile<'z3, 'tcx>(
    _checker: &PropertyChecker,
    _vm_state: &VmState<'z3, 'tcx>,
    _checkpoint: &Checkpoint<'tcx>,
    _property: &Property<'tcx>,
) -> CheckResult {
    CheckResult::ProvedByRule
}

/// Fallback for `PropertyKind`s without a dedicated checker (`Unwrap`, `Pinned`,
/// `Opened`, `Unreachable`, `Unknown`, …): reported `Unknown`.
fn check_unknown<'z3, 'tcx>(
    _checker: &PropertyChecker,
    _vm_state: &VmState<'z3, 'tcx>,
    _checkpoint: &Checkpoint<'tcx>,
    _property: &Property<'tcx>,
) -> CheckResult {
    CheckResult::Unknown(UnknownReason::UnsupportedProperty)
}

/// Every property rule, in dispatch order.
pub(crate) const PROPERTY_RULES: &[PropertyRule] = &[
    PropertyRule {
        name: "align",
        kind: PropertyKind::Align,
        apply: PropertyChecker::check_align,
    },
    PropertyRule {
        name: "non_null",
        kind: PropertyKind::NonNull,
        apply: PropertyChecker::check_non_null,
    },
    PropertyRule {
        name: "null",
        kind: PropertyKind::Null,
        apply: PropertyChecker::check_null,
    },
    PropertyRule {
        name: "allocated",
        kind: PropertyKind::Allocated,
        apply: PropertyChecker::check_allocated,
    },
    PropertyRule {
        name: "in_bound",
        kind: PropertyKind::InBound,
        apply: PropertyChecker::check_in_bound,
    },
    PropertyRule {
        name: "slice_offset",
        kind: PropertyKind::SliceOffset,
        apply: PropertyChecker::check_slice_offset,
    },
    PropertyRule {
        name: "init",
        kind: PropertyKind::Init,
        apply: PropertyChecker::check_init,
    },
    PropertyRule {
        name: "typed",
        kind: PropertyKind::Typed,
        apply: PropertyChecker::check_typed,
    },
    PropertyRule {
        name: "alias",
        kind: PropertyKind::Alias,
        apply: PropertyChecker::check_alias,
    },
    PropertyRule {
        name: "owning",
        kind: PropertyKind::Owning,
        apply: PropertyChecker::check_owning,
    },
    PropertyRule {
        name: "alive",
        kind: PropertyKind::Alive,
        apply: PropertyChecker::check_alive,
    },
    PropertyRule {
        name: "non_overlap",
        kind: PropertyKind::NonOverlap,
        apply: PropertyChecker::check_non_overlap,
    },
    PropertyRule {
        name: "non_volatile",
        kind: PropertyKind::NonVolatile,
        apply: check_non_volatile,
    },
    PropertyRule {
        name: "valid_num",
        kind: PropertyKind::ValidNum,
        apply: PropertyChecker::check_valid_num,
    },
    PropertyRule {
        name: "valid_string",
        kind: PropertyKind::ValidString,
        apply: PropertyChecker::check_valid_string,
    },
    PropertyRule {
        name: "valid_cstr",
        kind: PropertyKind::ValidCStr,
        apply: PropertyChecker::check_valid_cstr,
    },
    PropertyRule {
        name: "valid_transmute",
        kind: PropertyKind::ValidTransmute,
        apply: PropertyChecker::check_valid_transmute,
    },
    PropertyRule {
        name: "split_transmute",
        kind: PropertyKind::SplitTransmute,
        apply: PropertyChecker::check_split_transmute,
    },
    PropertyRule {
        name: "trait",
        kind: PropertyKind::Trait,
        apply: PropertyChecker::check_trait,
    },
    PropertyRule {
        name: "size",
        kind: PropertyKind::Size,
        apply: PropertyChecker::check_size,
    },
    PropertyRule {
        name: "no_padding",
        kind: PropertyKind::NoPadding,
        apply: PropertyChecker::check_no_padding,
    },
    PropertyRule {
        name: "contain_no_type",
        kind: PropertyKind::ContainNoType,
        apply: PropertyChecker::check_contain_no_type,
    },
    PropertyRule {
        name: "no_raw_ptr",
        kind: PropertyKind::NoRawPtr,
        apply: PropertyChecker::check_no_raw_ptr,
    },
    PropertyRule {
        name: "no_internal_mut",
        kind: PropertyKind::NoInternalMut,
        apply: PropertyChecker::check_no_internal_mut,
    },
    PropertyRule {
        name: "uni_internal_mut",
        kind: PropertyKind::UniInternalMut,
        apply: PropertyChecker::check_uni_internal_mut,
    },
    PropertyRule {
        name: "atomic_update",
        kind: PropertyKind::AtomicUpdate,
        apply: PropertyChecker::check_atomic_update,
    },
    PropertyRule {
        name: "ref_send",
        kind: PropertyKind::RefSend,
        apply: PropertyChecker::check_ref_send,
    },
];

/// Fallback rule for kinds with no dedicated checker.
pub(crate) const UNKNOWN_RULE: PropertyRule = PropertyRule {
    name: "unknown",
    kind: PropertyKind::Unknown,
    apply: check_unknown,
};

impl PropertyChecker {
    pub(crate) fn check<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
        structural: bool,
        reachability_cache: &std::cell::Cell<Option<z3::SatResult>>,
    ) -> CheckResult {
        if vm_state.path_infeasible {
            return CheckResult::ProvedByRule;
        }
        if vm_state.diagnostics.unsupported_mir {
            let mut details: Vec<_> = vm_state
                .diagnostics
                .unsupported_details
                .iter()
                .cloned()
                .collect();
            details.sort();
            let mut effect_details: Vec<_> = vm_state
                .diagnostics
                .unsupported_effects
                .iter()
                .cloned()
                .collect();
            effect_details.sort();
            let mut missing_mir: Vec<_> = vm_state.diagnostics.missing_mir.iter().cloned().collect();
            missing_mir.sort();
            let mut opaque_control_flow: Vec<_> =
                vm_state.diagnostics.opaque_control_flow.iter().cloned().collect();
            opaque_control_flow.sort();
            let mut reasons = Vec::new();
            if !missing_mir.is_empty() {
                reasons.push(UnknownReason::MissingMir(missing_mir));
            }
            if !opaque_control_flow.is_empty() {
                reasons.push(UnknownReason::OpaqueControlFlow(opaque_control_flow));
            }
            if details.is_empty() && effect_details.is_empty() && reasons.is_empty() {
                details.push("MIR operation could not be modeled (location unavailable)".to_string());
            }
            if !details.is_empty() {
                reasons.push(UnknownReason::UnsupportedMir(details));
            }
            if !effect_details.is_empty() {
                reasons.push(UnknownReason::UnsupportedEffect(effect_details));
            }
            return CheckResult::Unknown(if reasons.len() == 1 {
                reasons.pop().unwrap()
            } else {
                UnknownReason::Multiple(reasons)
            });
        }
        let result = self.check_inner(vm_state, checkpoint, property);
        if !structural || result.is_proved() {
            return result;
        }
        let reachable = if let Some(result) = reachability_cache.get() {
            result
        } else {
            let reachability = z3::Solver::new(vm_state.z3_ctx);
            vm_state.assert_path_constraints(&reachability);
            let result = reachability.check();
            if result != z3::SatResult::Unknown {
                reachability_cache.set(Some(result));
            }
            result
        };
        if reachable == z3::SatResult::Unsat {
            CheckResult::ProvedBySmt
        } else {
            result
        }
    }

    fn check_inner<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        // Vacuous truth (implicit): a property whose target place carries an
        // `unwrap_some()` / `iter()` projection is trivially satisfied when the
        // container resolves to no allocation (e.g. `Option::None`).  This is
        // distinct from the explicit `Null(p)` guard in `any(Null(p), …)`,
        // which is a `PropertyKind::Null` disjunct handled by `check_null`.
        if self.is_vacuously_true_for_nullable(vm_state, checkpoint, property) {
            return CheckResult::ProvedByRule;
        }
        if let Property::Atom(atom) = property
            && property.for_each().is_some()
        {
            let Some(alloc_id) = self
                .target_value(vm_state, checkpoint, property)
                .and_then(|value| value.provenance_alloc_id())
            else {
                return CheckResult::Unknown(UnknownReason::Unimplemented);
            };
            if vm_state.content(alloc_id).indexed_elements_modified {
                return CheckResult::Unknown(UnknownReason::Unimplemented);
            }
            let facts = &vm_state.alloc(alloc_id).facts.for_each;
            let expected_ty = property.args().get(1).and_then(|arg| match arg {
                PropertyArg::Ty(ty) => Some(*ty),
                _ => None,
            });
            let established = match atom.kind {
                PropertyKind::Align => expected_ty.is_some() && facts.aligned_ty == expected_ty,
                PropertyKind::Allocated => facts
                    .allocated
                    .as_ref()
                    .is_some_and(|(ty, _)| Some(*ty) == expected_ty),
                PropertyKind::Typed => expected_ty.is_some() && facts.target_ty == expected_ty,
                PropertyKind::Owning => facts.owning,
                _ => true,
            };
            if !established {
                return CheckResult::Unknown(UnknownReason::Unimplemented);
            }
        }
        match property {
            Property::Or(_) => self.check_or(vm_state, checkpoint, property),
            Property::And(_) => self.check_and(vm_state, checkpoint, property),
            Property::Atom(atom) => {
                if atom.kind == PropertyKind::Unknown {
                    let callee = checkpoint.callee_name(vm_state.tcx);
                    return CheckResult::Unknown(UnknownReason::MissingContract(format!(
                        "{callee} at {} bb{}",
                        vm_state.tcx.def_path_str(checkpoint.caller),
                        checkpoint.block.as_usize(),
                    )));
                }
                let target_arg = property.args().first().and_then(|arg| match arg {
                    PropertyArg::Expr(ContractExpr::Place(place)) => match place.base {
                        PlaceBase::Arg(index) => Some(index),
                        _ => None,
                    },
                    PropertyArg::Expr(ContractExpr::Const(index)) => usize::try_from(*index).ok(),
                    _ => None,
                });
                let target_alloc_id = self
                    .target_value(vm_state, checkpoint, property)
                    .and_then(|value| value.provenance_alloc_id());
                if target_alloc_id
                    .is_some_and(|id| vm_state.callback_may_drop.contains(&vm_state.root_alloc(id)))
                {
                    return CheckResult::Unknown(UnknownReason::CallbackMayInvalidate);
                }
                if atom.kind == PropertyKind::Init
                    && (target_alloc_id
                        .is_some_and(|id| vm_state.possible_uninit_allocs.contains(&id))
                        || target_arg
                            .and_then(|index| checkpoint.args.get(index))
                            .and_then(|arg| arg.place())
                            .and_then(|place| vm_state.current_frame.local_alloc.get(&place.local))
                            .is_some_and(|id| vm_state.possible_uninit_allocs.contains(id)))
                {
                    return CheckResult::Failed;
                }
                // A property whose target value (or a checkpoint argument it
                // reads) depends on a truncated inline cannot be decided:
                // report `Unknown` instead of failing on the placeholder term.
                for (terms, reason) in [
                    (
                        &vm_state.inline.inline_truncated_terms,
                        UnknownReason::InlineDepthExceeded,
                    ),
                    (
                        &vm_state.inline.inline_branch_terms,
                        UnknownReason::IncompleteInlineBranch,
                    ),
                    (
                        &vm_state.inline.opaque_intrinsic_terms,
                        UnknownReason::UnmodeledIntrinsic("opaque intrinsic result".to_string()),
                    ),
                ] {
                    if vm_state.atom_depends_on_inline_terms(checkpoint, property, terms) {
                        return CheckResult::Unknown(reason);
                    }
                }
                if vm_state.diagnostics.incomplete_inline_branch
                    && (checkpoint.callee.is_some() || !checkpoint.args.is_empty())
                {
                    return CheckResult::Unknown(UnknownReason::IncompleteInlineBranch);
                }
                let rule = PROPERTY_RULES
                    .iter()
                    .find(|r| r.kind == atom.kind)
                    .unwrap_or(&UNKNOWN_RULE);
                crate::rap_debug!("property rule: {}", rule.name);
                let result = (rule.apply)(self, vm_state, checkpoint, property);
                if vm_state.diagnostics.incomplete_inline_branch && result == CheckResult::Failed {
                    CheckResult::Unknown(UnknownReason::IncompleteInlineBranch)
                } else {
                    result
                }
            }
        }
    }

    fn check_or<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        // OR semantics: proved if any disjunct is proved; failed only if every
        // disjunct is definitely violated; otherwise unknown.  An empty
        // disjunction is unsatisfiable, hence Failed.
        let mut overall = CheckResult::Failed;
        for disjunct in property.disjuncts() {
            let result = self.check_inner(vm_state, checkpoint, disjunct);
            overall = overall.or(result);
        }
        overall
    }

    fn check_and<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        // AND semantics: proved if every conjunct is proved; failed if any is
        // definitely violated; otherwise unknown.  An empty conjunction is
        // vacuously proved.
        let mut overall = CheckResult::ProvedByRule;
        for conjunct in property.conjuncts() {
            let result = self.check_inner(vm_state, checkpoint, conjunct);
            overall = overall.and(result);
        }
        overall
    }
}
