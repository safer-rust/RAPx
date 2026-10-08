//! Unified property checker for the symbolic VM.
//!
//! `PropertyChecker::check` is the entry point; `check_inner` dispatches each
//! `PropertyKind` to a per-family `check_*` method living in one of the sibling
//! submodules (`memory`, `bounds`, `typed`, `numeric`, `string`, `alias`,
//! `cstr`, `transmute`).  Shared helpers live in `util`.

use z3::Solver;

use crate::helpers::mir_scan::Checkpoint;
use crate::verify::vm::state::VmState;
use crate::verify::{
    contract::{Property, PropertyKind},
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

impl PropertyChecker {
    pub(crate) fn check<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        let solver = Solver::new(vm_state.z3_ctx);
        vm_state.assert_all(&solver);
        self.check_inner(vm_state, &solver, checkpoint, property)
    }

    fn check_inner<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        solver: &Solver<'z3>,
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
        match property {
            Property::Or(_) => self.check_or(vm_state, solver, checkpoint, property),
            Property::And(_) => self.check_and(vm_state, solver, checkpoint, property),
            Property::Atom(atom) => match atom.kind {
                PropertyKind::Align => self.check_align(vm_state, checkpoint, property),
                PropertyKind::NonNull => {
                    self.check_non_null(vm_state, checkpoint, property)
                }
                PropertyKind::Null => self.check_null(vm_state, checkpoint, property),
                PropertyKind::Allocated => {
                    self.check_allocated(vm_state, checkpoint, property)
                }
                PropertyKind::InBound => {
                    self.check_in_bound(vm_state, solver, checkpoint, property)
                }
                PropertyKind::Init => self.check_init(vm_state, checkpoint, property),
                PropertyKind::Typed => self.check_typed(vm_state, checkpoint, property),
                PropertyKind::Alias => self.check_alias(vm_state, checkpoint),
                PropertyKind::Owning => self.check_owning(vm_state, checkpoint, property),
                PropertyKind::Alive => self.check_alive(vm_state, checkpoint, property),
                PropertyKind::NonOverlap => {
                    self.check_non_overlap(vm_state, solver, checkpoint, property)
                }
                // `NonVolatile` is uncheckable: the VM does not model volatile
                // access, so there is nothing to disprove.  Treated as
                // satisfied (Proved) as a documented soundness assumption —
                // analysed code is assumed not to mix volatile and non-volatile
                // access.  Revisit if volatile tracking is ever added.
                PropertyKind::NonVolatile => CheckResult::ProvedByRule,
                PropertyKind::ValidNum => {
                    self.check_valid_num(vm_state, solver, checkpoint, property)
                }
                PropertyKind::ValidString => {
                    self.check_valid_string(vm_state, solver, checkpoint, property)
                }
                PropertyKind::ValidCStr => {
                    self.check_valid_cstr(vm_state, solver, checkpoint, property)
                }
                PropertyKind::ValidTransmute => {
                    self.check_valid_transmute(vm_state, property)
                }
                PropertyKind::SplitTransmute => {
                    self.check_split_transmute(vm_state, checkpoint, property)
                }
                PropertyKind::Trait => self.check_trait(vm_state, checkpoint, property),
                PropertyKind::Size => self.check_size(vm_state, checkpoint, property),
                PropertyKind::NoPadding => {
                    self.check_no_padding(vm_state, checkpoint, property)
                }
                PropertyKind::ContainNoType => {
                    self.check_contain_no_type(vm_state, checkpoint, property)
                }
                PropertyKind::NoRawPtr => {
                    self.check_no_raw_ptr(vm_state, checkpoint, property)
                }
                PropertyKind::NoInternalMut => {
                    self.check_no_internal_mut(vm_state, property)
                }
                PropertyKind::UniInternalMut => {
                    self.check_uni_internal_mut(vm_state, property)
                }
                PropertyKind::AtomicUpdate => {
                    self.check_atomic_update(vm_state, checkpoint, property)
                }
                PropertyKind::RefSend => {
                    self.check_ref_send(vm_state, checkpoint, property)
                }

                _ => CheckResult::Unknown(UnknownReason::Unimplemented),
            },
        }
    }

    fn check_or<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        solver: &Solver<'z3>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        // OR semantics: proved if any disjunct is proved; failed only if every
        // disjunct is definitely violated; otherwise unknown.  An empty
        // disjunction is unsatisfiable, hence Failed.
        let mut overall = CheckResult::Failed;
        for disjunct in property.disjuncts() {
            let result = self.check_inner(vm_state, solver, checkpoint, disjunct);
            overall = overall.or(result);
        }
        overall
    }

    fn check_and<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        solver: &Solver<'z3>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        // AND semantics: proved if every conjunct is proved; failed if any is
        // definitely violated; otherwise unknown.  An empty conjunction is
        // vacuously proved.
        let mut overall = CheckResult::ProvedByRule;
        for conjunct in property.conjuncts() {
            let result = self.check_inner(vm_state, solver, checkpoint, conjunct);
            overall = overall.and(result);
        }
        overall
    }
}
