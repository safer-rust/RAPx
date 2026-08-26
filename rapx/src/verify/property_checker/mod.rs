//! Unified property checker for the symbolic VM.
//!
//! `PropertyChecker::check` is the entry point; `check_inner` dispatches each
//! `PropertyKind` to a per-family `check_*` method living in one of the sibling
//! submodules (`memory`, `bounds`, `typed`, `numeric`, `string`, `alias`,
//! `cstr`, `transmute`).  Shared helpers live in `util`.

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use z3::{
    Solver,
    ast::{Ast, Bool, Int},
};

use crate::verify::{
    contract::{Property, PropertyKind},
    report::CheckResult,
};
use crate::helpers::mir_scan::Checkpoint;
use crate::verify::vm::state::VmState;

mod alias;
mod bounds;
mod cstr;
mod memory;
mod numeric;
mod string;
mod transmute;
mod typed;
mod util;

pub struct PropertyChecker;

impl PropertyChecker {
    pub fn check<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        let solver = Solver::new(vm_state.ctx);
        vm_state.assert_all(&solver);
        self.check_inner(vm_state, &solver, checkpoint, property)
    }

    fn check_inner<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
        solver: &Solver<'ctx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        // Vacuous truth: properties with unwrap_some() / iter() projections
        // are trivially true when the container value cannot be resolved to
        // a meaningful pointer (e.g. Option::None has no provenance).
        if self.is_vacuously_true_for_nullable(vm_state, checkpoint, property) {
            return CheckResult::Proved;
        }
        match property {
            Property::Or(_) => self.check_or(vm_state, solver, checkpoint, property),
            Property::Leaf(leaf) => match leaf.kind {
                PropertyKind::Align => self.check_align(vm_state, solver, checkpoint, property),
                PropertyKind::NonNull => self.check_non_null(vm_state, solver, checkpoint, property),
                PropertyKind::Null => self.check_null(vm_state, solver, checkpoint, property),
                PropertyKind::Allocated => self.check_allocated(vm_state, solver, checkpoint, property),
                PropertyKind::InBound => self.check_in_bound(vm_state, solver, checkpoint, property),
                PropertyKind::Init => self.check_init(vm_state, solver, checkpoint, property),
                PropertyKind::Typed => self.check_typed(vm_state, solver, checkpoint, property),
                PropertyKind::Alias => self.check_alias(vm_state, solver, checkpoint, property),
                PropertyKind::Owning => self.check_owning(vm_state, solver, checkpoint, property),
                PropertyKind::Alive => self.check_alive(vm_state, solver, checkpoint, property),
                PropertyKind::NonOverlap => self.check_non_overlap(vm_state, solver, checkpoint, property),
                PropertyKind::NonVolatile => CheckResult::Proved,
                PropertyKind::ValidNum => self.check_valid_num(vm_state, solver, checkpoint, property),
                PropertyKind::ValidString => self.check_valid_string(vm_state, solver, checkpoint, property),
                PropertyKind::ValidCStr => self.check_valid_cstr(vm_state, solver, checkpoint, property),
                PropertyKind::ValidTransmute => {
                    self.check_valid_transmute(vm_state, solver, checkpoint, property)
                }
                PropertyKind::SplitTransmute => {
                    self.check_split_transmute(vm_state, solver, checkpoint, property)
                }
                PropertyKind::Trait => self.check_trait(vm_state, solver, checkpoint, property),
                PropertyKind::Size => self.check_size(vm_state, property),

                _ => CheckResult::Unknown,
            },
        }
    }

    fn check_or<'ctx, 'tcx>(&self, vm_state: &VmState<'ctx, 'tcx>, solver: &Solver<'ctx>,
        checkpoint: &Checkpoint<'tcx>, property: &Property<'tcx>) -> CheckResult
    {
        // OR semantics: proved if any group is fully proved; failed only if
        // *every* group is definitely violated; unknown otherwise.
        let mut overall: Option<CheckResult> = None;
        for group in property.groups() {
            let mut group_acc: Option<CheckResult> = None;
            for p in group {
                let result = self.check_inner(vm_state, solver, checkpoint, p);
                group_acc = Some(match group_acc {
                    Some(prev) => prev.and(result),
                    None => result,
                });
            }
            // An empty group is vacuously proved.
            let group_result = group_acc.unwrap_or(CheckResult::Proved);
            overall = Some(match overall {
                Some(prev) => prev.or(group_result),
                None => group_result,
            });
        }
        overall.unwrap_or(CheckResult::Failed)
    }
}

/// Check if the source-level function signature has a named lifetime in return type.
pub(super) fn signature_return_has_lifetime(tcx: TyCtxt<'_>, def_id: DefId) -> Option<(String, String)> {
    let local = def_id.as_local()?;
    let hir_id = tcx.local_def_id_to_hir_id(local);
    let span = tcx.hir_span(hir_id);
    let snippet = tcx.sess.source_map().span_to_snippet(span).ok()?;
    let start = snippet.find("fn ")?;
    let rest = &snippet[start..];
    let end = rest.find('{').unwrap_or(rest.len());
    let sig = &rest[..end];
    // Extract return type after "->"
    let ret = sig.split("->").nth(1)?;
    let ret = ret.split("where").next()?.trim();
    Some((sig.to_string(), ret.to_string()))
}

/// Build the boolean expression "`bytes` form a valid UTF-8 sequence".
///
/// Encodes the UTF-8 DFA over the per-byte Z3 terms: every byte is ASCII, a
/// continuation byte, or a valid lead byte, and a `k`-byte lead must be
/// followed by exactly `k-1` continuation bytes.  Value-range refinements
/// reject overlong encodings, surrogates (U+D800..=U+DFFF), and code points
/// above U+10FFFF.
pub(super) fn utf8_validity<'ctx>(ctx: &'ctx z3::Context, bytes: &[Int<'ctx>]) -> Bool<'ctx> {
    let zero = Int::from_u64(ctx, 0);
    let one = Int::from_u64(ctx, 1);
    let two = Int::from_u64(ctx, 2);
    let three = Int::from_u64(ctx, 3);

    let c_0x80 = Int::from_u64(ctx, 0x80);
    let c_0xc0 = Int::from_u64(ctx, 0xC0);
    let c_0xc2 = Int::from_u64(ctx, 0xC2);
    let c_0xe0 = Int::from_u64(ctx, 0xE0);
    let c_0xf0 = Int::from_u64(ctx, 0xF0);
    let c_0xf5 = Int::from_u64(ctx, 0xF5);
    let c_0xa0 = Int::from_u64(ctx, 0xA0);
    let c_0x90 = Int::from_u64(ctx, 0x90);
    let c_0xed = Int::from_u64(ctx, 0xED);
    let c_0xf4 = Int::from_u64(ctx, 0xF4);

    let mut valid = Bool::from_bool(ctx, true);
    // Number of continuation bytes still pending for the current multi-byte
    // sequence (0..=3).  `lead` holds the lead byte (only meaningful while a
    // multi-byte sequence is open).
    let mut state = zero.clone();
    let mut lead = zero.clone();

    for b in bytes {
        let is_ascii = b.lt(&c_0x80);
        let is_cont = b.ge(&c_0x80) & b.lt(&c_0xc0);
        let is_2lead = b.ge(&c_0xc2) & b.lt(&c_0xe0);
        let is_3lead = b.ge(&c_0xe0) & b.lt(&c_0xf0);
        let is_4lead = b.ge(&c_0xf0) & b.lt(&c_0xf5);

        // Overlong / surrogate / >U+10FFFF refinements on the first
        // continuation byte.  Each disjunct is vacuous unless `lead` equals the
        // constrained lead byte.
        let refine_3 = (lead._eq(&c_0xe0).not() | b.ge(&c_0xa0))
            & (lead._eq(&c_0xed).not() | b.lt(&c_0xa0));
        let refine_4 = (lead._eq(&c_0xf0).not() | b.ge(&c_0x90))
            & (lead._eq(&c_0xf4).not() | b.lt(&c_0x90));

        let valid_s0 = is_ascii.clone() | is_2lead.clone() | is_3lead.clone() | is_4lead.clone();
        let valid_s1 = is_cont.clone();
        let valid_s2 = is_cont.clone() & refine_3;
        let valid_s3 = is_cont.clone() & refine_4;

        let state0 = state._eq(&zero);
        let state1 = state._eq(&one);
        let state2 = state._eq(&two);

        let byte_valid = Bool::ite(
            &state0,
            &valid_s0,
            &Bool::ite(&state1, &valid_s1, &Bool::ite(&state2, &valid_s2, &valid_s3)),
        );

        let new_state_s0 = Bool::ite(
            &is_ascii,
            &zero,
            &Bool::ite(&is_2lead, &one, &Bool::ite(&is_3lead, &two, &three)),
        );
        let new_state_cont = Bool::ite(&state1, &zero, &Bool::ite(&state2, &one, &two));
        let new_state = Bool::ite(&state0, &new_state_s0, &new_state_cont);

        valid = valid & byte_valid;
        // Remember a 3-/4-byte lead so its first continuation is refined.
        let is_lead34 = is_3lead | is_4lead;
        lead = Bool::ite(&(state0 & is_lead34), b, &lead);
        state = new_state;
    }

    valid = valid & state._eq(&zero);
    valid
}
