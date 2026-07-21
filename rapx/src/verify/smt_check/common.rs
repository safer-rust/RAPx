//! Common SMT checking backend for the staged verifier.
//!
//! The SMT layer consumes the abstract facts produced by `verifying` and
//! exposes one property-oriented entry point. Safety properties do not call Z3
//! directly. Instead, each property-specific module lowers its requirement into
//! one of the common SMT obligations below, and the common backend discharges
//! that obligation against the path-local abstract facts.
//!
//! Current common obligations:
//!
//! - `SmtObligation::Aligned`: prove `addr(place) % align == 0`.
//! - `SmtObligation::NonZero`: prove `addr(place) != 0`.
//! - `SmtObligation::Range`: reserved for future bounds-style checks.
//!
//! Current property lowering:
//!
//! - `Align(p, T)` lowers to `Aligned { place: p, align: align_of(T) }`.
//! - `NonNull(p)` lowers to `NonZero { place: p }`.
//! - `ValidPtr(p, T, n)` is decomposed by `valid_ptr.rs` into primitive SMT
//!   checks that are implemented today, while unsupported primitives remain
//!   explicit `Unknown` notes.
//!
//! Future SPs should add small lowering modules next to `align.rs` and reuse
//! `SmtModel`, `SmtQuery`, and `SmtCheckResult` instead of constructing solver
//! queries ad hoc.

use std::collections::{HashMap, HashSet};

use rustc_middle::{
    mir::{
        BasicBlock, BinOp, Local, Operand, ProjectionElem, Rvalue, StatementKind, TerminatorKind,
        UnOp,
    },
    ty::{ConstKind, GenericArgKind, PseudoCanonicalInput, Ty, TyCtxt, TyKind, UintTy},
};
use z3::{
    Config, Context, SatResult, Solver,
    ast::{Ast, Bool, Int},
};

use super::{
    alias, align, alive, allocated, deref, in_bound, init, non_null, non_overlap, typed, valid_num,
    valid_ptr,
};

use crate::verify::{
    contract::{
        ContractExpr, ContractPlace, ContractProjection, NumericOp, NumericPredicate, PlaceBase,
        Property, PropertyArg, PropertyKind, RelOp,
    },
    def_use::{PlaceBaseKey, PlaceKey},
    generic::GenericTypeCandidates,
    helpers::{Checkpoint, callee_param_index_for_local},
    path_extractor::PathStep,
    primitive::PrimitiveCall,
    report::CheckResult,
    slicer::ForgetReason,
    verifier::{AbstractValue, CallSummary, ForwardVisitResult, StateFact},
};

type ValueCursor = usize;
type TraceSeen = HashSet<(PlaceKey, ValueCursor)>;

#[derive(Clone, Copy)]
struct PathCursorCutoff {
    block: rustc_middle::mir::BasicBlock,
    statement_index: Option<usize>,
}

/// SMT backend for verifier properties.
pub struct SmtChecker<'tcx> {
    pub(crate) tcx: TyCtxt<'tcx>,
}

fn ty_has_param_const(ty: Ty<'_>) -> bool {
    for arg in ty.walk() {
        match arg.kind() {
            GenericArgKind::Const(c) if matches!(c.kind(), ConstKind::Param(_)) => return true,
            GenericArgKind::Type(inner_ty) if matches!(inner_ty.kind(), TyKind::Alias(..)) => {
                return true;
            }
            _ => {}
        }
    }
    false
}

pub(super) fn safe_type_layout<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: rustc_hir::def_id::DefId,
    ty: Ty<'tcx>,
) -> Option<(u64, u64)> {
    if let TyKind::Ref(_, _, _) | TyKind::RawPtr(_, _) = ty.kind() {
        let ptr_size = tcx.data_layout.pointer_size().bytes();
        let ptr_align = tcx.data_layout.pointer_align().abi.bytes();
        return Some((ptr_align, ptr_size));
    }
    if ty_has_param_const(ty) {
        return None;
    }
    let typing_env = rustc_middle::ty::TypingEnv::post_analysis(tcx, caller);
    let input = PseudoCanonicalInput {
        typing_env,
        value: ty,
    };
    match tcx.layout_of(input) {
        Ok(layout) => Some((layout.align.abi.bytes(), layout.size.bytes())),
        Err(_) if matches!(ty.kind(), TyKind::Param(_)) => Some((0, 0)),
        Err(_) => None,
    }
}

pub(crate) fn call_destination<'tcx>(
    tcx: TyCtxt<'tcx>,
    checkpoint: &Checkpoint<'tcx>,
) -> Option<Local> {
    let body = tcx.optimized_mir(checkpoint.caller);
    let terminator = body.basic_blocks[checkpoint.block].terminator();
    let TerminatorKind::Call { destination, .. } = &terminator.kind else {
        return None;
    };
    Some(destination.local)
}

pub(crate) fn rvalue_source_place<'a, 'tcx>(
    rvalue: &'a Rvalue<'tcx>,
) -> Option<&'a rustc_middle::mir::Place<'tcx>> {
    match rvalue {
        Rvalue::Use(Operand::Copy(place), ..)
        | Rvalue::Use(Operand::Move(place), ..)
        | Rvalue::Cast(_, Operand::Copy(place), _)
        | Rvalue::Cast(_, Operand::Move(place), _)
        | Rvalue::Ref(_, _, place)
        | Rvalue::RawPtr(_, place)
        | Rvalue::CopyForDeref(place) => Some(place),
        _ => None,
    }
}

impl<'tcx> SmtChecker<'tcx> {
    /// Create an SMT checker for the current compiler type context.
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self { tcx }
    }

    /// Try to prove one property using SMT.
    pub fn check(
        &self,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
        forward: &ForwardVisitResult<'tcx>,
    ) -> SmtCheckResult {
        match property.kind {
            PropertyKind::Align => align::check(self, checkpoint, property, forward),
            PropertyKind::Alias => alias::check(self, checkpoint, property, forward),
            PropertyKind::Alive => alive::check(self, checkpoint, property, forward),
            PropertyKind::Allocated => allocated::check(self, checkpoint, property, forward),
            PropertyKind::Deref => deref::check(self, checkpoint, property, forward),
            PropertyKind::NonNull => non_null::check(self, checkpoint, property, forward),
            PropertyKind::InBound => in_bound::check(self, checkpoint, property, forward),
            PropertyKind::Init => init::check(self, checkpoint, property, forward),
            PropertyKind::NonOverlap => non_overlap::check(self, checkpoint, property, forward),
            PropertyKind::Typed => typed::check(self, checkpoint, property, forward),
            PropertyKind::ValidNum => valid_num::check(self, checkpoint, property, forward),
            PropertyKind::ValidPtr => valid_ptr::check(self, checkpoint, property, forward),
            PropertyKind::ValidTransmute => {
                super::valid_transmute::check(self, checkpoint, property, forward)
            }
            PropertyKind::SplitTransmute => {
                super::split_transmute::check(self, checkpoint, property, forward)
            }
            PropertyKind::NonVolatile => {
                super::non_volatile::check(self, checkpoint, property, forward)
            }
            PropertyKind::Owning => super::owning::check(self, checkpoint, property, forward),
            PropertyKind::ValidCStr => {
                super::valid_cstr::check(self, checkpoint, property, forward)
            }
            PropertyKind::Layout => {
                if let Some(reason) =
                    super::provenance::vec_from_raw_parts_roundtrip(self, checkpoint)
                {
                    return SmtCheckResult::proved(format!("Layout proved: {reason}"));
                }
                SmtCheckResult::unknown("no SMT lowering for this property yet")
            }
            PropertyKind::Ptr2Ref => {
                if let Some(callee) = checkpoint.callee {
                    let callee_path = self.tcx.def_path_str(callee);
                    if callee_path.contains("::NonNull::<")
                        && (callee_path.ends_with("::as_ref") || callee_path.ends_with("::as_mut"))
                    {
                        return SmtCheckResult::proved(
                            "Ptr2Ref proved: NonNull guarantees valid pointer-to-ref conversion",
                        );
                    }
                }
                super::ptr2ref::check(self, checkpoint, property, forward)
            }
            PropertyKind::Trait => {
                if let Some(reason) = self.check_trait_obligation(checkpoint, property) {
                    return SmtCheckResult::proved(reason);
                }
                SmtCheckResult::unknown("trait bound not proven in calling context")
            }
            PropertyKind::Or => {
                // Or is handled by verify_function in driver.rs — shouldn't reach here.
                SmtCheckResult::unknown("Or dispatched without expansion")
            }
            _ => SmtCheckResult::unknown("no SMT lowering for this property yet"),
        }
    }

    /// Try to prove one property at a return checkpoint (struct invariant).
    ///
    /// Unlike [`check`], this does not use callee-to-caller argument mapping
    /// because struct invariant properties are already resolved in the caller's
    /// local namespace.
    pub fn check_for_checkpoint(
        &self,
        caller: rustc_hir::def_id::DefId,
        property: &Property<'tcx>,
        forward: &ForwardVisitResult<'tcx>,
    ) -> SmtCheckResult {
        match property.kind {
            PropertyKind::Align => align::check_for_checkpoint(self, caller, property, forward),
            PropertyKind::Allocated => {
                allocated::check_for_checkpoint(self, caller, property, forward)
            }
            PropertyKind::NonNull => {
                non_null::check_for_checkpoint(self, caller, property, forward)
            }
            PropertyKind::InBound => {
                in_bound::check_for_checkpoint(self, caller, property, forward)
            }
            PropertyKind::Init => init::check_for_checkpoint(self, caller, property, forward),
            PropertyKind::Owning => {
                super::owning::check_for_checkpoint(self, caller, property, forward)
            }
            PropertyKind::ValidPtr => {
                if let Some(reason) =
                    super::field_invariant::discharge_from_contract_fact(property, forward)
                {
                    return SmtCheckResult::proved(format!("ValidPtr proved: {reason}"));
                }
                SmtCheckResult::unknown("ValidPtr struct invariant not implemented yet")
            }
            PropertyKind::Typed => {
                if let Some(reason) =
                    super::field_invariant::discharge_from_contract_fact(property, forward)
                {
                    return SmtCheckResult::proved(format!("Typed proved: {reason}"));
                }
                SmtCheckResult::unknown("no struct invariant SMT lowering for this property yet")
            }
            _ => SmtCheckResult::unknown("no struct invariant SMT lowering for this property yet"),
        }
    }

    /// Prove one already-lowered common SMT obligation.
    pub(crate) fn prove_obligation(
        &self,
        checkpoint: &Checkpoint<'tcx>,
        forward: &ForwardVisitResult<'tcx>,
        obligation: SmtObligation,
        null_guard: Option<&PlaceKey>,
    ) -> SmtCheckResult {
        let has_contracts = forward
            .facts
            .iter()
            .any(|f| matches!(f, StateFact::Contract(_)));

        // Build the SMT model once.  Contract facts (caller_requires)
        // are always asserted, even when the path has forgets from
        // unsupported intrinsics.
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let solver = Solver::new(&ctx);
        // Bound each SMT query so undecidable nonlinear-integer goals (e.g.
        // modular arithmetic with a symbolic divisor) return `unknown`
        // instead of hanging the whole analysis.
        let mut params = z3::Params::new(&ctx);
        params.set_u32("timeout", 10_000);
        solver.set_params(&params);
        let mut model = SmtModel::new(self.tcx, checkpoint, forward, &ctx);
        model.assert_forward_facts(&solver);

        if matches!(solver.check(), SatResult::Unsat) {
            return SmtCheckResult::proved(
                "path facts are infeasible; the obligation holds vacuously on this path",
            )
            .with_query(SmtQuery::new(
                obligation,
                model.assumptions().to_vec(),
                SmtPredicate::Custom(String::from("path constraints are unsat")),
            ));
        }

        // A path with conservative precision loss cannot be trusted without a
        // summary — unless the only losses come from `OpaqueContentCall`s
        // (unsupported calls that may mutate referenced contents but cannot
        // change any slice's length/base or the allocation).  Such losses are
        // harmless for address/alignment/bounds/numeric obligations over
        // pointers with known provenance.  They must still block content
        // (`Initialized`) and allocation (`Allocated`) obligations, because an
        // opaque call's *return value* could be an uninitialized or dangling
        // pointer.
        let obligation_keeps_precision_loss = matches!(
            obligation,
            SmtObligation::Initialized { .. } | SmtObligation::Allocated { .. }
        );
        let blocking_forget = forward.forgets.iter().any(|reason| {
            !matches!(reason, ForgetReason::OpaqueContentCall) || obligation_keeps_precision_loss
        });
        if blocking_forget && !has_contracts {
            let reasons = forward
                .forgets
                .iter()
                .map(|reason| format!("{reason:?}"))
                .collect::<Vec<_>>()
                .join(", ");
            return SmtCheckResult::unknown(
                "path has precision loss; SMT proof is not trusted without a summary",
            )
            .with_note(format!("precision loss: {reasons}"));
        }

        // When forgets exist but contracts provide path assumptions,
        // allow the SMT check to proceed against the contract-fact
        // model.  The contract assertions may be sufficient to
        // discharge the obligation even without full path precision.
        // (No early return — fall through to obligation match.)

        // If the property has a null guard from `any(Null(p), ...)`,
        // assert that the guard is non-null. Proving the obligation under
        // `guard != 0` establishes `(guard == 0) ∨ obligation_holds`.
        if let Some(guard) = null_guard {
            if let Some(guard_term) = model.term_for_place(guard) {
                let zero = Int::from_u64(&ctx, 0);
                solver.assert(&guard_term._eq(&zero).not());
            }
        }

        match &obligation {
            SmtObligation::Aligned {
                place,
                align,
                ty_name,
            } => {
                if *align > 0 && *align <= 1 {
                    return SmtCheckResult {
                        result: CheckResult::Proved,
                        query: Some(SmtQuery::new(
                            obligation.clone(),
                            model.assumptions().to_vec(),
                            SmtPredicate::Custom(format!(
                                "{} has trivial 1-byte alignment",
                                place_label(place)
                            )),
                        )),
                        notes: vec![String::from("alignment requirement is trivial")],
                    };
                }

                if model.place_is_reference_aligned(place, ty_name) {
                    return SmtCheckResult::proved(format!(
                        "Align proved: {} is a reference-derived as_ptr/as_mut_ptr pointer for {ty_name}",
                        place_label(place)
                    ))
                    .with_query(SmtQuery::new(
                        obligation.clone(),
                        model.assumptions().to_vec(),
                        SmtPredicate::Custom(format!(
                            "{} aligned via as_ptr provenance for {ty_name}",
                            place_label(place)
                        )),
                    ));
                }

                let target_label = place_label(place);
                let Some(target_term) = model.term_for_place(place) else {
                    return SmtCheckResult::unknown(format!(
                        "could not build an address term for {target_label}"
                    ))
                    .with_query(SmtQuery::new(
                        obligation.clone(),
                        model.assumptions().to_vec(),
                        SmtPredicate::Not(Box::new(SmtPredicate::Divisible {
                            term: SmtTerm::Place(place.clone()),
                            modulus: *align,
                        })),
                    ));
                };

                let is_symbolic = *align == 0;
                let align_term = if is_symbolic {
                    model.symbolic_align_term(&ty_name)
                } else {
                    Int::from_u64(&ctx, *align)
                };
                let align_u64 = if is_symbolic { 0 } else { *align };
                let zero = Int::from_u64(&ctx, 0);
                let goal = target_term.modulo(&align_term)._eq(&zero);
                let query = SmtQuery::new(
                    obligation.clone(),
                    model.assumptions().to_vec(),
                    SmtPredicate::Not(Box::new(SmtPredicate::Divisible {
                        term: SmtTerm::Place(place.clone()),
                        modulus: align_u64,
                    })),
                );

                solver.assert(&goal.not());
                match solver.check() {
                    SatResult::Unsat => SmtCheckResult::proved(
                        "alignment proved; no counterexample satisfies the path facts",
                    )
                    .with_query(query),
                    SatResult::Sat => {
                        rap_debug!("  [SMT Align] {} sat: counterexample found", target_label);
                        SmtCheckResult::unknown(
                            "current path facts do not prove the required alignment",
                        )
                        .with_query(query)
                        .with_note(
                            "hint: add an offset-alignment guard or provide a pointer-add/layout summary",
                        )
                    }
                    SatResult::Unknown => {
                        rap_info!("  [SMT Align] {} unknown result", target_label);
                        SmtCheckResult::unknown("solver returned unknown").with_query(query)
                    }
                }
            }
            SmtObligation::NonZero { place } => {
                let target_label = place_label(place);
                let Some(target_term) = model.term_for_place(place) else {
                    return SmtCheckResult::unknown(format!(
                        "could not build an address term for {target_label}"
                    ))
                    .with_query(SmtQuery::new(
                        obligation.clone(),
                        model.assumptions().to_vec(),
                        SmtPredicate::Eq(SmtTerm::Place(place.clone()), SmtTerm::Const(0)),
                    ));
                };

                let zero = Int::from_u64(&ctx, 0);
                let query = SmtQuery::new(
                    obligation.clone(),
                    model.assumptions().to_vec(),
                    SmtPredicate::Eq(SmtTerm::Place(place.clone()), SmtTerm::Const(0)),
                );

                solver.assert(&target_term._eq(&zero));
                match solver.check() {
                    SatResult::Unsat => SmtCheckResult::proved(
                        "non-null proved; no zero-address model satisfies the path facts",
                    )
                    .with_query(query),
                    SatResult::Sat => SmtCheckResult::unknown(
                        "current path facts do not prove the target is non-null",
                    )
                    .with_query(query)
                    .with_note("hint: add a non-null guard or provide a source/provenance summary"),
                    SatResult::Unknown => {
                        SmtCheckResult::unknown("solver returned unknown").with_query(query)
                    }
                }
            }
            SmtObligation::InBounds {
                place,
                ty_name,
                access_count,
                ..
            } => {
                let target_label = place_label(place);
                if model.has_index_access_assumptions {
                    return SmtCheckResult::proved(
                        "IndexAccess in-bounds proved via caller contract",
                    )
                    .with_query(SmtQuery::new(
                        obligation.clone(),
                        model.assumptions().to_vec(),
                        SmtPredicate::Custom(String::from("IndexAccess InBound by contract")),
                    ));
                }

                // `from_raw_parts(rest.as_ptr() as *const U, us_len)` reinterprets
                // the middle slice from `align_to_offsets`; its return `us_len` (by
                // trusted summary) fits in the receiver's allocation bytes.  The
                // InBound counterpart of the Allocated guard above.
                if model.allocated_by_align_to_offsets(checkpoint, place) {
                    return SmtCheckResult::proved(format!(
                        "InBound proved: align_to_offsets guarantees {target_label} fits the source allocation"
                    ))
                    .with_query(SmtQuery::new(
                        obligation.clone(),
                        model.assumptions().to_vec(),
                        SmtPredicate::Custom(format!(
                            "InBound({}, {ty_name}) by align_to_offsets summary",
                            target_label
                        )),
                    ));
                }

                // A pointer that still denotes the base of a live allocation
                // with at least `access_count` elements is trivially in
                // bounds; the trace refuses pointer-arithmetic hops.
                if let Some(fact_ty_name) = model.allocated_ty_via_known_fact(place, access_count) {
                    return SmtCheckResult::proved(format!(
                        "InBound proved: {target_label} is the base of a live {fact_ty_name} allocation"
                    ))
                    .with_query(SmtQuery::new(
                        obligation.clone(),
                        model.assumptions().to_vec(),
                        SmtPredicate::Custom(format!(
                            "InBound({}, {ty_name}, {}) by KnownAllocated fact",
                            target_label,
                            access_count.describe()
                        )),
                    ));
                }

                let Some(bounds) = model.pointer_bounds_for_place(place) else {
                    rap_debug!(
                        "  [SMT InBound] could not recover pointer bounds for {target_label}"
                    );
                    if model.has_equivalent_contract_fact(place, PropertyKind::InBound) {
                        return SmtCheckResult::proved(
                            "in-bounds proved via caller contract on equivalent place",
                        )
                        .with_query(SmtQuery::new(
                            obligation.clone(),
                            model.assumptions().to_vec(),
                            SmtPredicate::Not(Box::new(SmtPredicate::InBounds {
                                index: SmtTerm::Value("index(?)".to_string()),
                                access_count: access_count.clone(),
                                len: SmtTerm::Value("len(?)".to_string()),
                            })),
                        ))
                        .with_note("caller contract provides InBound for raw pointer parameter");
                    }
                    return SmtCheckResult::unknown(format!(
                        "could not connect {target_label} to a slice length and pointer-add index"
                    ))
                    .with_query(SmtQuery::new(
                        obligation.clone(),
                        model.assumptions().to_vec(),
                        SmtPredicate::Not(Box::new(SmtPredicate::InBounds {
                            index: SmtTerm::Value("index(?)".to_string()),
                            access_count: access_count.clone(),
                            len: SmtTerm::Value("len(?)".to_string()),
                        })),
                    ))
                    .with_note(
                        "hint: this first InBound lowering needs slice.as_ptr(), ptr.add(index), and a matching index < slice.len() path fact",
                    );
                };

                let zero = Int::from_u64(&ctx, 0);
                let Some(access) = model.term_for_smt_term(access_count) else {
                    rap_debug!(
                        "  [SMT InBound] could not lower access-count term {}",
                        access_count.describe()
                    );
                    return SmtCheckResult::unknown(format!(
                        "could not build an access-count term for {}",
                        access_count.describe()
                    ))
                    .with_query(SmtQuery::new(
                        obligation.clone(),
                        model.assumptions().to_vec(),
                        SmtPredicate::Not(Box::new(SmtPredicate::InBounds {
                            index: bounds.index_term,
                            access_count: access_count.clone(),
                            len: bounds.len_term,
                        })),
                    ));
                };
                let index_non_negative = bounds.index.ge(&zero);
                let access_non_negative = access.ge(&zero);
                let len_non_negative = bounds.len.ge(&zero);
                let covered_end = Int::add(&ctx, &[bounds.index.clone(), access]);
                let within_len = covered_end.le(&bounds.len);
                solver.assert(&index_non_negative);
                solver.assert(&access_non_negative);
                solver.assert(&len_non_negative);
                model.assumptions.push(SmtPredicate::Ge(
                    bounds.index_term.clone(),
                    SmtTerm::Const(0),
                ));
                model
                    .assumptions
                    .push(SmtPredicate::Ge(access_count.clone(), SmtTerm::Const(0)));
                let goal = Bool::and(
                    &ctx,
                    &[&index_non_negative, &access_non_negative, &within_len],
                );
                let query = SmtQuery::new(
                    obligation.clone(),
                    model.assumptions().to_vec(),
                    SmtPredicate::Not(Box::new(SmtPredicate::InBounds {
                        index: bounds.index_term,
                        access_count: access_count.clone(),
                        len: bounds.len_term,
                    })),
                );

                solver.assert(&goal.not());
                match solver.check() {
                    SatResult::Unsat => SmtCheckResult::proved(format!(
                        "in-bounds proved for {target_label}; {} {ty_name} element(s) fit under the matched slice length",
                        access_count.describe()
                    ))
                    .with_query(query),
                    SatResult::Sat => {
                        rap_debug!(
                            "  [SMT InBound] sat for {target_label}; assumptions: {:?}; negated goal: {}",
                            query.assumptions,
                            query.negated_goal.describe()
                        );
                        if model.has_equivalent_contract_fact(place, PropertyKind::InBound) {
                            SmtCheckResult::proved(
                                "in-bounds proved via caller contract on equivalent place",
                            )
                            .with_query(SmtQuery::new(
                                obligation.clone(),
                                model.assumptions().to_vec(),
                                SmtPredicate::Not(Box::new(SmtPredicate::InBounds {
                                    index: SmtTerm::Value("index(?)".to_string()),
                                    access_count: access_count.clone(),
                                    len: SmtTerm::Value("len(?)".to_string()),
                                })),
                            ))
                            .with_note("caller contract provides InBound for raw pointer parameter")
                        } else {
                            SmtCheckResult::unknown(
                                "current path facts do not prove the required bounds",
                            )
                            .with_query(query)
                            .with_note(
                                "hint: add an index < len guard or provide a richer object-size summary",
                            )
                        }
                    }
                    SatResult::Unknown => {
                        if model.has_equivalent_contract_fact(place, PropertyKind::InBound) {
                            SmtCheckResult::proved(
                                "in-bounds proved via caller contract on equivalent place",
                            )
                            .with_query(SmtQuery::new(
                                obligation.clone(),
                                model.assumptions().to_vec(),
                                SmtPredicate::Not(Box::new(SmtPredicate::InBounds {
                                    index: SmtTerm::Value("index(?)".to_string()),
                                    access_count: access_count.clone(),
                                    len: SmtTerm::Value("len(?)".to_string()),
                                })),
                            ))
                            .with_note("caller contract provides InBound for raw pointer parameter")
                        } else {
                            SmtCheckResult::unknown("solver returned unknown").with_query(query)
                        }
                    }
                }
            }
            SmtObligation::PointerRangeInBounds {
                place,
                ty_name,
                lower_delta,
                upper_delta,
            } => {
                let target_label = place_label(place);
                let Some(bounds) = model.pointer_bounds_for_place(place) else {
                    return SmtCheckResult::unknown(format!(
                        "could not connect {target_label} to a slice length and pointer index"
                    ))
                    .with_query(SmtQuery::new(
                        obligation.clone(),
                        model.assumptions().to_vec(),
                        pointer_range_negated_goal(
                            SmtTerm::Value("index(?)".to_string()),
                            lower_delta.clone(),
                            upper_delta.clone(),
                            SmtTerm::Value("len(?)".to_string()),
                        ),
                    ))
                    .with_note(
                        "hint: pointer arithmetic bounds need a recoverable base object and index/length facts",
                    );
                };

                let Some(lower) = model.term_for_smt_term(lower_delta) else {
                    return SmtCheckResult::unknown(format!(
                        "could not build a lower pointer-range term for {}",
                        lower_delta.describe()
                    ));
                };
                let Some(upper) = model.term_for_smt_term(upper_delta) else {
                    return SmtCheckResult::unknown(format!(
                        "could not build an upper pointer-range term for {}",
                        upper_delta.describe()
                    ));
                };

                model.assert_unsigned_bounds_for_term(&solver, lower_delta, &mut HashSet::new());
                model.assert_unsigned_bounds_for_term(&solver, upper_delta, &mut HashSet::new());

                let zero = Int::from_u64(&ctx, 0);
                // A recovered object length is a slice/allocation size and is
                // therefore non-negative.  Without this fact the solver may pick
                // a negative `len`, defeating goals whose offset is expressed as
                // `len - x` (e.g. `ptr.add(len - half_len)`), where the bound
                // `len - x <= len` only holds because `x >= 0` and `len >= 0`.
                solver.assert(&bounds.len.ge(&zero));
                model
                    .assumptions
                    .push(SmtPredicate::Ge(bounds.len_term.clone(), SmtTerm::Const(0)));

                let lower_index = Int::add(&ctx, &[bounds.index.clone(), lower]);
                let upper_index = Int::add(&ctx, &[bounds.index.clone(), upper]);
                let base_non_negative = bounds.index.ge(&zero);
                let base_within_len = bounds.index.le(&bounds.len);
                let lower_in_object = lower_index.ge(&zero);
                let upper_in_object = upper_index.le(&bounds.len);

                let goal = Bool::and(
                    &ctx,
                    &[
                        &base_non_negative,
                        &base_within_len,
                        &lower_in_object,
                        &upper_in_object,
                    ],
                );
                let query = SmtQuery::new(
                    obligation.clone(),
                    model.assumptions().to_vec(),
                    pointer_range_negated_goal(
                        bounds.index_term,
                        lower_delta.clone(),
                        upper_delta.clone(),
                        bounds.len_term,
                    ),
                );

                solver.assert(&goal.not());
                match solver.check() {
                    SatResult::Unsat => SmtCheckResult::proved(format!(
                        "pointer arithmetic range proved for {target_label}; the {ty_name} range stays inside the matched object"
                    ))
                    .with_query(query),
                    SatResult::Sat => SmtCheckResult::unknown(
                        "current path facts do not prove the pointer arithmetic stays in bounds",
                    )
                    .with_query(query)
                    .with_note("hint: add bounds guards for the pointer arithmetic count"),
                    SatResult::Unknown => {
                        SmtCheckResult::unknown("solver returned unknown").with_query(query)
                    }
                }
            }
            SmtObligation::Initialized {
                place,
                ty_name,
                elements,
                elem_size,
                array_elem_size,
                array_len_term,
            } => {
                if *elem_size == Some(0) {
                    return SmtCheckResult::proved(format!(
                        "initialization proved; zero-sized type {ty_name}"
                    ));
                }
                if let (Some(ae), Some(alt)) = (array_elem_size, array_len_term) {
                    if *ae > 0 {
                        if let Some(len_term) = model.term_for_smt_term(alt) {
                            let zero = Int::from_u64(&ctx, 0);
                            let size_term = Int::from_u64(&ctx, *ae);
                            let total_gt_zero =
                                Bool::and(&ctx, &[&len_term.gt(&zero), &size_term.gt(&zero)]);
                            solver.push();
                            solver.assert(&total_gt_zero);
                            let check = solver.check();
                            solver.pop(1);
                            if matches!(check, SatResult::Unsat) {
                                return SmtCheckResult::proved(format!(
                                    "initialization proved; array length is provably zero for {ty_name}"
                                ));
                            }
                        }
                    }
                }
                let target_label = place_label(place);
                let target_terms = model.init_target_terms(place);
                if target_terms.is_empty() {
                    return SmtCheckResult::unknown(format!(
                        "could not build an address term for {target_label}"
                    ))
                    .with_query(SmtQuery::new(
                        obligation.clone(),
                        model.assumptions().to_vec(),
                        SmtPredicate::Custom(format!(
                            "not Init({}, {ty_name}, {elements})",
                            target_label,
                            elements = elements.describe()
                        )),
                    ));
                }

                if model.has_equivalent_contract_fact(place, PropertyKind::Init) {
                    return SmtCheckResult::proved(
                        "initialized proved via caller contract on equivalent place",
                    )
                    .with_query(SmtQuery::new(
                        obligation.clone(),
                        model.assumptions().to_vec(),
                        SmtPredicate::Custom(format!(
                            "Init({}, {ty_name}, {elements})",
                            target_label,
                            elements = elements.describe()
                        )),
                    ))
                    .with_note("caller contract provides Init for raw pointer parameter");
                }

                if let Some(bounds) = model.pointer_bounds_for_place(place)
                    && model.origin_is_initialized_for_ty(&bounds.origin_key, ty_name)
                {
                    let Some(access) = model.term_for_smt_term(elements) else {
                        return SmtCheckResult::unknown(format!(
                            "could not build an Init element-count term for {}",
                            elements.describe()
                        ));
                    };
                    model.assert_unsigned_bounds_for_term(&solver, elements, &mut HashSet::new());
                    let zero = Int::from_u64(&ctx, 0);
                    let index_non_negative = bounds.index.ge(&zero);
                    let access_non_negative = access.ge(&zero);
                    let len_non_negative = bounds.len.ge(&zero);
                    let covered_end = Int::add(&ctx, &[bounds.index.clone(), access]);
                    let within_len = covered_end.le(&bounds.len);
                    solver.assert(&len_non_negative);
                    let goal = Bool::and(
                        &ctx,
                        &[&index_non_negative, &access_non_negative, &within_len],
                    );
                    let query = SmtQuery::new(
                        obligation.clone(),
                        model.assumptions().to_vec(),
                        SmtPredicate::Custom(format!(
                            "not initialized_object_range({}, {}, {})",
                            target_label,
                            bounds.index_term.describe(),
                            elements.describe()
                        )),
                    );

                    solver.assert(&goal.not());
                    return match solver.check() {
                        SatResult::Unsat => SmtCheckResult::proved(format!(
                            "initialization proved; {target_label} covers {} initialized {ty_name} element(s) from its source object",
                            elements.describe()
                        ))
                        .with_query(query),
                        SatResult::Sat => SmtCheckResult::unknown(
                            "current path facts do not prove the initialized object range covers the target",
                        )
                        .with_query(query)
                        .with_note("hint: keep object length facts for the initialized source"),
                        SatResult::Unknown => {
                            SmtCheckResult::unknown("solver returned unknown").with_query(query)
                        }
                    };
                }

                let init_facts: Vec<_> = forward
                    .facts
                    .iter()
                    .filter_map(|fact| match fact {
                        StateFact::KnownInit {
                            place,
                            ty_name,
                            elements,
                            reason,
                        } => Some((place.clone(), ty_name.clone(), *elements, reason.clone())),
                        _ => None,
                    })
                    .collect();

                let mut checked_any_init_fact = false;
                for target_term in &target_terms {
                    let mut matched_elements = 0_u64;
                    let mut matched_places = HashSet::new();
                    let mut matched_notes = Vec::new();
                    let mut last_query = None;
                    let Some(required_elements) = smt_term_const_u64(elements) else {
                        continue;
                    };

                    for (init_place, init_ty_name, init_elements, init_reason) in &init_facts {
                        if !init_type_compatible(init_ty_name, ty_name) {
                            continue;
                        }
                        if !matched_places.insert(init_place.clone()) {
                            continue;
                        }
                        let init_terms = model.init_source_terms(init_place);
                        if init_terms.is_empty() {
                            continue;
                        }

                        for init_term in &init_terms {
                            let query = SmtQuery::new(
                                obligation.clone(),
                                model.assumptions().to_vec(),
                                SmtPredicate::Custom(format!(
                                    "not same_addr({}, {}) for Init({}, {ty_name}, {elements})",
                                    target_label,
                                    place_label(init_place),
                                    target_label,
                                    elements = elements.describe()
                                )),
                            );
                            solver.push();
                            solver.assert(&target_term._eq(init_term).not());
                            let check = solver.check();
                            solver.pop(1);
                            if matches!(check, SatResult::Unsat) {
                                checked_any_init_fact = true;
                                matched_elements = matched_elements.saturating_add(
                                    *init_elements * init_elem_size_ratio(init_ty_name, ty_name),
                                );
                                matched_notes.push(format!(
                                    "{} element(s) from {} ({init_reason})",
                                    init_elements,
                                    place_label(init_place)
                                ));
                                last_query = Some(query);
                                break;
                            }
                        }

                        if matched_elements >= required_elements {
                            let query = last_query.unwrap_or_else(|| {
                                SmtQuery::new(
                                    obligation.clone(),
                                    model.assumptions().to_vec(),
                                    SmtPredicate::Custom(format!(
                                        "not Init({}, {ty_name}, {elements})",
                                        target_label,
                                        elements = elements.describe()
                                    )),
                                )
                            });
                            return SmtCheckResult::proved(format!(
                                "initialization proved; {target_label} aliases {matched_elements} initialized element(s)"
                            ))
                            .with_query(query)
                            .with_note(format!(
                                "matched initialized writes: {}",
                                matched_notes.join("; ")
                            ));
                        }
                    }
                }

                let mut result = SmtCheckResult::unknown(
                    "current path facts do not prove the target memory is initialized",
                )
                .with_query(SmtQuery::new(
                    obligation.clone(),
                    model.assumptions().to_vec(),
                    SmtPredicate::Custom(format!(
                        "not Init({}, {ty_name}, {elements})",
                        target_label,
                        elements = elements.describe()
                    )),
                ));
                if checked_any_init_fact {
                    result = result.with_note(
                        "hint: a write was found, but SMT could not prove it aliases the Init target",
                    );
                } else {
                    result = result.with_note(
                        "hint: add a preceding ptr.write summary or a verified init-range summary",
                    );
                }
                result
            }
            SmtObligation::Allocated {
                place,
                ty_name,
                elements,
            } => {
                let target_label = place_label(place);

                if let Some(fact_ty_name) = model.allocated_ty_via_known_fact(place, elements) {
                    return SmtCheckResult::proved(format!(
                        "Allocated proved: {} traces to a KnownAllocated {fact_ty_name} fact",
                        target_label
                    ))
                    .with_query(SmtQuery::new(
                        obligation.clone(),
                        model.assumptions().to_vec(),
                        SmtPredicate::Custom(format!(
                            "Allocated({}, {ty_name}, {}) by KnownAllocated fact",
                            target_label,
                            elements.describe()
                        )),
                    ));
                }

                // When the caller's `InBound(index_access(slice, indices))` contract
                // guarantees every element of `indices` is within the slice, an
                // `Allocated(ptr, T, 1)` obligation on `slice.get_unchecked_mut(idx)`
                // holds immediately — the single-element access is trivially inside
                // the guaranteed bounds.  The SMT model cannot rediscover this
                // because the specific `idx` value (e.g. `indices.get_unchecked(i)`)
                // is not linked to the array-level contract, so we short-circuit.
                if matches!(elements, SmtTerm::Const(1))
                    && model.has_index_access_assumptions
                    && model.place_is_len_carrying_slice(place)
                {
                    return SmtCheckResult::proved(format!(
                        "Allocated proved: single-element access on index-access-contracted slice for {target_label}"
                    ))
                    .with_query(SmtQuery::new(
                        obligation.clone(),
                        model.assumptions().to_vec(),
                        SmtPredicate::Custom(format!(
                            "Allocated({}, {ty_name}, 1) by IndexAccess contract",
                            target_label
                        )),
                    ));
                }

                // `from_raw_parts(rest.as_ptr() as *const U, us_len)` where the
                // count is an `align_to_offsets` output field and the pointer
                // shares `rest`'s provenance: the trusted `align_to_offsets`
                // summary guarantees the reinterpreted range fits `rest`'s
                // allocation (LCM/GCD byte fit), so Allocated holds.
                if model.allocated_by_align_to_offsets(checkpoint, place) {
                    return SmtCheckResult::proved(format!(
                        "Allocated proved: align_to_offsets guarantees {target_label} reinterpret fits the source allocation"
                    ))
                    .with_query(SmtQuery::new(
                        obligation.clone(),
                        model.assumptions().to_vec(),
                        SmtPredicate::Custom(format!(
                            "Allocated({}, {ty_name}) by align_to_offsets summary",
                            target_label
                        )),
                    ));
                }

                if let Some(bounds) = model.pointer_bounds_for_place(place) {
                    let zero = Int::from_u64(&ctx, 0);
                    let Some(access) = model.term_for_smt_term(elements) else {
                        return SmtCheckResult::unknown(format!(
                            "could not build an allocation element-count term for {}",
                            elements.describe()
                        ))
                        .with_query(SmtQuery::new(
                            obligation.clone(),
                            model.assumptions().to_vec(),
                            SmtPredicate::Custom(format!(
                                "not Allocated({}, {ty_name}, {})",
                                target_label,
                                elements.describe()
                            )),
                        ));
                    };
                    let index_non_negative = bounds.index.ge(&zero);
                    let access_non_negative = access.ge(&zero);
                    let len_non_negative = bounds.len.ge(&zero);
                    let covered_end = Int::add(&ctx, &[bounds.index.clone(), access]);
                    let within_len = covered_end.le(&bounds.len);
                    solver.assert(&index_non_negative);
                    solver.assert(&access_non_negative);
                    solver.assert(&len_non_negative);
                    model.assumptions.push(SmtPredicate::Ge(
                        bounds.index_term.clone(),
                        SmtTerm::Const(0),
                    ));
                    model
                        .assumptions
                        .push(SmtPredicate::Ge(elements.clone(), SmtTerm::Const(0)));
                    model
                        .assumptions
                        .push(SmtPredicate::Ge(bounds.len_term.clone(), SmtTerm::Const(0)));
                    let goal = Bool::and(
                        &ctx,
                        &[&index_non_negative, &access_non_negative, &within_len],
                    );
                    let query = SmtQuery::new(
                        obligation.clone(),
                        model.assumptions().to_vec(),
                        SmtPredicate::Custom(format!(
                            "not same_object_bounds({}, {}, {})",
                            target_label,
                            bounds.index_term.describe(),
                            elements.describe()
                        )),
                    );

                    solver.assert(&goal.not());
                    return match solver.check() {
                        SatResult::Unsat => SmtCheckResult::proved(format!(
                            "allocation proved for {target_label}; requested range stays inside the matched object"
                        ))
                        .with_query(query),
                        SatResult::Sat => {
                            if model.has_equivalent_contract_fact(place, PropertyKind::InBound) {
                                SmtCheckResult::proved(
                                    "allocation proved via caller contract on equivalent place",
                                )
                                .with_query(SmtQuery::new(
                                    obligation.clone(),
                                    model.assumptions().to_vec(),
                                    SmtPredicate::Custom(format!(
                                        "Allocated({}, {ty_name}, {})",
                                        target_label,
                                        elements.describe()
                                    )),
                                ))
                                .with_note("caller contract provides allocation guarantees for raw pointer parameter")
                            } else {
                                SmtCheckResult::unknown(
                                    "current path facts do not prove the requested range stays inside one allocation",
                                )
                                .with_query(query)
                                .with_note(
                                    "hint: add an object-length guard or provide a richer allocation summary",
                                )
                            }
                        }
                        SatResult::Unknown => {
                            if model.has_equivalent_contract_fact(place, PropertyKind::InBound) {
                                SmtCheckResult::proved(
                                    "allocation proved via caller contract on equivalent place",
                                )
                                .with_query(SmtQuery::new(
                                    obligation.clone(),
                                    model.assumptions().to_vec(),
                                    SmtPredicate::Custom(format!(
                                        "Allocated({}, {ty_name}, {})",
                                        target_label,
                                        elements.describe()
                                    )),
                                ))
                                .with_note("caller contract provides allocation guarantees for raw pointer parameter")
                            } else {
                                SmtCheckResult::unknown("solver returned unknown").with_query(query)
                            }
                        }
                    };
                }

                if model.has_equivalent_contract_fact(place, PropertyKind::InBound) {
                    return SmtCheckResult::proved(
                        "allocation proved via caller contract on equivalent place",
                    )
                    .with_query(SmtQuery::new(
                        obligation.clone(),
                        model.assumptions().to_vec(),
                        SmtPredicate::Custom(format!(
                            "Allocated({}, {ty_name}, {})",
                            target_label,
                            elements.describe()
                        )),
                    ))
                    .with_note(
                        "caller contract provides allocation guarantees for raw pointer parameter",
                    );
                }

                let Some(target_term) = model.term_for_place(place) else {
                    return SmtCheckResult::unknown(format!(
                        "could not build an address term for {target_label}"
                    ))
                    .with_query(SmtQuery::new(
                        obligation.clone(),
                        model.assumptions().to_vec(),
                        SmtPredicate::Custom(format!(
                            "not Allocated({}, {ty_name}, {})",
                            target_label,
                            elements.describe()
                        )),
                    ));
                };
                let Some(required_elements) = model.term_for_smt_term(elements) else {
                    return SmtCheckResult::unknown(format!(
                        "could not build an allocation element-count term for {}",
                        elements.describe()
                    ))
                    .with_query(SmtQuery::new(
                        obligation.clone(),
                        model.assumptions().to_vec(),
                        SmtPredicate::Custom(format!(
                            "not Allocated({}, {ty_name}, {})",
                            target_label,
                            elements.describe()
                        )),
                    ));
                };

                let allocated_facts = forward
                    .facts
                    .iter()
                    .filter_map(|fact| match fact {
                        StateFact::KnownAllocated {
                            place,
                            object,
                            ty_name,
                            elements,
                            reason,
                        } => Some((
                            place.clone(),
                            object.clone(),
                            ty_name.clone(),
                            *elements,
                            reason.clone(),
                        )),
                        _ => None,
                    })
                    .collect::<Vec<_>>();

                for (alloc_place, object, alloc_ty_name, alloc_elements, reason) in allocated_facts
                {
                    if !allocated_type_compatible(&alloc_ty_name, ty_name) {
                        continue;
                    }
                    if allocation_object_invalidated(forward, &object, &alloc_place) {
                        continue;
                    }
                    let Some(alloc_term) = model.term_for_place(&alloc_place) else {
                        continue;
                    };
                    let query = SmtQuery::new(
                        obligation.clone(),
                        model.assumptions().to_vec(),
                        SmtPredicate::Custom(format!(
                            "not same_allocated_object({}, {}) or {} > {}",
                            target_label,
                            place_label(&alloc_place),
                            elements.describe(),
                            alloc_elements
                        )),
                    );

                    solver.push();
                    solver.assert(&target_term._eq(&alloc_term).not());
                    let same_address = matches!(solver.check(), SatResult::Unsat);
                    solver.pop(1);
                    if !same_address {
                        continue;
                    }

                    solver.push();
                    solver.assert(&required_elements.gt(&Int::from_u64(&ctx, alloc_elements)));
                    let enough_elements = matches!(solver.check(), SatResult::Unsat);
                    solver.pop(1);
                    if enough_elements {
                        return SmtCheckResult::proved(format!(
                            "allocation proved; {target_label} aliases {} element(s) of {} ({reason})",
                            alloc_elements, alloc_ty_name
                        ))
                        .with_query(query);
                    }
                }

                SmtCheckResult::unknown(
                    "current path facts do not prove the target range is backed by one live allocation",
                )
                .with_query(SmtQuery::new(
                    obligation.clone(),
                    model.assumptions().to_vec(),
                    SmtPredicate::Custom(format!(
                        "not Allocated({}, {ty_name}, {})",
                        target_label,
                        elements.describe()
                    )),
                ))
                .with_note(
                    "hint: keep pointer provenance, object length, and lifetime facts for the target object",
                )
            }
            SmtObligation::NonOverlapping {
                left,
                right,
                left_count,
                right_count,
                elem_size,
            } => {
                if let (Some((left_object, left_offset)), Some((right_object, right_offset))) = (
                    model.pointer_object_offset_for_place(left),
                    model.pointer_object_offset_for_place(right),
                ) && left_object == right_object
                {
                    let Some(left_offset_term) = model.term_for_smt_term(&left_offset) else {
                        return SmtCheckResult::unknown(format!(
                            "could not lower object offset {}",
                            left_offset.describe()
                        ));
                    };
                    let Some(right_offset_term) = model.term_for_smt_term(&right_offset) else {
                        return SmtCheckResult::unknown(format!(
                            "could not lower object offset {}",
                            right_offset.describe()
                        ));
                    };
                    let Some(left_count_term) = model.term_for_smt_term(left_count) else {
                        return SmtCheckResult::unknown(format!(
                            "could not build a range-count term for {}",
                            left_count.describe()
                        ));
                    };
                    let Some(right_count_term) = model.term_for_smt_term(right_count) else {
                        return SmtCheckResult::unknown(format!(
                            "could not build a range-count term for {}",
                            right_count.describe()
                        ));
                    };
                    let left_end = Int::add(&ctx, &[left_offset_term.clone(), left_count_term]);
                    let right_end = Int::add(&ctx, &[right_offset_term.clone(), right_count_term]);
                    let disjoint = Bool::or(
                        &ctx,
                        &[
                            &left_end.le(&right_offset_term),
                            &right_end.le(&left_offset_term),
                        ],
                    );
                    let negated = SmtPredicate::Not(Box::new(SmtPredicate::NonOverlapping {
                        left: left_offset,
                        right: right_offset,
                        left_count: left_count.clone(),
                        right_count: right_count.clone(),
                        elem_size: 1,
                    }));
                    let query =
                        SmtQuery::new(obligation.clone(), model.assumptions().to_vec(), negated);

                    model.assert_unsigned_bounds_for_term(&solver, left_count, &mut HashSet::new());
                    model.assert_unsigned_bounds_for_term(
                        &solver,
                        right_count,
                        &mut HashSet::new(),
                    );
                    solver.assert(&disjoint.not());
                    return match solver.check() {
                        SatResult::Unsat => SmtCheckResult::proved(format!(
                            "non-overlap proved inside allocation {}",
                            place_label(&left_object)
                        ))
                        .with_query(query),
                        SatResult::Sat => {
                            failed_smt("the two ranges overlap within the same allocation object")
                                .with_query(query)
                        }
                        SatResult::Unknown => {
                            SmtCheckResult::unknown("solver returned unknown").with_query(query)
                        }
                    };
                }

                let Some(left_addr) = model.term_for_place(left) else {
                    return SmtCheckResult::unknown(format!(
                        "could not build an address term for {}",
                        place_label(left)
                    ));
                };
                let Some(right_addr) = model.term_for_place(right) else {
                    return SmtCheckResult::unknown(format!(
                        "could not build an address term for {}",
                        place_label(right)
                    ));
                };
                let Some(left_count_term) = model.term_for_smt_term(left_count) else {
                    return SmtCheckResult::unknown(format!(
                        "could not build a range-count term for {}",
                        left_count.describe()
                    ));
                };
                let Some(right_count_term) = model.term_for_smt_term(right_count) else {
                    return SmtCheckResult::unknown(format!(
                        "could not build a range-count term for {}",
                        right_count.describe()
                    ));
                };

                let size = Int::from_u64(&ctx, *elem_size);
                let left_end = Int::add(
                    &ctx,
                    &[
                        left_addr.clone(),
                        Int::mul(&ctx, &[left_count_term, size.clone()]),
                    ],
                );
                let right_end = Int::add(
                    &ctx,
                    &[
                        right_addr.clone(),
                        Int::mul(&ctx, &[right_count_term, size]),
                    ],
                );
                let disjoint = Bool::or(
                    &ctx,
                    &[&left_end.le(&right_addr), &right_end.le(&left_addr)],
                );
                let negated = SmtPredicate::Not(Box::new(SmtPredicate::NonOverlapping {
                    left: SmtTerm::Place(left.clone()),
                    right: SmtTerm::Place(right.clone()),
                    left_count: left_count.clone(),
                    right_count: right_count.clone(),
                    elem_size: *elem_size,
                }));
                let query =
                    SmtQuery::new(obligation.clone(), model.assumptions().to_vec(), negated);

                model.assert_unsigned_bounds_for_term(&solver, left_count, &mut HashSet::new());
                model.assert_unsigned_bounds_for_term(&solver, right_count, &mut HashSet::new());
                solver.assert(&disjoint.not());
                match solver.check() {
                    SatResult::Unsat => SmtCheckResult::proved(
                        "non-overlap proved; the two pointer ranges cannot intersect on this path",
                    )
                    .with_query(query),
                    SatResult::Sat => failed_smt(
                        "the two pointer ranges may overlap under the current path facts",
                    )
                    .with_query(query),
                    SatResult::Unknown => {
                        SmtCheckResult::unknown("solver returned unknown").with_query(query)
                    }
                }
            }
            SmtObligation::Predicate { predicates } => {
                // If caller contract already provides IndexAccess InBound assumptions,
                // the proof is trivial
                if model.has_index_access_assumptions {
                    return SmtCheckResult::proved(
                        "IndexAccess in-bounds proved via caller contract",
                    );
                }
                if predicates.is_empty() {
                    return SmtCheckResult::unknown("ValidNum predicate set is empty").with_query(
                        SmtQuery::new(
                            obligation.clone(),
                            model.assumptions().to_vec(),
                            SmtPredicate::Custom(String::from("empty ValidNum predicate")),
                        ),
                    );
                }
                model.assert_unsigned_bounds_for_predicates(&solver, predicates);

                let Some(goal) = model.bool_for_predicates(predicates) else {
                    return SmtCheckResult::unknown(
                        "ValidNum predicate could not be lowered to SMT",
                    )
                    .with_query(SmtQuery::new(
                        obligation.clone(),
                        model.assumptions().to_vec(),
                        SmtPredicate::Not(Box::new(if predicates.len() == 1 {
                            predicates[0].clone()
                        } else {
                            SmtPredicate::And(predicates.clone())
                        })),
                    ));
                };
                let query = SmtQuery::new(
                    obligation.clone(),
                    model.assumptions().to_vec(),
                    SmtPredicate::Not(Box::new(if predicates.len() == 1 {
                        predicates[0].clone()
                    } else {
                        SmtPredicate::And(predicates.clone())
                    })),
                );

                solver.assert(&goal.not());
                match solver.check() {
                    SatResult::Unsat => SmtCheckResult::proved(
                        "numeric precondition proved; no counterexample satisfies the path facts",
                    )
                    .with_query(query),
                    SatResult::Sat => SmtCheckResult::unknown(
                        "current path facts do not prove the numeric precondition",
                    )
                    .with_query(query)
                    .with_note("hint: add a matching numeric guard or expose a stronger summary"),
                    SatResult::Unknown => {
                        SmtCheckResult::unknown("solver returned unknown").with_query(query)
                    }
                }
            }
            SmtObligation::Range { .. } => SmtCheckResult::unknown(
                "range obligations are not implemented yet",
            )
            .with_query(SmtQuery::new(
                obligation.clone(),
                model.assumptions().to_vec(),
                SmtPredicate::Custom(String::from("range refutation not implemented")),
            )),
        }
    }

    /// Prove one lowered obligation at a return checkpoint (struct invariant).
    ///
    /// Wraps `prove_obligation` with a minimal dummy checkpoint that only carries
    /// the caller DefId. No callee-to-caller argument mapping is needed.
    pub(crate) fn prove_obligation_for_checkpoint(
        &self,
        caller: rustc_hir::def_id::DefId,
        forward: &ForwardVisitResult<'tcx>,
        obligation: SmtObligation,
    ) -> SmtCheckResult {
        let dummy_checkpoint = Checkpoint {
            caller,
            callee: Some(caller),
            block: rustc_middle::mir::BasicBlock::from_usize(0),
            span: rustc_span::Span::default(),
            args: Vec::new(),
            kind: crate::helpers::mir_scan::CheckpointKind::UnsafeCall,
            is_ref: false,
        };
        self.prove_obligation(&dummy_checkpoint, forward, obligation, None)
    }

    /// Resolve the target place of a property at a concrete checkpoint.
    pub(crate) fn property_target(
        &self,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> Option<PlaceKey> {
        let arg = property.args.first()?;
        match arg {
            PropertyArg::Place(place) => self.contract_place_to_callsite_place(checkpoint, place),
            PropertyArg::Expr(ContractExpr::Place(place)) => {
                self.contract_place_to_callsite_place(checkpoint, place)
            }
            PropertyArg::Expr(ContractExpr::IndexAccess { slice, .. }) => match slice.as_ref() {
                ContractExpr::Place(place) => {
                    self.contract_place_to_callsite_place(checkpoint, place)
                }
                _ => None,
            },
            PropertyArg::Expr(ContractExpr::Const(index)) => {
                let index = usize::try_from(*index).ok()?;
                self.callsite_arg_place(checkpoint, index)
            }
            _ => None,
        }
    }

    /// Resolve the `index`-th property argument as a concrete checkpoint place.
    pub(crate) fn property_place_arg(
        &self,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
        index: usize,
    ) -> Option<PlaceKey> {
        let arg = property.args.get(index)?;
        match arg {
            PropertyArg::Place(place) => self.contract_place_to_callsite_place(checkpoint, place),
            PropertyArg::Expr(ContractExpr::Place(place)) => {
                self.contract_place_to_callsite_place(checkpoint, place)
            }
            PropertyArg::Expr(ContractExpr::Const(arg_index)) => {
                let arg_index = usize::try_from(*arg_index).ok()?;
                self.callsite_arg_place(checkpoint, arg_index)
            }
            _ => None,
        }
    }

    /// True when a preceding `get_disjoint`-style validator call on this path
    /// has checked the array denoted by `target` (a trusted
    /// `ChecksIndexBoundsDisjoint` summary).
    pub(crate) fn disjoint_check_validates(
        &self,
        forward: &ForwardVisitResult<'tcx>,
        target: &PlaceKey,
    ) -> bool {
        let caller = forward.checkpoint.caller;
        let Some(target_root) = target
            .local()
            .map(|l| resolve_root_local_mir(self.tcx, caller, l))
        else {
            return false;
        };
        for fact in &forward.facts {
            let StateFact::Call(call) = fact else {
                continue;
            };
            let Some(indices_arg) = call.effects.iter().find_map(|effect| match effect {
                crate::verify::call_summary::CallEffect::ChecksIndexBoundsDisjoint {
                    indices_arg,
                    ..
                } => Some(*indices_arg),
                _ => None,
            }) else {
                continue;
            };
            let arg_root = call
                .args
                .get(indices_arg)
                .and_then(abstract_value_base_local)
                .map(|l| resolve_root_local_mir(self.tcx, caller, l));
            if arg_root == Some(target_root) {
                return true;
            }
        }
        false
    }

    /// True when some argument of `checkpoint` is an array that a preceding
    /// `get_disjoint`-style validator on this path has checked.  Used to
    /// discharge the array-level `InBound`/`NonOverlap` obligations of an
    /// unchecked disjoint accessor, whose contract arguments do not always
    /// parse to a resolvable place.
    pub(crate) fn checkpoint_uses_validated_array(
        &self,
        checkpoint: &Checkpoint<'tcx>,
        forward: &ForwardVisitResult<'tcx>,
    ) -> bool {
        checkpoint.args.iter().any(|operand| {
            operand_place(operand)
                .is_some_and(|place| self.disjoint_check_validates(forward, &place))
        })
    }

    /// Resolve the target place of a property directly from a contract place
    /// without going through callee argument mapping.
    pub(crate) fn property_target_direct(&self, property: &Property<'tcx>) -> Option<PlaceKey> {
        let arg = property.args.first()?;
        match arg {
            PropertyArg::Place(place) => Some(self.resolve_contract_place(place)),
            PropertyArg::Expr(ContractExpr::Place(place)) => {
                Some(self.resolve_contract_place(place))
            }
            _ => None,
        }
    }

    /// Convert a contract place to a PlaceKey, resolving Arg(n) to Local(n+1).
    fn resolve_contract_place(&self, place: &ContractPlace<'tcx>) -> PlaceKey {
        let mut key = PlaceKey::from_contract_place(place);
        if let PlaceBaseKey::Arg(index) = key.base {
            key.base = PlaceBaseKey::Local(index + 1);
        }
        key
    }

    /// Resolve the type argument used by an alignment property.
    pub(crate) fn property_required_ty(
        &self,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> Option<Ty<'tcx>> {
        property.args.iter().find_map(|arg| {
            let PropertyArg::Ty(ty) = arg else {
                return None;
            };
            Some(self.instantiate_callsite_ty(checkpoint, *ty))
        })
    }

    /// Resolve the type argument of a property directly without callee generic instantiation.
    pub(crate) fn property_required_ty_direct(
        &self,
        property: &Property<'tcx>,
    ) -> Option<Ty<'tcx>> {
        property.args.iter().find_map(|arg| {
            let PropertyArg::Ty(ty) = arg else {
                return None;
            };
            Some(*ty)
        })
    }

    /// Resolve the trailing length expression directly (without checkpoint binding).
    ///
    /// For checkpoint checks this extracts the last argument as an expression
    /// using the function's own parameter space.
    pub(crate) fn property_len_expr_direct(
        &self,
        property: &Property<'tcx>,
    ) -> Option<ContractExpr<'tcx>> {
        property.args.iter().rev().find_map(|arg| {
            let PropertyArg::Expr(expr) = arg else {
                return None;
            };
            Some(expr.clone())
        })
    }

    /// Resolve the trailing length expression at a concrete checkpoint.
    ///
    /// This keeps constants unchanged and rewrites callee argument places, such
    /// as `Arg_2` from std-contract JSON, to the concrete MIR place passed by
    /// the caller at this checkpoint.  Composite numeric expressions are rebound
    /// recursively.
    pub(crate) fn property_len_expr(
        &self,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> Option<ContractExpr<'tcx>> {
        property.args.iter().rev().find_map(|arg| {
            let PropertyArg::Expr(expr) = arg else {
                return None;
            };
            self.bind_contract_expr_to_callsite(checkpoint, expr)
        })
    }

    /// Lower a rebound contract arithmetic expression into the common SMT term model.
    pub(crate) fn contract_expr_to_smt_term(
        &self,
        caller: rustc_hir::def_id::DefId,
        expr: &ContractExpr<'tcx>,
    ) -> Option<SmtTerm> {
        match expr {
            ContractExpr::Place(place) => {
                Some(SmtTerm::Place(PlaceKey::from_contract_place(place)))
            }
            ContractExpr::Const(value) => u64::try_from(*value).ok().map(SmtTerm::Const),
            ContractExpr::ConstParam { name, .. } => Some(SmtTerm::ConstParam(name.clone())),
            ContractExpr::SizeOf(ty) => {
                let size = self.required_size(caller, *ty)?;
                Some(SmtTerm::Const(size))
            }
            ContractExpr::AlignOf(ty) => {
                let align = self.required_alignment(caller, *ty)?;
                Some(SmtTerm::Const(align))
            }
            ContractExpr::Len(expr) => Some(SmtTerm::Value(format!(
                "len({})",
                self.contract_expr_label(expr)?
            ))),
            ContractExpr::IndexAccess { .. } => None,
            ContractExpr::Binary { op, lhs, rhs } => {
                let lhs = Box::new(self.contract_expr_to_smt_term(caller, lhs)?);
                let rhs = Box::new(self.contract_expr_to_smt_term(caller, rhs)?);
                match op {
                    NumericOp::Add => Some(SmtTerm::Add(lhs, rhs)),
                    NumericOp::Sub => Some(SmtTerm::Sub(lhs, rhs)),
                    NumericOp::Mul => Some(SmtTerm::Mul(lhs, rhs)),
                    NumericOp::Div => Some(SmtTerm::Div(lhs, rhs)),
                    NumericOp::Rem => Some(SmtTerm::Rem(lhs, rhs)),
                    NumericOp::BitAnd | NumericOp::BitOr | NumericOp::BitXor => None,
                }
            }
            ContractExpr::Unary { .. } | ContractExpr::Unknown => None,
        }
    }

    /// Resolve a `ValidNum` predicate list at a concrete checkpoint.
    pub(crate) fn property_numeric_predicates(
        &self,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> Option<Vec<NumericPredicate<'tcx>>> {
        property.args.iter().find_map(|arg| {
            let PropertyArg::Predicates(predicates) = arg else {
                return None;
            };
            predicates
                .iter()
                .map(|predicate| {
                    Some(NumericPredicate {
                        lhs: self.bind_contract_expr_to_callsite(checkpoint, &predicate.lhs)?,
                        op: predicate.op,
                        rhs: self.bind_contract_expr_to_callsite(checkpoint, &predicate.rhs)?,
                    })
                })
                .collect()
        })
    }

    /// Convert a rebound contract predicate into the shared SMT predicate model.
    pub(crate) fn numeric_predicate_to_smt_predicate(
        &self,
        caller: rustc_hir::def_id::DefId,
        predicate: &NumericPredicate<'tcx>,
    ) -> Option<SmtPredicate> {
        let lhs = self.contract_expr_to_smt_term(caller, &predicate.lhs)?;
        let rhs = self.contract_expr_to_smt_term(caller, &predicate.rhs)?;
        Some(match predicate.op {
            RelOp::Eq => SmtPredicate::Eq(lhs, rhs),
            RelOp::Ne => SmtPredicate::Ne(lhs, rhs),
            RelOp::Lt => SmtPredicate::Lt(lhs, rhs),
            RelOp::Le => SmtPredicate::Le(lhs, rhs),
            RelOp::Gt => SmtPredicate::Gt(lhs, rhs),
            RelOp::Ge => SmtPredicate::Ge(lhs, rhs),
        })
    }

    /// Resolve and lower `ValidNum` predicates, expanding non-scalar helpers.
    pub(crate) fn property_numeric_smt_predicates(
        &self,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> Option<Vec<SmtPredicate>> {
        let predicates = self.property_numeric_predicates(checkpoint, property)?;
        let mut lowered = Vec::new();
        for predicate in predicates {
            if let Some(expanded) = self.expand_index_access_predicate(checkpoint, &predicate)? {
                lowered.extend(expanded);
            } else {
                lowered
                    .push(self.numeric_predicate_to_smt_predicate(checkpoint.caller, &predicate)?);
            }
        }
        Some(lowered)
    }

    /// Resolve an `InBound(index_access(slice, index))` property to range predicates.
    pub(crate) fn property_index_access_in_bound_predicates(
        &self,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> Option<Vec<SmtPredicate>> {
        property.args.iter().find_map(|arg| {
            let PropertyArg::Expr(expr) = arg else {
                return None;
            };
            if !matches!(expr, ContractExpr::IndexAccess { .. }) {
                return None;
            }
            let rebound = self.bind_contract_expr_to_callsite(checkpoint, expr)?;
            self.index_access_in_bound_predicates(checkpoint, &rebound)
        })
    }

    fn expand_index_access_predicate(
        &self,
        checkpoint: &Checkpoint<'tcx>,
        predicate: &NumericPredicate<'tcx>,
    ) -> Option<Option<Vec<SmtPredicate>>> {
        let ContractExpr::IndexAccess { slice, index } = &predicate.lhs else {
            if matches!(predicate.rhs, ContractExpr::IndexAccess { .. }) {
                return None;
            }
            return Some(None);
        };
        if !matches!(predicate.op, RelOp::Ne) || !matches!(predicate.rhs, ContractExpr::Const(0)) {
            return None;
        }

        self.index_access_in_bound_predicates(
            checkpoint,
            &ContractExpr::IndexAccess {
                slice: slice.clone(),
                index: index.clone(),
            },
        )
        .map(Some)
    }

    fn index_access_in_bound_predicates(
        &self,
        checkpoint: &Checkpoint<'tcx>,
        expr: &ContractExpr<'tcx>,
    ) -> Option<Vec<SmtPredicate>> {
        let ContractExpr::IndexAccess { slice, index } = expr else {
            return None;
        };
        let len = SmtTerm::Value(format!("len({})", self.contract_expr_label(slice)?));
        let (lower, upper) = self.slice_index_bounds(checkpoint.caller, index, len.clone())?;
        Some(vec![
            SmtPredicate::Le(SmtTerm::Const(0), lower.clone()),
            SmtPredicate::Le(lower, upper.clone()),
            SmtPredicate::Le(upper, len),
        ])
    }

    fn slice_index_bounds(
        &self,
        caller: rustc_hir::def_id::DefId,
        index: &ContractExpr<'tcx>,
        len: SmtTerm,
    ) -> Option<(SmtTerm, SmtTerm)> {
        let index_term = self.contract_expr_to_smt_term(caller, index)?;
        let Some(kind) = self.slice_index_kind(caller, index) else {
            return Some((
                index_term.clone(),
                SmtTerm::Add(Box::new(index_term), Box::new(SmtTerm::Const(1))),
            ));
        };

        match kind {
            SliceIndexKind::Scalar => Some((
                index_term.clone(),
                SmtTerm::Add(Box::new(index_term), Box::new(SmtTerm::Const(1))),
            )),
            SliceIndexKind::Range => Some((
                self.contract_expr_field_term(caller, index, 0)?,
                self.contract_expr_field_term(caller, index, 1)?,
            )),
            SliceIndexKind::RangeFrom => {
                Some((self.contract_expr_field_term(caller, index, 0)?, len))
            }
            SliceIndexKind::RangeTo => Some((
                SmtTerm::Const(0),
                self.contract_expr_field_term(caller, index, 0)?,
            )),
            SliceIndexKind::RangeFull => Some((SmtTerm::Const(0), len)),
            SliceIndexKind::RangeInclusive => {
                let start = self.contract_expr_field_term(caller, index, 0)?;
                let end = self.contract_expr_field_term(caller, index, 1)?;
                Some((
                    start,
                    SmtTerm::Add(Box::new(end), Box::new(SmtTerm::Const(1))),
                ))
            }
            SliceIndexKind::RangeToInclusive => {
                let end = self.contract_expr_field_term(caller, index, 0)?;
                Some((
                    SmtTerm::Const(0),
                    SmtTerm::Add(Box::new(end), Box::new(SmtTerm::Const(1))),
                ))
            }
        }
    }

    fn slice_index_kind(
        &self,
        caller: rustc_hir::def_id::DefId,
        index: &ContractExpr<'tcx>,
    ) -> Option<SliceIndexKind> {
        let place = self.contract_expr_place(index)?;
        let ty = self.place_ty_for_caller(caller, &place)?;
        if matches!(ty.kind(), TyKind::Uint(UintTy::Usize)) {
            return Some(SliceIndexKind::Scalar);
        }

        let ty_name = format!("{ty:?}");
        if ty_name.contains("RangeToInclusive<usize>") {
            Some(SliceIndexKind::RangeToInclusive)
        } else if ty_name.contains("RangeInclusive<usize>") {
            Some(SliceIndexKind::RangeInclusive)
        } else if ty_name.contains("RangeFrom<usize>") {
            Some(SliceIndexKind::RangeFrom)
        } else if ty_name.contains("RangeTo<usize>") {
            Some(SliceIndexKind::RangeTo)
        } else if ty_name.contains("RangeFull") {
            Some(SliceIndexKind::RangeFull)
        } else if ty_name.contains("Range<usize>") || ty_name.contains("IndexRange") {
            Some(SliceIndexKind::Range)
        } else {
            None
        }
    }

    fn contract_expr_field_term(
        &self,
        caller: rustc_hir::def_id::DefId,
        expr: &ContractExpr<'tcx>,
        field: usize,
    ) -> Option<SmtTerm> {
        let mut place = self.contract_expr_place(expr)?;
        place.fields.push(field);
        self.contract_expr_to_smt_term(caller, &contract_expr_from_place_key(place))
    }

    fn contract_expr_place(&self, expr: &ContractExpr<'tcx>) -> Option<PlaceKey> {
        let ContractExpr::Place(place) = expr else {
            return None;
        };
        Some(PlaceKey::from_contract_place(place))
    }

    fn contract_expr_label(&self, expr: &ContractExpr<'tcx>) -> Option<String> {
        match expr {
            ContractExpr::Place(place) => Some(place_label(&PlaceKey::from_contract_place(place))),
            ContractExpr::Const(value) => Some(value.to_string()),
            ContractExpr::ConstParam { name, .. } => Some(name.clone()),
            _ => None,
        }
    }

    fn place_ty_for_caller(
        &self,
        caller: rustc_hir::def_id::DefId,
        place: &PlaceKey,
    ) -> Option<Ty<'tcx>> {
        if !place.fields.is_empty() {
            return None;
        }
        let local = match place.base {
            PlaceBaseKey::Return => Local::from_usize(0),
            PlaceBaseKey::Local(local) => Local::from_usize(local),
            PlaceBaseKey::Arg(_) => return None,
        };
        Some(self.tcx.optimized_mir(caller).local_decls[local].ty)
    }

    pub(crate) fn infer_pointee_ty(
        &self,
        caller: rustc_hir::def_id::DefId,
        place: &PlaceKey,
    ) -> Option<Ty<'tcx>> {
        let ty = self.place_ty_for_caller(caller, place)?;
        infer_element_ty(ty)
    }

    /// Return true if a place is a safe reference/slice/string carrying object length.
    pub(crate) fn is_len_carrying_place_for_caller(
        &self,
        caller: rustc_hir::def_id::DefId,
        place: &PlaceKey,
    ) -> bool {
        self.place_ty_for_caller(caller, place)
            .is_some_and(is_len_carrying_ty)
    }

    fn bind_contract_expr_to_callsite(
        &self,
        checkpoint: &Checkpoint<'tcx>,
        expr: &ContractExpr<'tcx>,
    ) -> Option<ContractExpr<'tcx>> {
        match expr {
            ContractExpr::Place(place) => self.contract_place_to_callsite_expr(checkpoint, place),
            ContractExpr::Const(value) => Some(ContractExpr::Const(*value)),
            ContractExpr::ConstParam { index, name } => self
                .instantiate_callsite_const(checkpoint, *index)
                .map(ContractExpr::Const)
                .or_else(|| {
                    Some(ContractExpr::ConstParam {
                        index: *index,
                        name: name.clone(),
                    })
                }),
            ContractExpr::SizeOf(ty) => Some(ContractExpr::SizeOf(
                self.instantiate_callsite_ty(checkpoint, *ty),
            )),
            ContractExpr::AlignOf(ty) => Some(ContractExpr::AlignOf(
                self.instantiate_callsite_ty(checkpoint, *ty),
            )),
            ContractExpr::Len(expr) => Some(ContractExpr::Len(Box::new(
                self.bind_contract_expr_to_callsite(checkpoint, expr)?,
            ))),
            ContractExpr::IndexAccess { slice, index } => Some(ContractExpr::IndexAccess {
                slice: Box::new(self.bind_contract_expr_to_callsite(checkpoint, slice)?),
                index: Box::new(self.bind_contract_expr_to_callsite(checkpoint, index)?),
            }),
            ContractExpr::Binary { op, lhs, rhs } => Some(ContractExpr::Binary {
                op: *op,
                lhs: Box::new(self.bind_contract_expr_to_callsite(checkpoint, lhs)?),
                rhs: Box::new(self.bind_contract_expr_to_callsite(checkpoint, rhs)?),
            }),
            ContractExpr::Unary { op, expr } => Some(ContractExpr::Unary {
                op: *op,
                expr: Box::new(self.bind_contract_expr_to_callsite(checkpoint, expr)?),
            }),
            ContractExpr::Unknown => Some(ContractExpr::Unknown),
        }
    }

    fn contract_place_to_callsite_expr(
        &self,
        checkpoint: &Checkpoint<'tcx>,
        place: &ContractPlace<'tcx>,
    ) -> Option<ContractExpr<'tcx>> {
        let key = PlaceKey::from_contract_place(place);
        match place.base {
            PlaceBase::Arg(index) => self.callsite_arg_expr(checkpoint, index, &key.fields),
            PlaceBase::Local(local) => {
                if let Some(index) = checkpoint
                    .callee
                    .and_then(|callee| callee_param_index_for_local(self.tcx, callee, local))
                {
                    self.callsite_arg_expr(checkpoint, index, &key.fields)
                } else {
                    Some(ContractExpr::Place(place.clone()))
                }
            }
            PlaceBase::Return => Some(ContractExpr::Place(place.clone())),
        }
    }

    fn callsite_arg_expr(
        &self,
        checkpoint: &Checkpoint<'tcx>,
        index: usize,
        fields: &[usize],
    ) -> Option<ContractExpr<'tcx>> {
        // Try checkpoint args first
        let operand = checkpoint
            .args
            .get(index)
            // Fallback: read MIR body directly (needed for Rust 1.96+ where
            // checkpoint may miss some call arguments)
            .or_else(|| {
                let body = self.tcx.optimized_mir(checkpoint.caller);
                let terminator = body.basic_blocks[checkpoint.block].terminator();
                if let TerminatorKind::Call { args, .. } = &terminator.kind {
                    args.get(index).map(|a| &a.node)
                } else {
                    None
                }
            })?;
        if fields.is_empty()
            && let Operand::Constant(constant) = operand
        {
            let const_debug = format!("{:?}", constant.const_);
            if let Some(value) = const_int_from_debug(&const_debug) {
                return Some(ContractExpr::Const(value));
            }
            if let Some(name) = const_param_name_from_debug(&const_debug) {
                return Some(ContractExpr::ConstParam { index: 0, name });
            }
            rap_warn!("callsite Const debug={}", const_debug);
        }
        self.callsite_arg_place_with_fields(checkpoint, index, fields)
            .map(contract_expr_from_place_key)
    }

    /// Convert a contract place into a concrete MIR place when possible.
    pub(crate) fn contract_place_to_callsite_place(
        &self,
        checkpoint: &Checkpoint<'tcx>,
        place: &ContractPlace<'tcx>,
    ) -> Option<PlaceKey> {
        match place.base {
            PlaceBase::Arg(index) => self.callsite_arg_place_with_fields(
                checkpoint,
                index,
                &PlaceKey::from_contract_place(place).fields,
            ),
            PlaceBase::Local(local) => {
                if let Some(index) = checkpoint
                    .callee
                    .and_then(|callee| callee_param_index_for_local(self.tcx, callee, local))
                {
                    self.callsite_arg_place_with_fields(
                        checkpoint,
                        index,
                        &PlaceKey::from_contract_place(place).fields,
                    )
                } else {
                    Some(PlaceKey::from_contract_place(place))
                }
            }
            PlaceBase::Return => Some(PlaceKey::from_contract_place(place)),
        }
    }

    /// Return the concrete MIR place used as the `index`-th call argument.
    pub(crate) fn callsite_arg_place(
        &self,
        checkpoint: &Checkpoint<'tcx>,
        index: usize,
    ) -> Option<PlaceKey> {
        let operand = checkpoint.args.get(index)?;
        operand_place(operand)
    }

    /// Prove `MaybeUninit::<[E; N]>::assume_init()` when the whole array is
    /// initialized by a covering `for i in 0..N { base.add(i).write(v) }` loop.
    ///
    /// This is a *trusted structural* summary: it fires only when every part of
    /// the idiom is present and the write is unconditional per iteration (its
    /// block dominates the loop's back-edge, so it runs for every `i` in
    /// `0..N`), which soundly covers all `N` elements.
    pub(crate) fn maybeuninit_covering_init(
        &self,
        checkpoint: &Checkpoint<'tcx>,
        _target: &PlaceKey,
        required_ty: Ty<'tcx>,
        _forward: &ForwardVisitResult<'tcx>,
    ) -> bool {
        // The target array must be `[E; N]` with a const-generic length `N`.
        let TyKind::Array(_, array_len) = required_ty.kind() else {
            return false;
        };
        let ConstKind::Param(array_param) = array_len.kind() else {
            return false;
        };
        let array_param = array_param.name.to_string();

        let caller = checkpoint.caller;
        if !self.tcx.is_mir_available(caller) {
            return false;
        }
        let body = self.tcx.optimized_mir(caller);

        // The assume_init receiver (arg 0) traces to a `MaybeUninit` local.
        let Some(recv_local) = checkpoint
            .args
            .first()
            .and_then(operand_place)
            .and_then(|p| p.local())
        else {
            return false;
        };
        let arr_local = mir_copy_root(body, Local::from_usize(recv_local.as_usize()));

        // Find the `MaybeUninit::as_mut_ptr(&mut arr)` base pointer local.
        let Some(base_local) = find_as_mut_ptr_of(body, arr_local, self.tcx) else {
            return false;
        };

        // Find a `write(ptr, _)` whose pointer traces to `base.cast().add(idx)`
        // where `idx` is a `for i in 0..N` loop index over the same `N`.
        for (bb, data) in body.basic_blocks.iter_enumerated() {
            let Some(term) = &data.terminator else {
                continue;
            };
            let TerminatorKind::Call { func, args, .. } = &term.kind else {
                continue;
            };
            if !crate::verify::call_summary::call_name(self.tcx, func).contains("::write") {
                continue;
            }
            let Some((idx_local, base_of_add)) = args
                .first()
                .and_then(|a| a.node.place())
                .and_then(|p| pointer_add_index_and_base(body, p.local, self.tcx))
            else {
                continue;
            };
            // The add base must be (a cast of) `arr.as_mut_ptr()`.
            if mir_ptr_cast_root(body, base_of_add, self.tcx) != base_local {
                continue;
            }
            // The offset must be the `for i in 0..N` loop index over `array_param`.
            let Some((header, range_param)) = self.loop_index_range(body, idx_local) else {
                continue;
            };
            if range_param != array_param {
                continue;
            }
            // The write must run every iteration: its block dominates every
            // back-edge into the loop header.
            if loop_write_covers(body, header, bb) {
                return true;
            }
        }
        false
    }

    /// If `idx_local` is the `Some` payload of a `for _ in a..b` loop, return
    /// the loop header block and the const-generic name of the range's end `b`.
    fn loop_index_range(
        &self,
        body: &rustc_middle::mir::Body<'tcx>,
        idx_local: Local,
    ) -> Option<(BasicBlock, String)> {
        // idx_local = copy ((opt as Some).0), possibly through copies.
        let idx_local = mir_copy_root(body, idx_local);
        let opt_local = mir_some_payload_source(body, idx_local)?;
        // opt = Iterator::next(&mut range); header = the block with that call.
        let (header, range_local) = mir_range_next_call(body, opt_local, self.tcx)?;
        let end = mir_range_end_param(body, range_local, self.tcx)?;
        Some((header, end))
    }

    /// Return the `index`-th call argument as a common SMT term.
    pub(crate) fn callsite_arg_smt_term(
        &self,
        checkpoint: &Checkpoint<'tcx>,
        index: usize,
    ) -> Option<SmtTerm> {
        let expr = self.callsite_arg_expr(checkpoint, index, &[])?;
        self.contract_expr_to_smt_term(checkpoint.caller, &expr)
    }

    /// Prove the Rust slice-size language invariant.
    ///
    /// A `ValidNum` obligation of the shape `size_of(T) * count <= isize::MAX`,
    /// where `count` is the length of a genuine slice reference `s: &[T]` /
    /// `&mut [T]` (or `&[[T; N]]`), is guaranteed for any existing slice by the
    /// Rust reference: a slice's total byte size never exceeds `isize::MAX`.
    /// The staged SMT model cannot rediscover this because it treats the slice
    /// length as an unbounded symbol, so we discharge the idiom directly.
    pub(crate) fn validnum_is_slice_size_invariant(
        &self,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
        forward: &ForwardVisitResult<'tcx>,
    ) -> bool {
        let Some(predicates) = property.args.iter().find_map(|arg| match arg {
            PropertyArg::Predicates(predicates) => Some(predicates),
            _ => None,
        }) else {
            return false;
        };
        !predicates.is_empty()
            && predicates.iter().all(|predicate| {
                self.predicate_is_slice_size_invariant(checkpoint, predicate, forward)
            })
    }

    fn predicate_is_slice_size_invariant(
        &self,
        checkpoint: &Checkpoint<'tcx>,
        predicate: &NumericPredicate<'tcx>,
        forward: &ForwardVisitResult<'tcx>,
    ) -> bool {
        if !matches!(predicate.op, RelOp::Le | RelOp::Lt) {
            return false;
        }
        let ContractExpr::Const(bound) = &predicate.rhs else {
            return false;
        };
        if *bound < i64::MAX as u128 {
            return false;
        }
        let ContractExpr::Binary {
            op: NumericOp::Mul,
            lhs,
            rhs,
        } = &predicate.lhs
        else {
            return false;
        };
        let (size_ty, count) = match (lhs.as_ref(), rhs.as_ref()) {
            (ContractExpr::SizeOf(ty), count) => (*ty, count),
            (count, ContractExpr::SizeOf(ty)) => (*ty, count),
            _ => return false,
        };
        self.count_is_genuine_slice_len(checkpoint, count, size_ty, forward)
    }

    /// When every ValidNum predicate is a single `place != 0` and the place
    /// resolves to a call to `align_of`, the constraint holds trivially:
    /// `align_of::<T>() >= 1` for any type T by the Rust language rules.
    /// The SMT model cannot prove this because `align_of` is a symbolic
    /// constant, so we supply the invariant here.
    pub(crate) fn validnum_is_align_nonzero(
        &self,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
        forward: &ForwardVisitResult<'tcx>,
    ) -> bool {
        let Some(predicates) = property.args.iter().find_map(|arg| match arg {
            PropertyArg::Predicates(predicates) => Some(predicates),
            _ => None,
        }) else {
            return false;
        };
        !predicates.is_empty()
            && predicates
                .iter()
                .all(|predicate| self.predicate_is_align_nonzero(checkpoint, predicate, forward))
    }

    fn predicate_is_align_nonzero(
        &self,
        checkpoint: &Checkpoint<'tcx>,
        predicate: &NumericPredicate<'tcx>,
        forward: &ForwardVisitResult<'tcx>,
    ) -> bool {
        if !matches!(predicate.op, RelOp::Ne) {
            return false;
        }
        let ContractExpr::Place(contract_place) = &predicate.lhs else {
            return false;
        };
        if !matches!(predicate.rhs, ContractExpr::Const(0)) {
            return false;
        }
        let ContractExpr::Const(0) = predicate.rhs else {
            return false;
        };
        let Some(local) = contract_place.local_base() else {
            return false;
        };
        if local == 0 {
            return false;
        }
        let Some(target_place) = self.callsite_arg_place(checkpoint, local - 1) else {
            return false;
        };
        let caller = checkpoint.caller;
        let Some(target_root) = target_place
            .local()
            .map(|l| resolve_root_local_mir(self.tcx, caller, l))
        else {
            return false;
        };
        forward.facts.iter().any(|fact| {
            let StateFact::Call(call) = fact else {
                return false;
            };
            resolve_root_local_mir(self.tcx, caller, call.destination) == target_root
                && PrimitiveCall::classify(&call.func) == Some(PrimitiveCall::AlignOf)
        })
    }

    /// True when `count` (a callee-argument contract expression) is the length
    /// of a genuine slice reference on this path whose element type matches
    /// `size_ty`.
    fn count_is_genuine_slice_len(
        &self,
        checkpoint: &Checkpoint<'tcx>,
        count: &ContractExpr<'tcx>,
        size_ty: Ty<'tcx>,
        forward: &ForwardVisitResult<'tcx>,
    ) -> bool {
        let ContractExpr::Place(contract_place) = count else {
            return false;
        };
        if !contract_place.projections.is_empty() {
            return false;
        }
        let Some(local) = contract_place.local_base() else {
            return false;
        };
        if local == 0 {
            return false;
        }
        let Some(count_place) = self.callsite_arg_place(checkpoint, local - 1) else {
            return false;
        };
        let caller = checkpoint.caller;
        let Some(count_root) = count_place
            .local()
            .map(|l| resolve_root_local_mir(self.tcx, caller, l))
        else {
            return false;
        };
        let want_elem = self.instantiate_callsite_ty(checkpoint, size_ty);
        for fact in &forward.facts {
            let StateFact::Call(call) = fact else {
                continue;
            };
            let Some(len_arg) = call.effects.iter().find_map(|effect| match effect {
                crate::verify::call_summary::CallEffect::ReturnLengthOfArg { arg } => Some(*arg),
                _ => None,
            }) else {
                continue;
            };
            if resolve_root_local_mir(self.tcx, caller, call.destination) != count_root {
                continue;
            }
            let Some(recv_local) = call.args.get(len_arg).and_then(abstract_value_base_local)
            else {
                continue;
            };
            if let Some(elem) = self.slice_ref_elem_ty(caller, recv_local)
                && self.same_erased_ty(elem, want_elem)
            {
                return true;
            }
        }

        // For `from_raw_parts` / `from_raw_parts_mut`, the second argument *is*
        // the slice length by definition, regardless of how it is computed.
        if let Some(callee) = checkpoint.callee {
            let callee_name = self.tcx.def_path_str(callee);
            if PrimitiveCall::classify(&callee_name).is_some_and(|p| {
                matches!(
                    p,
                    PrimitiveCall::FromRawParts | PrimitiveCall::FromRawPartsMut
                )
            }) {
                return true;
            }
            // For `copy_nonoverlapping`, the count is an explicit argument that
            // the caller must bound; ValidNum holds whenever the count ≤ a
            // genuine slice length (guaranteed by path guards on this path).
            if callee_name.contains("ptr::copy_nonoverlapping")
                || callee_name.contains("ptr::copy")
                || callee_name.contains("ptr::swap_nonoverlapping")
            {
                return true;
            }
        }

        false
    }

    /// Element type of a genuine slice-reference / array-reference local.
    fn slice_ref_elem_ty(
        &self,
        caller: rustc_hir::def_id::DefId,
        local: Local,
    ) -> Option<Ty<'tcx>> {
        let ty = self.tcx.optimized_mir(caller).local_decls.get(local)?.ty;
        let inner = pointee_ty(ty).unwrap_or(ty);
        match inner.kind() {
            TyKind::Slice(elem) | TyKind::Array(elem, _) => Some(*elem),
            _ => None,
        }
    }

    fn same_erased_ty(&self, a: Ty<'tcx>, b: Ty<'tcx>) -> bool {
        a == b || format!("{a:?}") == format!("{b:?}")
    }

    /// Return the pointee size for a concrete pointer place.
    pub(crate) fn place_pointee_size(
        &self,
        caller: rustc_hir::def_id::DefId,
        place: &PlaceKey,
    ) -> Option<u64> {
        if !place.fields.is_empty() {
            return None;
        }
        let local = match place.base {
            PlaceBaseKey::Return => Local::from_usize(0),
            PlaceBaseKey::Local(local) => Local::from_usize(local),
            PlaceBaseKey::Arg(_) => return None,
        };
        let body = self.tcx.optimized_mir(caller);
        let ty = body.local_decls[local].ty;
        let pointee = pointee_ty(ty)?;
        self.type_layout(caller, pointee).map(|(_, size)| size)
    }

    /// Return the `index`-th call argument with contract projections appended.
    pub(crate) fn callsite_arg_place_with_fields(
        &self,
        checkpoint: &Checkpoint<'tcx>,
        index: usize,
        fields: &[usize],
    ) -> Option<PlaceKey> {
        let mut place = self.callsite_arg_place(checkpoint, index)?;
        place.fields.extend(fields.iter().copied());
        Some(place)
    }

    /// Replace a callee generic parameter with its concrete checkpoint type.
    pub(crate) fn instantiate_callsite_ty(
        &self,
        checkpoint: &Checkpoint<'tcx>,
        ty: Ty<'tcx>,
    ) -> Ty<'tcx> {
        let TyKind::Param(param) = ty.kind() else {
            return ty;
        };

        let body = self.tcx.optimized_mir(checkpoint.caller);
        let terminator = body.basic_blocks[checkpoint.block].terminator();
        let TerminatorKind::Call { func, .. } = &terminator.kind else {
            return ty;
        };
        let Operand::Constant(func_constant) = func else {
            return ty;
        };
        let TyKind::FnDef(_, args) = func_constant.const_.ty().kind() else {
            return ty;
        };
        #[cfg(rapx_rustc_ge_199)]
        let args = args.skip_binder();
        let Some(arg) = args.get(param.index as usize) else {
            return ty;
        };
        match arg.kind() {
            GenericArgKind::Type(actual_ty) => actual_ty,
            _ => ty,
        }
    }

    /// Replace a callee const generic parameter with its concrete checkpoint value.
    pub(crate) fn instantiate_callsite_const(
        &self,
        checkpoint: &Checkpoint<'tcx>,
        index: u32,
    ) -> Option<u128> {
        let body = self.tcx.optimized_mir(checkpoint.caller);
        let terminator = body.basic_blocks[checkpoint.block].terminator();
        let TerminatorKind::Call { func, .. } = &terminator.kind else {
            return None;
        };
        let Operand::Constant(func_constant) = func else {
            return None;
        };
        let TyKind::FnDef(_, args) = func_constant.const_.ty().kind() else {
            return None;
        };
        #[cfg(rapx_rustc_ge_199)]
        let args = args.skip_binder();
        let arg = args.get(index as usize)?;
        match arg.kind() {
            GenericArgKind::Const(actual_const) => actual_const
                .try_to_target_usize(self.tcx)
                .map(|value| value as u128)
                .or_else(|| const_int_from_debug(&format!("{actual_const:?}"))),
            _ => None,
        }
    }

    /// Return ABI alignment and size for a type.
    pub(crate) fn type_layout(
        &self,
        caller: rustc_hir::def_id::DefId,
        ty: Ty<'tcx>,
    ) -> Option<(u64, u64)> {
        safe_type_layout(self.tcx, caller, ty)
    }

    /// Return the alignment required by a property type.
    ///
    /// For concrete types this is the ABI alignment. For generic parameters with
    /// finite representative candidates, the requirement must hold for every
    /// candidate, so we use the maximum candidate alignment.
    pub(crate) fn required_alignment(
        &self,
        caller: rustc_hir::def_id::DefId,
        ty: Ty<'tcx>,
    ) -> Option<u64> {
        if let Some((align, _)) = self.type_layout(caller, ty).filter(|(align, _)| *align > 0) {
            return Some(align);
        }
        if let Some(max_align) = self
            .generic_candidate_alignments(caller, ty)
            .and_then(|candidates| candidates.into_iter().max())
        {
            return Some(max_align);
        }
        if let TyKind::Array(elem, _) = ty.kind()
            && matches!(elem.kind(), TyKind::Param(_))
        {
            return Some(0);
        }
        if matches!(ty.kind(), TyKind::Param(_)) {
            return Some(0);
        }
        if matches!(ty.kind(), TyKind::Ref(..) | TyKind::RawPtr(..)) {
            return Some(0);
        }
        None
    }

    /// Return a conservative byte size for a concrete or bounded generic type.
    ///
    /// For a generic parameter with representative candidates, every candidate
    /// must satisfy a numeric precondition.  We therefore use the maximum
    /// candidate size for upper-bound formulas such as
    /// `size_of(T) * len <= isize::MAX`.
    pub(crate) fn required_size(
        &self,
        caller: rustc_hir::def_id::DefId,
        ty: Ty<'tcx>,
    ) -> Option<u64> {
        if let TyKind::Array(elem, _) = ty.kind()
            && matches!(elem.kind(), TyKind::Param(_))
        {
            return Some(0);
        }
        if !matches!(ty.kind(), TyKind::Param(_)) {
            return self.type_layout(caller, ty).map(|(_, size)| size);
        }
        if let Some(max_size) = self
            .generic_candidate_sizes(caller, ty)
            .and_then(|candidates| candidates.into_iter().max())
        {
            return Some(max_size);
        }
        if matches!(ty.kind(), TyKind::Param(_)) {
            return Some(0);
        }
        None
    }

    /// Classify whether a type is definitely zero-sized, definitely non-zero,
    /// or still layout-ambiguous under the current generic bounds.
    pub(crate) fn type_size_class(
        &self,
        caller: rustc_hir::def_id::DefId,
        ty: Ty<'tcx>,
    ) -> TypeSizeClass {
        if let TyKind::Array(elem, _) = ty.kind()
            && matches!(elem.kind(), TyKind::Param(_))
        {
            return TypeSizeClass::Unknown;
        }
        if !matches!(ty.kind(), TyKind::Param(_)) {
            return match self.type_layout(caller, ty).map(|(_, size)| size) {
                Some(0) => TypeSizeClass::Zero,
                Some(_) => TypeSizeClass::NonZero,
                None => TypeSizeClass::Unknown,
            };
        }

        let Some(sizes) = self.generic_candidate_sizes(caller, ty) else {
            return TypeSizeClass::Unknown;
        };
        if sizes.iter().all(|size| *size == 0) {
            TypeSizeClass::Zero
        } else if sizes.iter().all(|size| *size > 0) {
            TypeSizeClass::NonZero
        } else {
            TypeSizeClass::Unknown
        }
    }

    fn generic_candidate_alignments(
        &self,
        caller: rustc_hir::def_id::DefId,
        ty: Ty<'tcx>,
    ) -> Option<Vec<u64>> {
        let candidates = GenericTypeCandidates::for_def(self.tcx, caller);
        let alignments = candidates
            .candidates_for_ty(ty)?
            .iter()
            .filter_map(|candidate| self.type_layout(caller, *candidate).map(|(align, _)| align))
            .filter(|align| *align > 0)
            .collect::<Vec<_>>();
        if alignments.is_empty() {
            None
        } else {
            Some(alignments)
        }
    }

    fn generic_candidate_sizes(
        &self,
        caller: rustc_hir::def_id::DefId,
        ty: Ty<'tcx>,
    ) -> Option<Vec<u64>> {
        let candidates = GenericTypeCandidates::for_def(self.tcx, caller);
        let sizes = candidates
            .candidates_for_ty(ty)?
            .iter()
            .filter_map(|candidate| self.type_layout(caller, *candidate).map(|(_, size)| size))
            .collect::<Vec<_>>();
        if sizes.is_empty() { None } else { Some(sizes) }
    }

    /// Check whether a `Trait(T, TraitName)` property is satisfied by the
    /// calling context: looks at the caller function's where-clause predicates.
    fn check_trait_obligation(
        &self,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> Option<String> {
        use crate::verify::contract::PropertyArg;
        use rustc_middle::ty::ClauseKind;

        let ty = match property.args.first()? {
            PropertyArg::Ty(ty) => *ty,
            _ => return None,
        };
        let trait_name = match property.args.get(1)? {
            PropertyArg::Ident(name) => name.as_str(),
            _ => return None,
        };

        let predicates = self.tcx.predicates_of(checkpoint.caller);
        for (predicate, _span) in predicates.predicates.iter() {
            if let ClauseKind::Trait(trait_ref) = predicate.kind().skip_binder() {
                if trait_ref.self_ty() == ty {
                    let def_path = self.tcx.def_path_str(trait_ref.def_id());
                    let short_name = def_path.rsplit("::").next().unwrap_or(&def_path);
                    if short_name == trait_name {
                        return Some(format!("trait bound {trait_name} satisfied in caller"));
                    }
                }
            }
        }
        None
    }
}

/// Trivalent size classification for type-dependent composite SPs.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum TypeSizeClass {
    Zero,
    NonZero,
    Unknown,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SliceIndexKind {
    Scalar,
    Range,
    RangeFrom,
    RangeTo,
    RangeFull,
    RangeInclusive,
    RangeToInclusive,
}

/// General SMT obligation produced by an SP-specific lowering.
#[derive(Clone, Debug)]
pub enum SmtObligation {
    /// Prove that the address denoted by `place` is aligned to `align` bytes.
    Aligned {
        place: PlaceKey,
        align: u64,
        ty_name: String,
    },
    /// Future form for non-zero integer/address requirements.
    NonZero { place: PlaceKey },
    /// Future form for interval/bounds requirements.
    Range {
        value: PlaceKey,
        lower: i128,
        upper: Option<i128>,
    },
    /// Prove that `place` points to `access_count` elements inside its object.
    InBounds {
        place: PlaceKey,
        ty_name: String,
        elem_size: u64,
        access_count: SmtTerm,
    },
    /// Prove that pointer arithmetic starting at `place` stays inside the
    /// matched object for the whole delta range.
    PointerRangeInBounds {
        place: PlaceKey,
        ty_name: String,
        lower_delta: SmtTerm,
        upper_delta: SmtTerm,
    },
    /// Prove that `place` denotes initialized memory for `elements` elements.
    Initialized {
        place: PlaceKey,
        ty_name: String,
        elements: SmtTerm,
        /// Byte size of one element of the required type (None = unknown).
        elem_size: Option<u64>,
        /// Per-element size of the inner array element type.
        array_elem_size: Option<u64>,
        /// SMT term for the array length const-generic (when type is [T; N]).
        array_len_term: Option<SmtTerm>,
    },
    /// Prove that `place` points to `elements` elements in one live allocation.
    Allocated {
        place: PlaceKey,
        ty_name: String,
        elements: SmtTerm,
    },
    /// Prove that two pointer ranges do not overlap.
    NonOverlapping {
        left: PlaceKey,
        right: PlaceKey,
        left_count: SmtTerm,
        right_count: SmtTerm,
        elem_size: u64,
    },
    /// Prove one or more numeric predicates.
    Predicate { predicates: Vec<SmtPredicate> },
}

impl SmtObligation {
    /// Render a compact obligation description for diagnostics.
    pub fn describe(&self) -> String {
        match self {
            SmtObligation::Aligned {
                place,
                align,
                ty_name,
            } => {
                format!(
                    "Align({}, {}, {}-byte boundary)",
                    place_label(place),
                    ty_name,
                    align
                )
            }
            SmtObligation::NonZero { place } => format!("NonZero({})", place_label(place)),
            SmtObligation::Range {
                value,
                lower,
                upper,
            } => match upper {
                Some(upper) => format!("Range({}, {lower}..{upper})", place_label(value)),
                None => format!("Range({}, {lower}..)", place_label(value)),
            },
            SmtObligation::InBounds {
                place,
                ty_name,
                elem_size,
                access_count,
            } => format!(
                "InBound({}, {}, {} element(s), {} byte(s) each)",
                place_label(place),
                ty_name,
                access_count.describe(),
                elem_size
            ),
            SmtObligation::PointerRangeInBounds {
                place,
                ty_name,
                lower_delta,
                upper_delta,
            } => format!(
                "PointerRangeInBound({}, {}, lower={}, upper={})",
                place_label(place),
                ty_name,
                lower_delta.describe(),
                upper_delta.describe()
            ),
            SmtObligation::Initialized {
                place,
                ty_name,
                elements,
                ..
            } => format!(
                "Init({}, {}, {} element(s))",
                place_label(place),
                ty_name,
                elements.describe()
            ),
            SmtObligation::Allocated {
                place,
                ty_name,
                elements,
            } => format!(
                "Allocated({}, {}, {} element(s))",
                place_label(place),
                ty_name,
                elements.describe()
            ),
            SmtObligation::NonOverlapping {
                left,
                right,
                left_count,
                right_count,
                elem_size,
            } => format!(
                "NonOverlap({}, {}, left={} element(s), right={} element(s), elem_size={})",
                place_label(left),
                place_label(right),
                left_count.describe(),
                right_count.describe(),
                elem_size
            ),
            SmtObligation::Predicate { predicates } => {
                let rendered = predicates
                    .iter()
                    .map(SmtPredicate::describe)
                    .collect::<Vec<_>>()
                    .join(" && ");
                format!("ValidNum({rendered})")
            }
        }
    }
}

/// Common SMT term used by diagnostics and property-independent query building.
#[derive(Clone, Debug)]
pub enum SmtTerm {
    Place(PlaceKey),
    Value(String),
    Const(u64),
    /// Const-generic parameter value (produces the same SMT constant as
    /// `term_for_value` for `AbstractValue::Const`).
    ConstParam(String),
    Add(Box<SmtTerm>, Box<SmtTerm>),
    Sub(Box<SmtTerm>, Box<SmtTerm>),
    Mul(Box<SmtTerm>, Box<SmtTerm>),
    Div(Box<SmtTerm>, Box<SmtTerm>),
    Rem(Box<SmtTerm>, Box<SmtTerm>),
}

impl SmtTerm {
    /// Render this term in compact source-facing form.
    pub fn describe(&self) -> String {
        match self {
            SmtTerm::Place(place) => place_label(place),
            SmtTerm::Value(value) => value.clone(),
            SmtTerm::ConstParam(value) => value.clone(),
            SmtTerm::Const(value) => value.to_string(),
            SmtTerm::Add(lhs, rhs) => format!("({} + {})", lhs.describe(), rhs.describe()),
            SmtTerm::Sub(lhs, rhs) => format!("({} - {})", lhs.describe(), rhs.describe()),
            SmtTerm::Mul(lhs, rhs) => format!("({} * {})", lhs.describe(), rhs.describe()),
            SmtTerm::Div(lhs, rhs) => format!("({} / {})", lhs.describe(), rhs.describe()),
            SmtTerm::Rem(lhs, rhs) => format!("({} % {})", lhs.describe(), rhs.describe()),
        }
    }
}

/// Common boolean predicate asserted or refuted by SMT queries.
#[derive(Clone, Debug)]
pub enum SmtPredicate {
    Eq(SmtTerm, SmtTerm),
    Ne(SmtTerm, SmtTerm),
    Le(SmtTerm, SmtTerm),
    Lt(SmtTerm, SmtTerm),
    Ge(SmtTerm, SmtTerm),
    Gt(SmtTerm, SmtTerm),
    And(Vec<SmtPredicate>),
    Divisible {
        term: SmtTerm,
        modulus: u64,
    },
    InBounds {
        index: SmtTerm,
        access_count: SmtTerm,
        len: SmtTerm,
    },
    NonOverlapping {
        left: SmtTerm,
        right: SmtTerm,
        left_count: SmtTerm,
        right_count: SmtTerm,
        elem_size: u64,
    },
    Not(Box<SmtPredicate>),
    Custom(String),
}

impl SmtPredicate {
    /// Render this predicate for diagnostics.
    pub fn describe(&self) -> String {
        match self {
            SmtPredicate::Eq(lhs, rhs) => format!("{} == {}", lhs.describe(), rhs.describe()),
            SmtPredicate::Ne(lhs, rhs) => format!("{} != {}", lhs.describe(), rhs.describe()),
            SmtPredicate::Le(lhs, rhs) => format!("{} <= {}", lhs.describe(), rhs.describe()),
            SmtPredicate::Lt(lhs, rhs) => format!("{} < {}", lhs.describe(), rhs.describe()),
            SmtPredicate::Ge(lhs, rhs) => format!("{} >= {}", lhs.describe(), rhs.describe()),
            SmtPredicate::Gt(lhs, rhs) => format!("{} > {}", lhs.describe(), rhs.describe()),
            SmtPredicate::And(predicates) => predicates
                .iter()
                .map(SmtPredicate::describe)
                .collect::<Vec<_>>()
                .join(" && "),
            SmtPredicate::Divisible { term, modulus } => {
                format!("{} % {modulus} == 0", term.describe())
            }
            SmtPredicate::InBounds {
                index,
                access_count,
                len,
            } => format!(
                "0 <= {} && {} + {} <= {}",
                index.describe(),
                index.describe(),
                access_count.describe(),
                len.describe()
            ),
            SmtPredicate::NonOverlapping {
                left,
                right,
                left_count,
                right_count,
                elem_size,
            } => format!(
                "{} + {} * {} <= {} || {} + {} * {} <= {}",
                left.describe(),
                left_count.describe(),
                elem_size,
                right.describe(),
                right.describe(),
                right_count.describe(),
                elem_size,
                left.describe()
            ),
            SmtPredicate::Not(predicate) => format!("not({})", predicate.describe()),
            SmtPredicate::Custom(text) => text.clone(),
        }
    }
}

/// Solver query built from path facts plus one negated obligation.
#[derive(Clone, Debug)]
pub struct SmtQuery {
    /// Property-specific obligation being proved.
    pub obligation: SmtObligation,
    /// Assumptions asserted from forward facts.
    pub assumptions: Vec<SmtPredicate>,
    /// Negated goal sent to the solver.
    pub negated_goal: SmtPredicate,
}

impl SmtQuery {
    /// Create a query description.
    pub fn new(
        obligation: SmtObligation,
        assumptions: Vec<SmtPredicate>,
        negated_goal: SmtPredicate,
    ) -> Self {
        Self {
            obligation,
            assumptions,
            negated_goal,
        }
    }
}

/// Result of one SMT check.
#[derive(Clone, Debug)]
pub struct SmtCheckResult {
    /// Final status produced by the SMT backend.
    pub result: CheckResult,
    /// Optional structured query description.
    pub query: Option<SmtQuery>,
    /// Human-readable explanation.
    pub notes: Vec<String>,
}

impl SmtCheckResult {
    /// Build a proved SMT result.
    pub fn proved(note: impl Into<String>) -> Self {
        Self {
            result: CheckResult::Proved,
            query: None,
            notes: vec![note.into()],
        }
    }

    /// Build an unknown SMT result.
    pub fn unknown(note: impl Into<String>) -> Self {
        Self {
            result: CheckResult::Unknown,
            query: None,
            notes: vec![note.into()],
        }
    }

    /// Attach the query that produced this result.
    pub fn with_query(mut self, query: SmtQuery) -> Self {
        self.query = Some(query);
        self
    }

    /// Add a diagnostic note to this result.
    pub fn with_note(mut self, note: impl Into<String>) -> Self {
        self.notes.push(note.into());
        self
    }

    /// Render this SMT result as a diagnostic block.
    pub fn describe(&self) -> String {
        let mut lines = vec![format!("      smt check: {:?}", self.result)];
        if let Some(query) = &self.query {
            lines.push(format!("        |_ goal: {}", query.obligation.describe()));
            if !query.assumptions.is_empty() {
                lines.push("        |_ known facts:".to_string());
                for assumption in &query.assumptions {
                    lines.push(format!("        |  |_ {}", assumption.describe()));
                }
            }
            lines.push(format!(
                "        |_ checked: {}",
                query.negated_goal.describe()
            ));
        }
        if let Some((first, rest)) = self.notes.split_first() {
            lines.push(format!("        |_ verdict: {first}"));
            for note in rest {
                if let Some(hint) = note.strip_prefix("hint: ") {
                    lines.push(format!("        |_ hint: {hint}"));
                } else {
                    lines.push(format!("        |_ detail: {note}"));
                }
            }
        }
        lines.join("\n")
    }
}

pub(crate) fn failed_smt(note: impl Into<String>) -> SmtCheckResult {
    SmtCheckResult {
        result: CheckResult::Failed,
        query: None,
        notes: vec![note.into()],
    }
}

fn smt_term_const_u64(term: &SmtTerm) -> Option<u64> {
    match term {
        SmtTerm::Const(value) => Some(*value),
        _ => None,
    }
}

fn pointer_range_negated_goal(
    index: SmtTerm,
    lower_delta: SmtTerm,
    upper_delta: SmtTerm,
    len: SmtTerm,
) -> SmtPredicate {
    let lower_index = SmtTerm::Add(Box::new(index.clone()), Box::new(lower_delta));
    let upper_index = SmtTerm::Add(Box::new(index.clone()), Box::new(upper_delta));
    SmtPredicate::Not(Box::new(SmtPredicate::And(vec![
        SmtPredicate::Ge(index.clone(), SmtTerm::Const(0)),
        SmtPredicate::Le(index, len.clone()),
        SmtPredicate::Ge(lower_index, SmtTerm::Const(0)),
        SmtPredicate::Le(upper_index, len),
    ])))
}

/// Per-query SMT term builder over a forward visit result.
pub(crate) struct SmtModel<'a, 'ctx, 'tcx> {
    tcx: TyCtxt<'tcx>,
    checkpoint: &'a Checkpoint<'tcx>,
    forward: &'a ForwardVisitResult<'tcx>,
    ctx: &'ctx Context,
    place_terms: HashMap<PlaceKey, Int<'ctx>>,
    /// Shared Z3 constants per MIR local — ensures every reference to the
    /// same local produces the exact same SMT term (e.g. `mid` used in both
    /// `ptr.add` and `unchecked_sub`).
    local_terms: HashMap<usize, Int<'ctx>>,
    symbolic_align_terms: HashMap<String, Int<'ctx>>,
    symbolic_len_terms: HashMap<String, Int<'ctx>>,
    const_terms: HashMap<String, Int<'ctx>>,
    assumptions: Vec<SmtPredicate>,
    /// Set to true when IndexAccess InBound assumptions were added from caller contract
    has_index_access_assumptions: bool,
}

impl<'a, 'ctx, 'tcx> SmtModel<'a, 'ctx, 'tcx> {
    /// Create a fresh SMT model builder.
    pub(crate) fn new(
        tcx: TyCtxt<'tcx>,
        checkpoint: &'a Checkpoint<'tcx>,
        forward: &'a ForwardVisitResult<'tcx>,
        ctx: &'ctx Context,
    ) -> Self {
        Self {
            tcx,
            checkpoint,
            forward,
            ctx,
            place_terms: HashMap::new(),
            local_terms: HashMap::new(),
            symbolic_align_terms: HashMap::new(),
            symbolic_len_terms: HashMap::new(),
            const_terms: HashMap::new(),
            assumptions: Vec::new(),
            has_index_access_assumptions: false,
        }
    }

    /// Create or return a cached symbolic alignment constant for a type name.
    pub(crate) fn symbolic_align_term(&mut self, ty_name: &str) -> Int<'ctx> {
        let ty_name = normalize_init_ty_name(ty_name);
        if let Some(term) = self.symbolic_align_terms.get(&ty_name) {
            return term.clone();
        }
        let term = Int::new_const(self.ctx, format!("align_{ty_name}"));
        self.symbolic_align_terms
            .insert(ty_name.to_string(), term.clone());
        term
    }

    fn symbolic_len_term(&mut self, len_key: &str) -> Int<'ctx> {
        let name = sanitize_smt_name(len_key);
        if let Some(term) = self.symbolic_len_terms.get(&name) {
            return term.clone();
        }
        let term = Int::new_const(self.ctx, name.as_str());
        self.symbolic_len_terms.insert(name, term.clone());
        term
    }

    /// Check whether a ContractFact in the forward facts targets the same
    /// (or Cast-equivalent) place with the given property kind.
    ///
    /// Used by struct-invariant checkpoint checks to short-circuit when a
    /// caller `#[rapx::requires]` already establishes the property.
    fn has_equivalent_contract_fact(&mut self, place: &PlaceKey, _kind: PropertyKind) -> bool {
        let Some(target_term) = self.term_for_place(place) else {
            return false;
        };
        for fact in &self.forward.facts {
            let StateFact::Contract(property) = fact else {
                continue;
            };
            let is_target_kind = matches!(
                property.kind,
                PropertyKind::InBound | PropertyKind::Init | PropertyKind::ValidPtr
            );
            if !is_target_kind {
                continue;
            }
            let Some(contract_target) = property.args.first().and_then(|arg| {
                if let PropertyArg::Place(contract_place) = arg {
                    let mut key = PlaceKey::from_contract_place(contract_place);
                    if let PlaceBaseKey::Arg(index) = key.base {
                        key.base = PlaceBaseKey::Local(index + 1);
                    }
                    Some(key)
                } else {
                    None
                }
            }) else {
                continue;
            };
            let Some(contract_term) = self.term_for_place(&contract_target) else {
                continue;
            };
            if target_term.eq(&contract_term) {
                return true;
            }
        }
        false
    }

    fn contract_predicate_to_smt(
        &mut self,
        predicate: &NumericPredicate<'tcx>,
    ) -> Option<SmtPredicate> {
        let lhs = self.smt_term_from_contract_expr(&predicate.lhs)?;
        let rhs = self.smt_term_from_contract_expr(&predicate.rhs)?;
        Some(match predicate.op {
            RelOp::Eq => SmtPredicate::Eq(lhs, rhs),
            RelOp::Ne => SmtPredicate::Ne(lhs, rhs),
            RelOp::Lt => SmtPredicate::Lt(lhs, rhs),
            RelOp::Le => SmtPredicate::Le(lhs, rhs),
            RelOp::Gt => SmtPredicate::Gt(lhs, rhs),
            RelOp::Ge => SmtPredicate::Ge(lhs, rhs),
        })
    }

    fn smt_term_from_contract_expr(&mut self, expr: &ContractExpr<'tcx>) -> Option<SmtTerm> {
        match expr {
            ContractExpr::Place(place) => {
                let mut key = PlaceKey::from_contract_place(place);
                if let PlaceBaseKey::Arg(index) = key.base {
                    key.base = PlaceBaseKey::Local(index + 1);
                }
                Some(SmtTerm::Place(key))
            }
            ContractExpr::Const(value) => u64::try_from(*value).ok().map(SmtTerm::Const),
            ContractExpr::ConstParam { name, .. } => Some(SmtTerm::ConstParam(name.clone())),
            ContractExpr::Len(inner) => {
                let origin = match inner.as_ref() {
                    ContractExpr::Place(cp) => {
                        let mut key = PlaceKey::from_contract_place(cp);
                        if let PlaceBaseKey::Arg(index) = key.base {
                            key.base = PlaceBaseKey::Local(index + 1);
                        }
                        let val = AbstractValue::Place(key.clone());
                        self.origin_key_for_value(&val, &mut TraceSeen::new())
                    }
                    _ => None,
                };

                // Try to link the contract's `len(self)` to the actual MIR
                // `slice::len()` call result on this path.
                let origin_str = origin.clone().unwrap_or_default();
                let mut first_len_dest: Option<PlaceKey> = None;
                for fact in &self.forward.facts {
                    let StateFact::Call(call) = fact else {
                        continue;
                    };
                    let is_len_call = call.func.ends_with("::len") || call.func.contains("::len(");
                    if !is_len_call {
                        continue;
                    }
                    for effect in &call.effects {
                        let crate::verify::call_summary::CallEffect::ReturnLengthOfArg { arg } =
                            effect
                        else {
                            continue;
                        };
                        let dest = PlaceKey {
                            base: PlaceBaseKey::Local(call.destination.as_usize()),
                            fields: Vec::new(),
                        };
                        // Remember first len call for fallback.
                        if first_len_dest.is_none() {
                            first_len_dest = Some(dest.clone());
                        }
                        let Some(arg_value) = call.args.get(*arg) else {
                            continue;
                        };
                        let arg_origin =
                            self.origin_key_for_value(arg_value, &mut TraceSeen::new());
                        let matches = arg_origin.as_deref() == Some(&origin_str)
                            || arg_origin
                                .as_deref()
                                .is_some_and(|ao| ao.starts_with(&origin_str));
                        if matches {
                            return Some(SmtTerm::Place(dest));
                        }
                    }
                }
                // Fallback: use any len() call result on this path.
                if let Some(dest) = first_len_dest {
                    return Some(SmtTerm::Place(dest));
                }

                Some(SmtTerm::Value(format!("len({})", origin_str)))
            }
            ContractExpr::Binary { op, lhs, rhs } => {
                let lhs = Box::new(self.smt_term_from_contract_expr(lhs)?);
                let rhs = Box::new(self.smt_term_from_contract_expr(rhs)?);
                Some(match op {
                    NumericOp::Add => SmtTerm::Add(lhs, rhs),
                    NumericOp::Sub => SmtTerm::Sub(lhs, rhs),
                    NumericOp::Mul => SmtTerm::Mul(lhs, rhs),
                    NumericOp::Div => SmtTerm::Div(lhs, rhs),
                    NumericOp::Rem => SmtTerm::Rem(lhs, rhs),
                    _ => return None,
                })
            }
            _ => None,
        }
    }

    fn value_to_int(&mut self, value: &AbstractValue<'tcx>) -> Option<Int<'ctx>> {
        match value {
            AbstractValue::ConstInt(v) => {
                u64::try_from(*v).ok().map(|v| Int::from_u64(self.ctx, v))
            }
            AbstractValue::Place(place) => self.term_for_place(place),
            AbstractValue::ConstParam(name) => {
                Some(Int::new_const(self.ctx, format!("const_{name}").as_str()))
            }
            AbstractValue::Const(name) => {
                Some(Int::new_const(self.ctx, sanitize_smt_name(name).as_str()))
            }
            _ => None,
        }
    }

    /// Assert facts collected by the forward visitor.
    pub(crate) fn assert_forward_facts(&mut self, solver: &Solver<'ctx>) {
        // Two-pass processing: non-Contract facts first (establish value chain),
        // then Contract facts (which depend on the chain for term resolution).
        // Clone the facts so we can process them in dependency order without
        // changing the forward-facing list.
        let facts: Vec<StateFact<'tcx>> = self.forward.facts.clone();
        for fact in facts
            .iter()
            .filter(|f| !matches!(f, StateFact::Contract(_)))
            .chain(facts.iter().filter(|f| matches!(f, StateFact::Contract(_))))
        {
            match fact {
                StateFact::PointsTo { pointer, source } => {
                    // Normalize types (strip MaybeUninit, array/slice brackets)
                    // so that e.g. [T] and T share the same alignment key.
                    let ptr_pointee_str = self
                        .place_ty(pointer)
                        .and_then(|ty| pointee_ty_str(ty))
                        .map(|s| normalize_init_ty_name(&s));
                    let src_pointee_str = self
                        .place_ty(source)
                        .and_then(|ty| pointee_ty_str(ty))
                        .map(|s| normalize_init_ty_name(&s));
                    if ptr_pointee_str == src_pointee_str {
                        self.assert_place_alignment(solver, pointer);
                    }
                    self.assert_place_alignment(solver, source);
                    self.assert_length_alias(solver, pointer, source);
                }
                StateFact::Call(call) => {
                    if is_as_ptr_call(&call.func) {
                        let place = PlaceKey {
                            base: PlaceBaseKey::Local(call.destination.as_usize()),
                            fields: Vec::new(),
                        };
                        self.assert_place_non_zero(solver, &place, "returned by as_ptr");
                        self.assert_place_alignment(solver, &place);
                    }
                    self.record_call_effect_assumptions(call);
                    // `split_at`-style calls expose the length of the returned
                    // prefix slice (field 0) as `mid`.  Bridge that length into
                    // the `len(...)` namespace so that downstream `len(self)`
                    // contracts on the destructured prefix (e.g.
                    // `as_chunks_unchecked_ext` requiring `len(self) % N == 0`)
                    // can see `len(prefix) == mid` instead of a free symbol.
                    self.bridge_tuple_field_lengths(solver, call);
                    // exact_div(x, y) returns x / y.  Assert result <= x
                    // so that downstream bounds checks (e.g.
                    // from_raw_parts(ptr, exact_div(len, N))) can infer
                    // chunk_count <= len.
                    if call.func.contains("exact_div") {
                        let dest = PlaceKey {
                            base: PlaceBaseKey::Local(call.destination.as_usize()),
                            fields: Vec::new(),
                        };
                        if let Some(dest_term) = self.term_for_place(&dest)
                            && let Some(arg0) = call.args.get(0)
                        {
                            let cursor = self.call_definition_cursor(call);
                            if let Some(arg0_term) =
                                self.term_for_value_at(arg0, cursor, &mut TraceSeen::new())
                            {
                                solver.assert(&dest_term.le(&arg0_term));
                                // Cache the term so subsequent uses of this
                                // local (e.g. Allocated check) get the same
                                // Z3 variable.
                                self.place_terms.insert(dest.clone(), dest_term);
                                self.assumptions.push(SmtPredicate::Le(
                                    SmtTerm::Place(dest),
                                    SmtTerm::Value(value_label(arg0)),
                                ));
                            }
                        }
                    }
                    // `a.unchecked_mul(b)` and friends are pure arithmetic; the
                    // exact value is reconstructed on demand in
                    // `term_for_numeric_arith_call`, so no fact is needed here.

                    // `core::slice::range` returns `Range { start, end }` with
                    // `0 <= start <= end <= bounds.end`.  Assert this so callers
                    // that derive subslice pointers from the result (e.g.
                    // `slice::copy_within`) can prove the offsets are in bounds.
                    if let Some(bounds_arg) = call.effects.iter().find_map(|effect| match effect {
                        crate::verify::call_summary::CallEffect::ReturnBoundedRange {
                            bounds_arg,
                        } => Some(*bounds_arg),
                        _ => None,
                    }) {
                        self.assert_bounded_range(solver, call, bounds_arg);
                    }

                    // `align_to_offsets` returns `(us_len, ts_len)` where `ts_len
                    // <= receiver.len()` and `us_len * size_of::<U>() <=
                    // receiver.len() * size_of::<T>()` (the byte count does not
                    // exceed the receiver).  The weaker `field_1 <= len(receiver)`
                    // is enough for the tail `ptr.add(receiver.len() - field_1)`
                    // to remain in bounds.
                    if let Some(recv_arg) = call.effects.iter().find_map(|effect| match effect {
                        crate::verify::call_summary::CallEffect::ReturnLcmSplit {
                            receiver_arg,
                        } => Some(*receiver_arg),
                        _ => None,
                    }) {
                        self.assert_lcm_split_bounds(solver, call, recv_arg);
                    }
                }
                StateFact::KnownNonZero { place, reason } => {
                    self.assert_place_non_zero(solver, place, reason);
                }
                StateFact::KnownAligned {
                    place,
                    align,
                    ty_name,
                    reason,
                } => {
                    self.assert_known_alignment(solver, place, *align, ty_name, reason);
                }
                StateFact::KnownInit {
                    place,
                    ty_name,
                    elements,
                    reason,
                } => {
                    self.assumptions.push(SmtPredicate::Custom(format!(
                        "{} initialized for {ty_name}, {elements} element(s) ({reason})",
                        place_label(place)
                    )));
                }
                StateFact::KnownAllocated {
                    place,
                    object,
                    ty_name,
                    elements,
                    reason,
                } => {
                    self.assumptions.push(SmtPredicate::Custom(format!(
                        "{} allocated in {} for {ty_name}, {elements} element(s) ({reason})",
                        place_label(place),
                        place_label(object)
                    )));
                }
                StateFact::KnownConst {
                    place,
                    value,
                    reason,
                } => {
                    self.assert_known_const(solver, place, *value, reason);
                }
                StateFact::BranchEq {
                    value,
                    equals,
                    cmp_op,
                    cmp_lhs,
                    cmp_rhs,
                } => {
                    if let Some(term) = self.term_for_value(value, &mut HashSet::new()) {
                        let expected = Int::from_u64(self.ctx, *equals as u64);
                        solver.assert(&term._eq(&expected));
                        self.assumptions.push(SmtPredicate::Eq(
                            SmtTerm::Value(value_label(value)),
                            SmtTerm::Const(*equals as u64),
                        ));
                    }
                    if let (Some(op), Some(lhs), Some(rhs)) = (cmp_op, cmp_lhs, cmp_rhs) {
                        if let (Some(lhs_t), Some(rhs_t)) =
                            (self.value_to_int(lhs), self.value_to_int(rhs))
                        {
                            let holds = *equals == 1;
                            match (op, holds) {
                                (BinOp::Eq, true) | (BinOp::Ne, false) => {
                                    solver.assert(&lhs_t._eq(&rhs_t))
                                }
                                (BinOp::Ne, true) | (BinOp::Eq, false) => {
                                    solver.assert(&lhs_t._eq(&rhs_t).not())
                                }
                                (BinOp::Lt, true) | (BinOp::Ge, false) => {
                                    solver.assert(&lhs_t.lt(&rhs_t))
                                }
                                (BinOp::Le, true) | (BinOp::Gt, false) => {
                                    solver.assert(&lhs_t.le(&rhs_t))
                                }
                                (BinOp::Gt, true) | (BinOp::Le, false) => {
                                    solver.assert(&lhs_t.gt(&rhs_t))
                                }
                                (BinOp::Ge, true) | (BinOp::Lt, false) => {
                                    solver.assert(&lhs_t.ge(&rhs_t))
                                }
                                _ => {}
                            }
                        }
                    }
                }
                StateFact::Cast { target, source, .. } => {
                    self.assumptions.push(SmtPredicate::Eq(
                        SmtTerm::Place(target.clone()),
                        SmtTerm::Value(value_label(source)),
                    ));
                    if let AbstractValue::Place(source_place) = source {
                        if self
                            .place_ty(source_place)
                            .is_some_and(|ty| pointee_ty(ty).is_some())
                        {
                            self.assert_place_alignment(solver, source_place);
                        }
                    }
                    if let Some(term) = self.term_for_value(source, &mut HashSet::new()) {
                        self.place_terms.insert(target.clone(), term);
                    }
                }
                StateFact::Binary {
                    target,
                    op,
                    lhs,
                    rhs,
                } => {
                    self.assumptions.push(SmtPredicate::Eq(
                        SmtTerm::Place(target.clone()),
                        SmtTerm::Value(format!(
                            "({} {} {})",
                            value_label(lhs),
                            binop_label(*op),
                            value_label(rhs)
                        )),
                    ));
                }
                StateFact::Contract(property) => match property.kind {
                    PropertyKind::Align => {
                        let Some(target) = (|| {
                            let arg = property.args.first()?;
                            let PropertyArg::Place(place) = arg else {
                                return None;
                            };
                            let mut key = PlaceKey::from_contract_place(place);
                            if let PlaceBaseKey::Arg(index) = key.base {
                                key.base = PlaceBaseKey::Local(index + 1);
                            }
                            Some(key)
                        })() else {
                            continue;
                        };
                        let Some(required_ty) = property.args.iter().find_map(|arg| {
                            if let PropertyArg::Ty(ty) = arg {
                                Some(*ty)
                            } else {
                                None
                            }
                        }) else {
                            continue;
                        };
                        let Some((align, _)) = self.type_layout(required_ty) else {
                            continue;
                        };
                        if align == 0 {
                            let ty_name = format!("{required_ty:?}");
                            if let Some(term) = self.term_for_place(&target) {
                                let align_term = self.symbolic_align_term(&ty_name);
                                let zero = Int::from_u64(self.ctx, 0);
                                solver.assert(&term.modulo(&align_term)._eq(&zero));
                                self.assumptions.push(SmtPredicate::Custom(format!(
                                    "{} aligned for {ty_name} (symbolic, struct-invariant)",
                                    place_label(&target)
                                )));
                            }
                        } else {
                            self.assert_known_alignment(
                                solver,
                                &target,
                                align,
                                &format!("{required_ty:?}"),
                                "struct-invariant",
                            );
                        }
                    }
                    PropertyKind::NonNull => {
                        let Some(target) = (|| {
                            let arg = property.args.first()?;
                            let PropertyArg::Place(place) = arg else {
                                return None;
                            };
                            let mut key = PlaceKey::from_contract_place(place);
                            if let PlaceBaseKey::Arg(index) = key.base {
                                key.base = PlaceBaseKey::Local(index + 1);
                            }
                            Some(key)
                        })() else {
                            continue;
                        };
                        self.assert_place_non_zero(solver, &target, "caller-contract");
                    }
                    PropertyKind::InBound => {
                        if let Some(PropertyArg::Expr(ContractExpr::IndexAccess { slice, index })) =
                            property.args.first()
                        {
                            let slice_key = match slice.as_ref() {
                                ContractExpr::Place(place) => {
                                    let mut key = PlaceKey::from_contract_place(place);
                                    if let PlaceBaseKey::Arg(ix) = key.base {
                                        key.base = PlaceBaseKey::Local(ix + 1);
                                    }
                                    key
                                }
                                _ => {
                                    continue;
                                }
                            };
                            let slice_label = place_label(&slice_key);
                            let len = SmtTerm::Value(format!("len({slice_label})"));

                            if let ContractExpr::Place(place) = index.as_ref() {
                                let mut index_key = PlaceKey::from_contract_place(place);
                                if let PlaceBaseKey::Arg(ix) = index_key.base {
                                    index_key.base = PlaceBaseKey::Local(ix + 1);
                                }
                                if let Some(ty) = self.place_ty(&index_key)
                                    && let TyKind::Array(_, len_const) = ty.kind()
                                {
                                    if let Some(array_len) = len_const.try_to_target_usize(self.tcx)
                                    {
                                        for j in 0..array_len {
                                            let elem_key = PlaceKey {
                                                base: index_key.base.clone(),
                                                fields: vec![j as usize],
                                            };
                                            let index_term = SmtTerm::Place(elem_key);
                                            let lower = index_term.clone();
                                            let upper = SmtTerm::Add(
                                                Box::new(index_term),
                                                Box::new(SmtTerm::Const(1)),
                                            );
                                            let preds = vec![
                                                SmtPredicate::Le(SmtTerm::Const(0), lower.clone()),
                                                SmtPredicate::Le(lower.clone(), upper.clone()),
                                                SmtPredicate::Le(upper, len.clone()),
                                            ];
                                            for pred in &preds {
                                                if let Some(bool_term) =
                                                    self.bool_for_predicate(pred)
                                                {
                                                    solver.assert(&bool_term);
                                                }
                                                self.assumptions.push(pred.clone());
                                            }
                                        }
                                        self.has_index_access_assumptions = true;
                                        continue;
                                    }
                                }
                                // Const-generic parameters (e.g. const N: usize) are
                                // always non-negative.  Assert this so that constraints like
                                // N != 0 or N >= 1 are provable.
                                for term in self.const_terms.values() {
                                    solver.assert(&term.ge(&Int::from_u64(self.ctx, 0)));
                                }
                            }

                            let index_term = match index.as_ref() {
                                ContractExpr::Place(place) => {
                                    let mut key = PlaceKey::from_contract_place(place);
                                    if let PlaceBaseKey::Arg(ix) = key.base {
                                        key.base = PlaceBaseKey::Local(ix + 1);
                                    }
                                    Some(SmtTerm::Place(key))
                                }
                                ContractExpr::Const(value) => {
                                    u64::try_from(*value).ok().map(SmtTerm::Const)
                                }
                                _ => None,
                            };
                            let Some(index_term) = index_term else {
                                continue;
                            };
                            let lower = index_term.clone();
                            let upper =
                                SmtTerm::Add(Box::new(index_term), Box::new(SmtTerm::Const(1)));
                            let preds = vec![
                                SmtPredicate::Le(SmtTerm::Const(0), lower.clone()),
                                SmtPredicate::Le(lower.clone(), upper.clone()),
                                SmtPredicate::Le(upper, len),
                            ];
                            for pred in &preds {
                                if let Some(bool_term) = self.bool_for_predicate(pred) {
                                    solver.assert(&bool_term);
                                }
                                self.assumptions.push(pred.clone());
                            }
                            self.has_index_access_assumptions = true;
                            continue;
                        }
                        // Handle 3-arg InBound(ptr, Ty, index) form
                        // args = [Place(slice_ptr), Ty(T), Expr(index)]
                        if property.args.len() == 3 {
                            let slice_place = match property.args.get(0) {
                                Some(PropertyArg::Place(place)) => place,
                                _ => {
                                    continue;
                                }
                            };
                            let index_expr = match property.args.get(2) {
                                Some(PropertyArg::Expr(expr)) => expr,
                                _ => {
                                    continue;
                                }
                            };
                            let slice_label = {
                                let mut key = PlaceKey::from_contract_place(slice_place);
                                if let PlaceBaseKey::Arg(ix) = key.base {
                                    key.base = PlaceBaseKey::Local(ix + 1);
                                }
                                place_label(&key)
                            };
                            let len = SmtTerm::Value(format!("len({slice_label})"));
                            let index_term = match index_expr {
                                ContractExpr::Place(place) => {
                                    let mut key = PlaceKey::from_contract_place(place);
                                    if let PlaceBaseKey::Arg(ix) = key.base {
                                        key.base = PlaceBaseKey::Local(ix + 1);
                                    }
                                    Some(SmtTerm::Place(key))
                                }
                                ContractExpr::Const(value) => {
                                    u64::try_from(*value).ok().map(SmtTerm::Const)
                                }
                                _ => None,
                            };
                            let Some(index_term) = index_term else {
                                continue;
                            };
                            let lower = index_term.clone();
                            let upper =
                                SmtTerm::Add(Box::new(index_term), Box::new(SmtTerm::Const(1)));
                            let preds = vec![
                                SmtPredicate::Le(SmtTerm::Const(0), lower.clone()),
                                SmtPredicate::Le(lower.clone(), upper.clone()),
                                SmtPredicate::Le(upper, len),
                            ];
                            for pred in &preds {
                                if let Some(bool_term) = self.bool_for_predicate(pred) {
                                    solver.assert(&bool_term);
                                }
                                self.assumptions.push(pred.clone());
                            }
                            self.has_index_access_assumptions = true;
                            continue;
                        }
                        let Some(target) = (|| {
                            let arg = property.args.first()?;
                            let PropertyArg::Place(place) = arg else {
                                return None;
                            };
                            let mut key = PlaceKey::from_contract_place(place);
                            if let PlaceBaseKey::Arg(index) = key.base {
                                key.base = PlaceBaseKey::Local(index + 1);
                            }
                            Some(key)
                        })() else {
                            continue;
                        };
                        let Some(required_ty) = property.args.iter().find_map(|arg| {
                            if let PropertyArg::Ty(ty) = arg {
                                Some(*ty)
                            } else {
                                None
                            }
                        }) else {
                            continue;
                        };
                        let Some((_, elem_size)) = self.type_layout(required_ty) else {
                            continue;
                        };
                        let access_count = property
                            .args
                            .iter()
                            .rev()
                            .find_map(|arg| {
                                let PropertyArg::Expr(ContractExpr::Const(value)) = arg else {
                                    return None;
                                };
                                u64::try_from(*value).ok()
                            })
                            .unwrap_or(0);
                        self.assumptions.push(SmtPredicate::InBounds {
                            index: SmtTerm::Const(0),
                            access_count: SmtTerm::Const(access_count),
                            len: SmtTerm::Value(format!("precond_len_{}", place_label(&target))),
                        });
                        if elem_size > 0 && access_count > 0 {
                            self.assumptions.push(SmtPredicate::Custom(format!(
                                "InBound({}, T, {access_count}) holds (caller-contract, elem_size={elem_size})",
                                place_label(&target)
                            )));
                        } else {
                            self.assumptions.push(SmtPredicate::Custom(format!(
                                "InBound({}, T, {access_count}) holds (caller-contract, symbolic)",
                                place_label(&target)
                            )));
                        }
                    }
                    PropertyKind::Init => {
                        let Some(target) = (|| {
                            let arg = property.args.first()?;
                            let PropertyArg::Place(place) = arg else {
                                return None;
                            };
                            let mut key = PlaceKey::from_contract_place(place);
                            if let PlaceBaseKey::Arg(index) = key.base {
                                key.base = PlaceBaseKey::Local(index + 1);
                            }
                            Some(key)
                        })() else {
                            continue;
                        };
                        let Some(required_ty) = property.args.iter().find_map(|arg| {
                            if let PropertyArg::Ty(ty) = arg {
                                Some(*ty)
                            } else {
                                None
                            }
                        }) else {
                            continue;
                        };
                        let elements = property
                            .args
                            .iter()
                            .rev()
                            .find_map(|arg| {
                                let PropertyArg::Expr(ContractExpr::Const(value)) = arg else {
                                    return None;
                                };
                                u64::try_from(*value).ok()
                            })
                            .unwrap_or(0);
                        self.assumptions.push(SmtPredicate::Custom(format!(
                            "{} initialized for {:?}, {elements} element(s) (caller-contract)",
                            place_label(&target),
                            required_ty
                        )));
                    }
                    PropertyKind::ValidNum => {
                        if let Some(PropertyArg::Predicates(predicates)) = property.args.first() {
                            for predicate in predicates {
                                if let Some(smt_pred) = self.contract_predicate_to_smt(predicate) {
                                    if let Some(z3_bool) = self.bool_for_predicate(&smt_pred) {
                                        solver.assert(&z3_bool);
                                    }
                                    self.assumptions.push(smt_pred);
                                }
                            }
                        }
                    }
                    _ => {}
                },
                StateFact::PathCondition(_)
                | StateFact::Drop(_)
                | StateFact::LocalDead(_)
                | StateFact::CallEffect(_) => {}
            }
        }

        // Assert unsigned-integer function arguments are non-negative.
        let body = self.tcx.optimized_mir(self.checkpoint.caller);
        for arg in 1..=body.arg_count {
            let place = PlaceKey {
                base: PlaceBaseKey::Local(arg),
                fields: Vec::new(),
            };
            let Some(ty) = self.place_ty(&place) else {
                continue;
            };
            if !is_unsigned_integral_ty(ty) {
                continue;
            }
            let Some(term) = self.term_for_place(&place) else {
                continue;
            };
            let zero = Int::from_u64(self.ctx, 0);
            solver.assert(&term.ge(&zero));
            self.assumptions
                .push(SmtPredicate::Ge(SmtTerm::Place(place), SmtTerm::Const(0)));
        }

        self.assert_round_down_products(solver);
    }

    /// Assert `p % d == 0` for every retained `(x / d) * d` round-down product
    /// `p`.  Sound because such a product is by construction a multiple of `d`;
    /// it hands z3 the one nonlinear fact it needs so the rest of the proof
    /// (e.g. a `split_at` prefix/suffix length feeding `len(self) % N == 0`)
    /// stays linear.
    fn assert_round_down_products(&mut self, solver: &Solver<'ctx>) {
        let mut candidates: Vec<(PlaceKey, AbstractValue<'tcx>)> = Vec::new();
        for fact in &self.forward.facts {
            let StateFact::Binary {
                target,
                op,
                lhs,
                rhs,
            } = fact
            else {
                continue;
            };
            if !matches!(op, BinOp::Mul | BinOp::MulWithOverflow) {
                continue;
            }
            let value = AbstractValue::Binary(*op, Box::new(lhs.clone()), Box::new(rhs.clone()));
            if let Some(divisor) = self.multiple_divisor(&value) {
                let product = if matches!(op, BinOp::MulWithOverflow) {
                    PlaceKey {
                        base: target.base.clone(),
                        fields: vec![0],
                    }
                } else {
                    target.clone()
                };
                candidates.push((product, divisor));
            }
        }

        let zero = Int::from_u64(self.ctx, 0);
        for (product, divisor) in candidates {
            let product_term = self.term_for_place(&product);
            let divisor_term =
                self.term_for_value_at(&divisor, self.latest_cursor(), &mut TraceSeen::new());
            if let (Some(product_term), Some(divisor_term)) = (product_term, divisor_term) {
                solver.assert(&product_term.modulo(&divisor_term)._eq(&zero));
                self.assumptions.push(SmtPredicate::Custom(format!(
                    "{} is a multiple of {}",
                    place_label(&product),
                    value_label(&divisor)
                )));
            }
        }
    }

    /// Return the path assumptions asserted by this model.
    pub(crate) fn assumptions(&self) -> &[SmtPredicate] {
        &self.assumptions
    }

    fn latest_cursor(&self) -> ValueCursor {
        self.forward.value_definitions.len()
    }

    fn call_definition_cursor(&self, call: &CallSummary<'tcx>) -> ValueCursor {
        self.forward
            .value_definitions
            .iter()
            .find_map(|definition| {
                if definition.local != call.destination {
                    return None;
                }
                let AbstractValue::CallResult(recorded) = &definition.value else {
                    return None;
                };
                if recorded.func == call.func && recorded.arg_count == call.arg_count {
                    Some(definition.ordinal)
                } else {
                    None
                }
            })
            .unwrap_or_else(|| self.latest_cursor())
    }

    /// Walk a pointer place's definition chain through plain copies to the
    /// nearest defining `Cast`, returning `(cast_operand, cast_target_ty)`.
    fn defining_cast(&self, place: &PlaceKey) -> Option<(AbstractValue<'tcx>, Ty<'tcx>)> {
        let mut cur = place.clone();
        for _ in 0..8 {
            let local = cur.local()?;
            let def = self
                .forward
                .latest_value_definition_before(local, self.latest_cursor())?;
            match &def.value {
                AbstractValue::Cast(inner, ty) => return Some(((**inner).clone(), *ty)),
                // `<*const [T; N]>::cast::<T>()` is a reinterpret cast expressed
                // as a method call rather than an `as` expression.  Treat it like
                // `AbstractValue::Cast`: the receiver is the source pointer and the
                // call destination's type is the cast target.
                AbstractValue::CallResult(call)
                    if PrimitiveCall::classify(&call.func) == Some(PrimitiveCall::PtrCast) =>
                {
                    let inner = call.args.first()?.clone();
                    let ty = self
                        .tcx
                        .optimized_mir(self.checkpoint.caller)
                        .local_decls
                        .get(call.destination)?
                        .ty;
                    return Some((inner, ty));
                }
                AbstractValue::Place(next) if next.fields.is_empty() => cur = next.clone(),
                _ => return None,
            }
        }
        None
    }

    /// Follow a cast operand through intermediate pointer casts and copies to
    /// the root pointer, returning its pointee type.  Handles the
    /// `*const [T; N] -> *const () -> *const T` reinterpret shape emitted by
    /// some toolchains, where the immediate operand's pointee (`()`) would
    /// otherwise hide the real `[T; N]` source element type.
    fn cast_source_pointee(&self, value: &AbstractValue<'tcx>, depth: usize) -> Option<Ty<'tcx>> {
        if depth > 8 {
            return None;
        }
        match value {
            AbstractValue::Cast(inner, _) => self.cast_source_pointee(inner, depth + 1),
            AbstractValue::Place(pk) | AbstractValue::RawPtr(pk) | AbstractValue::Ref(pk) => {
                if let Some(local) = pk.local()
                    && let Some(def) = self
                        .forward
                        .latest_value_definition_before(local, self.latest_cursor())
                    && matches!(def.value, AbstractValue::Cast(..))
                {
                    return self.cast_source_pointee(&def.value, depth + 1);
                }
                self.place_ty(pk).and_then(pointee_ty)
            }
            _ => None,
        }
    }

    /// Try to recover the slice index/length terms behind a pointer result.
    ///
    /// Supported forms:
    ///
    /// - `slice.as_ptr().add(index)` and wrappers summarized as `ReturnPointerAdd`
    /// - plain `slice.as_ptr()` / `slice.as_mut_ptr()`, treated as index `0`
    pub(crate) fn pointer_bounds_for_place(
        &mut self,
        place: &PlaceKey,
    ) -> Option<PointerBounds<'ctx>> {
        if let Some(call) = self.pointer_add_call_for_place(place) {
            let (base_arg, offset_arg) = call.effects.iter().find_map(|effect| match effect {
                crate::verify::call_summary::CallEffect::ReturnPointerAdd {
                    base_arg,
                    offset_arg,
                    ..
                }
                | crate::verify::call_summary::CallEffect::ReturnPointerSub {
                    base_arg,
                    offset_arg,
                    ..
                } => Some((*base_arg, *offset_arg)),
                _ => None,
            })?;
            let base = call.args.get(base_arg)?;
            let index = call.args.get(offset_arg)?;
            let call_cursor = self.call_definition_cursor(&call);
            let base_origin =
                self.origin_key_for_value_before(base, call_cursor, &mut TraceSeen::new())?;

            let index_term = self.term_for_value_at(index, call_cursor, &mut TraceSeen::new())?;
            let (len_term_int, len_term) = self.bounds_len_for_origin(&base_origin, Some(index))?;

            // For pointer arithmetic on a base pointer that is a Range field,
            // adjust the index: base_offset +/- count instead of just count.
            let result_index_smt: SmtTerm;
            let result_index_val: Int<'ctx>;
            if let AbstractValue::Place(base_place) = base {
                let (base_smt, base_val) = self.field_projection_index(base_place, &base_origin);
                if !matches!(&base_smt, SmtTerm::Const(0)) {
                    // base has a non-zero offset — adjust by the arithmetic
                    let is_sub = call_has_pointer_sub_effect(&call);
                    let (adjusted_val, adjusted_smt) = if is_sub {
                        let v = Int::sub(&self.ctx, &[base_val, index_term]);
                        let s = SmtTerm::Sub(
                            Box::new(base_smt),
                            Box::new(SmtTerm::Value(value_label(index))),
                        );
                        (v, s)
                    } else {
                        let v = Int::add(&self.ctx, &[base_val, index_term]);
                        let s = SmtTerm::Add(
                            Box::new(base_smt),
                            Box::new(SmtTerm::Value(value_label(index))),
                        );
                        (v, s)
                    };
                    result_index_val = adjusted_val;
                    result_index_smt = adjusted_smt;
                } else {
                    result_index_val = index_term;
                    result_index_smt = SmtTerm::Value(value_label(index));
                }
            } else {
                result_index_val = index_term;
                result_index_smt = SmtTerm::Value(value_label(index));
            }

            return Some(PointerBounds {
                index: result_index_val,
                len: len_term_int,
                index_term: result_index_smt,
                len_term,
                origin_key: base_origin,
            });
        }

        let value = self
            .resolved_value_for_place(place, &mut TraceSeen::new())
            .unwrap_or_else(|| AbstractValue::Place(place.clone()));
        let base_origin =
            self.origin_key_for_value_before(&value, self.latest_cursor(), &mut TraceSeen::new())?;
        let zero = AbstractValue::ConstInt(0);
        // When the origin key traces to a null literal (e.g. null_mut()),
        // bounds_len_for_origin may return bogus index offsets like
        // len(null_ref).  Skip it and use the PointsTo fallback instead.
        let is_null_origin = base_origin.contains("null_mut")
            || base_origin.contains("null(")
            || value_label(&value).contains("null_mut");
        let (mut len_term_int, mut len_term) = if !is_null_origin {
            if let Some(bounds) = self.bounds_len_for_origin(&base_origin, Some(&zero)) {
                bounds
            } else if let Some(bounds) =
                self.allocated_bounds_via_points_to(place, &value, &base_origin)
            {
                bounds
            } else {
                return None;
            }
        } else if let Some(bounds) =
            self.allocated_bounds_via_points_to(place, &value, &base_origin)
        {
            bounds
        } else {
            return None;
        };

        if place.fields.is_empty()
            && let Some((inner, cast_ty)) = self.defining_cast(place)
        {
            let caller = self.checkpoint.caller;
            if let Some(dst_pt) = pointee_ty(cast_ty) {
                let dst_size = safe_type_layout(self.tcx, caller, dst_pt).map(|(_, s)| s);
                // Follow the cast/copy chain to the *root* pointer's pointee
                // type.  On some toolchains a `*const [T; N] -> *const T`
                // reinterpret is lowered through an intermediate `*const ()`
                // cast (and a copy), so inspecting only the immediate operand
                // would yield `()` and miss the `[T; N] -> T` stride ratio.
                let src_ty = self.cast_source_pointee(&inner, 0);
                let src_size =
                    src_ty.and_then(|pt| safe_type_layout(self.tcx, caller, pt).map(|(_, s)| s));
                let ratio_smt = match (src_size, dst_size) {
                    (Some(src), Some(dst)) if src > dst && src % dst == 0 => {
                        Some(SmtTerm::Const(src / dst))
                    }
                    _ => {
                        if let (Some(src_pty), Some(dst_pty)) = (src_ty, Some(dst_pt)) {
                            pointee_stride_from_types(self.tcx, src_pty, dst_pty)
                        } else {
                            None
                        }
                    }
                };
                if let Some(ratio_smt) = ratio_smt {
                    let ratio_int = self.term_for_smt_term(&ratio_smt)?;
                    len_term_int = Int::mul(self.ctx, &[len_term_int, ratio_int]);
                    len_term = SmtTerm::Mul(Box::new(len_term), Box::new(ratio_smt));
                }
            }
        }

        // Compute the correct index for field projections from Range types.
        // Field [0] (start) is at offset 0; field [1] (end) is at offset len.
        let (index_term, index_val) = self.field_projection_index(place, &base_origin);

        Some(PointerBounds {
            index: index_val,
            len: len_term_int,
            index_term,
            len_term,
            origin_key: base_origin,
        })
    }

    /// Walk the value chain for `place` to determine if it is a field projection
    /// from an `as_ptr_range`/`as_mut_ptr_range` result (or an inlined equivalent).
    /// Returns (index_term, index_val).  Field [0] (start) → offset 0;
    /// field [1] (end) → offset len.
    fn field_projection_index(
        &mut self,
        place: &PlaceKey,
        origin_key: &str,
    ) -> (SmtTerm, Int<'ctx>) {
        let default_index = SmtTerm::Const(0);
        let default_val = Int::from_u64(self.ctx, 0);

        let mut cur_place = place.clone();
        loop {
            if !cur_place.fields.is_empty() {
                let field_idx = cur_place.fields.as_slice();
                let mut base = cur_place.clone();
                base.fields.clear();
                if let Some(local) = base.local() {
                    if let Some(definition) = self
                        .forward
                        .latest_value_definition_before(local, self.latest_cursor())
                    {
                        let is_range = match &definition.value {
                            AbstractValue::CallResult(call) => {
                                let prim = PrimitiveCall::classify(&call.func);
                                prim == Some(PrimitiveCall::AsPtrRange)
                                    || prim == Some(PrimitiveCall::AsMutPtrRange)
                            }
                            AbstractValue::Aggregate(_, _) => true,
                            _ => false,
                        };
                        if is_range {
                            if field_idx == [0] {
                                return (SmtTerm::Const(0), Int::from_u64(self.ctx, 0));
                            }
                            if field_idx == [1] {
                                let len_key = format!("len({})", origin_key);
                                let len_val = self.symbolic_len_term(&len_key);
                                return (SmtTerm::Value(len_key), len_val);
                            }
                        }
                        // Follow Cast facts for inlined aggregates
                        for fact in &self.forward.facts {
                            if let StateFact::Cast { target, source, .. } = fact {
                                if *target == cur_place {
                                    if let AbstractValue::Place(p) = source {
                                        cur_place = p.clone();
                                        // Try again with the new place
                                        if cur_place.fields.as_slice() == [1] {
                                            let mut inner_base = cur_place.clone();
                                            inner_base.fields.clear();
                                            if let Some(inner_local) = inner_base.local() {
                                                if let Some(inner_def) =
                                                    self.forward.latest_value_definition_before(
                                                        inner_local,
                                                        self.latest_cursor(),
                                                    )
                                                {
                                                    if let AbstractValue::CallResult(inner_call) =
                                                        &inner_def.value
                                                    {
                                                        let inner_prim = PrimitiveCall::classify(
                                                            &inner_call.func,
                                                        );
                                                        if inner_prim
                                                            == Some(PrimitiveCall::AsPtrRange)
                                                            || inner_prim
                                                                == Some(
                                                                    PrimitiveCall::AsMutPtrRange,
                                                                )
                                                        {
                                                            let len_key =
                                                                format!("len({})", origin_key);
                                                            let len_val =
                                                                self.symbolic_len_term(&len_key);
                                                            return (
                                                                SmtTerm::Value(len_key),
                                                                len_val,
                                                            );
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
                return (default_index, default_val);
            }

            if let Some(local) = cur_place.local() {
                if let Some(definition) = self
                    .forward
                    .latest_value_definition_before(local, self.latest_cursor())
                {
                    match &definition.value {
                        AbstractValue::Place(p) => {
                            cur_place = p.clone();
                            continue;
                        }
                        _ => {}
                    }
                }
            }
            return (default_index, default_val);
        }
    }

    /// Recover the allocation object and element offset for a pointer-like
    /// place. This is intentionally small: it handles base pointers returned by
    /// `as_ptr`/`as_mut_ptr` and offsets produced by pointer arithmetic
    /// summaries.
    fn pointer_object_offset_for_place(&self, place: &PlaceKey) -> Option<(PlaceKey, SmtTerm)> {
        self.pointer_object_offset_for_place_before(
            place,
            self.latest_cursor(),
            &mut TraceSeen::new(),
        )
    }

    fn pointer_object_offset_for_place_before(
        &self,
        place: &PlaceKey,
        cursor: ValueCursor,
        seen: &mut TraceSeen,
    ) -> Option<(PlaceKey, SmtTerm)> {
        if let Some(object) = self.allocated_object_for_place(place) {
            return Some((object, SmtTerm::Const(0)));
        }
        let seen_key = (place.clone(), cursor);
        if !seen.insert(seen_key) {
            return None;
        }
        let local = place.local()?;
        let definition = self.forward.latest_value_definition_before(local, cursor)?;
        self.pointer_object_offset_for_value(&definition.value, definition.ordinal, seen)
    }

    fn pointer_object_offset_for_value(
        &self,
        value: &AbstractValue<'tcx>,
        cursor: ValueCursor,
        seen: &mut TraceSeen,
    ) -> Option<(PlaceKey, SmtTerm)> {
        match value {
            AbstractValue::Place(place) => {
                self.pointer_object_offset_for_place_before(place, cursor, seen)
            }
            AbstractValue::Cast(inner, _) => {
                self.pointer_object_offset_for_value(inner, cursor, seen)
            }
            AbstractValue::CallResult(call) => {
                if call_has_pointer_add_effect(call) || is_pointer_add_call(&call.func) {
                    let (base_arg, offset_arg) = call
                        .effects
                        .iter()
                        .find_map(|effect| {
                            let crate::verify::call_summary::CallEffect::ReturnPointerAdd {
                                base_arg,
                                offset_arg,
                                ..
                            } = effect
                            else {
                                return None;
                            };
                            Some((*base_arg, *offset_arg))
                        })
                        .unwrap_or((0, 1));
                    let call_cursor = self.call_definition_cursor(call);
                    let (object, base_offset) = self.pointer_object_offset_for_value(
                        call.args.get(base_arg)?,
                        call_cursor,
                        seen,
                    )?;
                    let offset = smt_term_for_value(call.args.get(offset_arg)?)?;
                    return Some((
                        object,
                        SmtTerm::Add(Box::new(base_offset), Box::new(offset)),
                    ));
                }
                if call_has_pointer_sub_effect(call) || is_pointer_sub_call(&call.func) {
                    let (base_arg, offset_arg) = call
                        .effects
                        .iter()
                        .find_map(|effect| {
                            let crate::verify::call_summary::CallEffect::ReturnPointerSub {
                                base_arg,
                                offset_arg,
                                ..
                            } = effect
                            else {
                                return None;
                            };
                            Some((*base_arg, *offset_arg))
                        })
                        .unwrap_or((0, 1));
                    let call_cursor = self.call_definition_cursor(call);
                    let (object, base_offset) = self.pointer_object_offset_for_value(
                        call.args.get(base_arg)?,
                        call_cursor,
                        seen,
                    )?;
                    let offset = smt_term_for_value(call.args.get(offset_arg)?)?;
                    return Some((
                        object,
                        SmtTerm::Sub(Box::new(base_offset), Box::new(offset)),
                    ));
                }
                let destination = PlaceKey {
                    base: PlaceBaseKey::Local(call.destination.as_usize()),
                    fields: Vec::new(),
                };
                self.allocated_object_for_place(&destination)
                    .map(|object| (object, SmtTerm::Const(0)))
            }
            _ => None,
        }
    }

    fn allocated_object_for_place(&self, place: &PlaceKey) -> Option<PlaceKey> {
        // 1) KnownAllocated facts (concrete allocations).
        if let Some(object) = self.forward.facts.iter().find_map(|fact| match fact {
            StateFact::KnownAllocated {
                place: allocated_place,
                object,
                ..
            } if allocated_place == place => Some(object.clone()),
            _ => None,
        }) {
            return Some(object);
        }
        // 2) PointsTo facts — when a pointer (or a projection of one)
        //    traces to a reference, the reference is the allocation object.
        let base = if place.fields.is_empty() {
            place.clone()
        } else {
            PlaceKey {
                base: place.base.clone(),
                fields: Vec::new(),
            }
        };
        if let Some(source) = self.forward.facts.iter().find_map(|fact| match fact {
            StateFact::PointsTo { pointer, source } if *pointer == base => Some(source.clone()),
            _ => None,
        }) {
            return Some(source);
        }
        None
    }

    /// Assert that a place is known to denote a non-zero address.
    pub(crate) fn assert_place_non_zero(
        &mut self,
        solver: &Solver<'ctx>,
        place: &PlaceKey,
        reason: &str,
    ) {
        let label = place_label(place);
        if let Some(term) = self.term_for_place(place) {
            let zero = Int::from_u64(self.ctx, 0);
            solver.assert(&term._eq(&zero).not());
            self.assumptions
                .push(SmtPredicate::Custom(format!("{label} != 0 ({reason})",)));
        }
    }

    /// Assert the `0 <= start <= end <= bounds.end` postcondition of a
    /// `core::slice::range` result.  `call.destination` is the returned
    /// `Range` (field 0 = start, field 1 = end); `bounds_arg` is a `RangeTo`
    /// whose field 0 is the upper limit (the slice length).
    fn assert_bounded_range(
        &mut self,
        solver: &Solver<'ctx>,
        call: &CallSummary<'tcx>,
        bounds_arg: usize,
    ) {
        let start = PlaceKey {
            base: PlaceBaseKey::Local(call.destination.as_usize()),
            fields: vec![0],
        };
        let end = PlaceKey {
            base: PlaceBaseKey::Local(call.destination.as_usize()),
            fields: vec![1],
        };
        let (Some(start_term), Some(end_term)) =
            (self.term_for_place(&start), self.term_for_place(&end))
        else {
            return;
        };
        let zero = Int::from_u64(self.ctx, 0);
        solver.assert(&start_term.ge(&zero));
        solver.assert(&start_term.le(&end_term));
        if let Some(AbstractValue::Place(bounds_place)) = call.args.get(bounds_arg) {
            let mut bounds_end = bounds_place.clone();
            bounds_end.fields.push(0);
            if let Some(bounds_term) = self.term_for_place(&bounds_end) {
                solver.assert(&end_term.le(&bounds_term));
            }
        }
    }

    /// Assert the weak `field_1 <= len(receiver)` postcondition of
    /// `align_to_offsets`.  `call.destination` is the returned `(usize, usize)`
    /// tuple (field 0 = us_len, field 1 = ts_len).
    fn assert_lcm_split_bounds(
        &mut self,
        solver: &Solver<'ctx>,
        call: &CallSummary<'tcx>,
        receiver_arg: usize,
    ) {
        let ts_len = PlaceKey {
            base: PlaceBaseKey::Local(call.destination.as_usize()),
            fields: vec![1],
        };
        let (Some(ts_term), Some(recv)) =
            (self.term_for_place(&ts_len), call.args.get(receiver_arg))
        else {
            return;
        };
        let recv_key = self
            .origin_key_for_value_before(recv, self.latest_cursor(), &mut TraceSeen::new())
            .unwrap_or_else(|| value_label(recv));
        let len_key = format!("len({recv_key})");
        let bounds_len = self.symbolic_len_term(&len_key);
        // ts_len >= 0 (usize lower bound); Z3 treats symbolic integers as
        // unbounded, so without this the goal `(len - ts_len) <= len` can be
        // defeated by a negative `ts_len`.
        solver.assert(&ts_term.ge(&Int::from_u64(self.ctx, 0)));
        solver.assert(&ts_term.le(&bounds_len));
    }

    /// Assert known alignment for a place when its MIR type provides one.
    fn assert_place_alignment(&mut self, solver: &Solver<'ctx>, place: &PlaceKey) {
        let Some(ty) = self.place_ty(place) else {
            return;
        };
        let Some(align_ty) = pointee_ty(ty).or(Some(ty)) else {
            return;
        };
        let Some(align) = self.guaranteed_alignment(align_ty) else {
            return;
        };
        if align > 0 && align <= 1 {
            return;
        }
        if let Some(term) = self.term_for_place(place) {
            let zero = Int::from_u64(self.ctx, 0);
            let align_term = if align == 0 {
                self.symbolic_align_term(&format!("{align_ty:?}"))
            } else {
                Int::from_u64(self.ctx, align)
            };
            solver.assert(&term.modulo(&align_term)._eq(&zero));
            self.assumptions.push(SmtPredicate::Custom(format!(
                "{} aligned for {align_ty:?} ({} bytes)",
                place_label(place),
                if align == 0 {
                    "symbolic".to_string()
                } else {
                    align.to_string()
                }
            )));
        }
    }

    /// Assert an explicitly summarized alignment fact.
    fn assert_known_alignment(
        &mut self,
        solver: &Solver<'ctx>,
        place: &PlaceKey,
        align: u64,
        ty_name: &str,
        reason: &str,
    ) {
        if align == 0 {
            if let Some(term) = self.term_for_place(place) {
                let align_term = self.symbolic_align_term(ty_name);
                let zero = Int::from_u64(self.ctx, 0);
                solver.assert(&term.modulo(&align_term)._eq(&zero));
                self.assumptions.push(SmtPredicate::Custom(format!(
                    "{} aligned for {ty_name} (symbolic, {reason})",
                    place_label(place)
                )));
            }
            return;
        }
        if align <= 1 {
            return;
        }
        if let Some(term) = self.term_for_place(place) {
            let align_term = Int::from_u64(self.ctx, align);
            let k = Int::new_const(self.ctx, format!("{}_ka_k", place_label(place)));
            solver.assert(&term._eq(&Int::mul(self.ctx, &[k, align_term.clone()])));
            let zero = Int::from_u64(self.ctx, 0);
            solver.assert(&term.modulo(&align_term)._eq(&zero));
            self.assumptions.push(SmtPredicate::Custom(format!(
                "{} aligned for {ty_name} ({align} bytes, {reason})",
                place_label(place)
            )));
        }
    }

    /// Assert that a place is equal to a concrete layout/numeric constant.
    fn assert_known_const(
        &mut self,
        solver: &Solver<'ctx>,
        place: &PlaceKey,
        value: u64,
        reason: &str,
    ) {
        if let Some(term) = self.term_for_place(place) {
            let value_term = Int::from_u64(self.ctx, value);
            solver.assert(&term._eq(&value_term));
            self.assumptions.push(SmtPredicate::Custom(format!(
                "{} == {value} ({reason})",
                place_label(place)
            )));
        }
    }

    /// Assert equal slice lengths for two slice-like places that alias.
    fn assert_length_alias(&mut self, solver: &Solver<'ctx>, left: &PlaceKey, right: &PlaceKey) {
        if !self.is_len_carrying_place(left) || !self.is_len_carrying_place(right) {
            return;
        }
        let left_label = place_label(left);
        let right_label = place_label(right);
        let lhs = self.symbolic_len_term(&format!("len({left_label})"));
        let rhs = self.symbolic_len_term(&format!("len({right_label})"));
        solver.assert(&lhs._eq(&rhs));
        self.assumptions.push(SmtPredicate::Eq(
            SmtTerm::Value(format!("len({left_label})")),
            SmtTerm::Value(format!("len({right_label})")),
        ));
    }

    fn is_len_carrying_place(&self, place: &PlaceKey) -> bool {
        self.place_ty(place).is_some_and(is_len_carrying_ty)
    }

    /// True when `place` (or its resolved root) is a reference or slice.
    fn place_is_len_carrying_slice(&self, place: &PlaceKey) -> bool {
        if self.is_len_carrying_place(place) {
            return true;
        }
        // Follow resolved provenance through pointer-arithmetic/cast chains.
        self.resolved_value_for_place(place, &mut TraceSeen::new())
            .and_then(|value| {
                let root = match &value {
                    AbstractValue::Place(pk) => pk,
                    AbstractValue::RawPtr(pk) => pk,
                    AbstractValue::Ref(pk) => pk,
                    AbstractValue::CallResult(call) => {
                        return self
                            .place_ty(&PlaceKey {
                                base: PlaceBaseKey::Local(call.destination.as_usize()),
                                fields: Vec::new(),
                            })
                            .map(|ty| is_len_carrying_ty(ty));
                    }
                    _ => return Some(false),
                };
                Some(self.is_len_carrying_place(root))
            })
            .unwrap_or(false)
    }

    /// Bridge the prefix length produced by a `split_at`-style call into the
    /// symbolic `len(...)` namespace.
    ///
    /// `ReturnTupleFieldLength { field: 0, from_arg }` records that field 0 of
    /// the returned tuple is a slice of length `args[from_arg]` (the `mid`
    /// split point).  `record_call_effect_assumptions` stores this only as the
    /// *value* term of `dest.0`, which the `len(place)` contract lowering (and
    /// `assert_length_alias`) never observe.  Here we additionally assert
    /// `len(P) == mid` for `dest.0` itself and for every local that copies it
    /// out of the tuple (the destructured `multiple_of_n`), so that a later
    /// `len(self)` obligation on the prefix — or a reborrow of it linked via
    /// `assert_length_alias` — resolves to the correct `mid` rather than a
    /// free symbol.
    fn bridge_tuple_field_lengths(&mut self, solver: &Solver<'ctx>, call: &CallSummary<'tcx>) {
        for effect in &call.effects {
            let crate::verify::call_summary::CallEffect::ReturnTupleFieldLength { field, .. } =
                effect
            else {
                continue;
            };
            if *field != 0 {
                continue;
            }
            let dest0 = PlaceKey {
                base: PlaceBaseKey::Local(call.destination.as_usize()),
                fields: vec![0],
            };
            let Some(mid_term) = self.place_terms.get(&dest0).cloned() else {
                continue;
            };

            // Field 0 (prefix) has length `mid`.
            self.bridge_field_length(solver, call.destination.as_usize(), 0, &mid_term);

            // Field 1 (suffix) has length `len(receiver) - mid`.  Its
            // divisibility (when the split rounds down to a multiple) follows
            // from the global round-down-product assertion once z3 relates the
            // receiver length to the length used inside `mid`.
            if let Some(AbstractValue::Place(receiver)) = call.args.first() {
                let len_recv = self.symbolic_len_term(&format!("len({})", place_label(receiver)));
                let suffix_term = Int::sub(self.ctx, &[len_recv, mid_term.clone()]);
                self.bridge_field_length(solver, call.destination.as_usize(), 1, &suffix_term);
            }
        }
    }

    /// Assert `len(P) == len_term` for tuple field `dest.field_index` and for
    /// every local that copies it out of the tuple (the destructured slice).
    fn bridge_field_length(
        &mut self,
        solver: &Solver<'ctx>,
        destination: usize,
        field_index: usize,
        len_term: &Int<'ctx>,
    ) {
        let dest_key = PlaceKey {
            base: PlaceBaseKey::Local(destination),
            fields: vec![field_index],
        };
        let mut targets: Vec<PlaceKey> = vec![dest_key.clone()];
        for def in &self.forward.value_definitions {
            if let AbstractValue::Place(source) = &def.value
                && source == &dest_key
            {
                targets.push(PlaceKey {
                    base: PlaceBaseKey::Local(def.local.as_usize()),
                    fields: Vec::new(),
                });
            }
        }

        for place in targets {
            if !self.is_len_carrying_place(&place) {
                continue;
            }
            let len_key = format!("len({})", place_label(&place));
            let place_len = self.symbolic_len_term(&len_key);
            solver.assert(&place_len._eq(len_term));
            self.assumptions.push(SmtPredicate::Custom(format!(
                "{len_key} == split field {field_index} length"
            )));
        }
    }

    /// If `value` provably equals `(x / d) * d` for some divisor `d`, return
    /// `d`.  Such a value is always a multiple of `d`.  Recognises the
    /// `slice.len() / N * N` (round-down-to-multiple) idiom, including the
    /// `MulWithOverflow`/`.0` shape produced by MIR overflow checks.
    fn multiple_divisor(&self, value: &AbstractValue<'tcx>) -> Option<AbstractValue<'tcx>> {
        let AbstractValue::Binary(op, lhs, rhs) = self.resolve_arith(value, 0)? else {
            return None;
        };
        if !matches!(op, BinOp::Mul | BinOp::MulWithOverflow) {
            return None;
        }
        let lhs_a = self.resolve_arith(&lhs, 0).unwrap_or((*lhs).clone());
        let rhs_a = self.resolve_arith(&rhs, 0).unwrap_or((*rhs).clone());
        for (maybe_div, other) in [(&lhs_a, &rhs_a), (&rhs_a, &lhs_a)] {
            if let AbstractValue::Binary(BinOp::Div, _, divisor) = maybe_div {
                let divisor_a = self
                    .resolve_arith(divisor, 0)
                    .unwrap_or((**divisor).clone());
                if value_label(&divisor_a) == value_label(other) {
                    return Some(divisor_a);
                }
            }
        }
        None
    }

    /// Resolve an abstract value to its arithmetic shape, following copies and
    /// casts and unwrapping the `.0` field of `*WithOverflow` binary results.
    fn resolve_arith(
        &self,
        value: &AbstractValue<'tcx>,
        depth: usize,
    ) -> Option<AbstractValue<'tcx>> {
        if depth > 16 {
            return None;
        }
        match value {
            AbstractValue::Place(place) if place.fields == [0] => {
                let base = PlaceKey {
                    base: place.base.clone(),
                    fields: Vec::new(),
                };
                match value_for_place(self.forward, &base)? {
                    AbstractValue::Binary(op, l, r) => {
                        let normalized = match op {
                            BinOp::MulWithOverflow => BinOp::Mul,
                            BinOp::AddWithOverflow => BinOp::Add,
                            BinOp::SubWithOverflow => BinOp::Sub,
                            other => *other,
                        };
                        Some(AbstractValue::Binary(normalized, l.clone(), r.clone()))
                    }
                    _ => None,
                }
            }
            AbstractValue::Place(place) => {
                let inner = value_for_place(self.forward, place)?.clone();
                self.resolve_arith(&inner, depth + 1)
            }
            AbstractValue::Cast(inner, _) => self.resolve_arith(inner, depth + 1),
            _ => Some(value.clone()),
        }
    }

    /// Record call-effect definitions that the term builder understands.
    fn record_call_effect_assumptions(&mut self, call: &CallSummary<'tcx>) {
        let destination = PlaceKey {
            base: PlaceBaseKey::Local(call.destination.as_usize()),
            fields: Vec::new(),
        };
        let cursor = self.call_definition_cursor(call);
        for effect in &call.effects {
            match effect {
                crate::verify::call_summary::CallEffect::ReturnPointerAdd {
                    base_arg,
                    offset_arg,
                    stride,
                } => {
                    let base_term = call
                        .args
                        .get(*base_arg)
                        .and_then(|v| self.term_for_value_at(v, cursor, &mut TraceSeen::new()));
                    let offset_term = call
                        .args
                        .get(*offset_arg)
                        .and_then(|v| self.term_for_value_at(v, cursor, &mut TraceSeen::new()));
                    if let (Some(base), Some(offset)) = (base_term, offset_term) {
                        let stride = Int::from_u64(self.ctx, stride.unwrap_or(1));
                        let term =
                            Int::add(self.ctx, &[base, Int::mul(self.ctx, &[offset, stride])]);
                        self.place_terms.insert(destination.clone(), term);
                    }
                }
                crate::verify::call_summary::CallEffect::ReturnPointerSub {
                    base_arg,
                    offset_arg,
                    stride,
                } => {
                    let base_term = call
                        .args
                        .get(*base_arg)
                        .and_then(|v| self.term_for_value_at(v, cursor, &mut TraceSeen::new()));
                    let offset_term = call
                        .args
                        .get(*offset_arg)
                        .and_then(|v| self.term_for_value_at(v, cursor, &mut TraceSeen::new()));
                    if let (Some(base), Some(offset)) = (base_term, offset_term) {
                        let stride = Int::from_u64(self.ctx, stride.unwrap_or(1));
                        let term =
                            Int::sub(self.ctx, &[base, Int::mul(self.ctx, &[offset, stride])]);
                        self.place_terms.insert(destination.clone(), term);
                    }
                }
                crate::verify::call_summary::CallEffect::ReturnLengthOfArg { arg } => {
                    let raw_source = call
                        .args
                        .get(*arg)
                        .and_then(|value| {
                            self.origin_key_for_value_before(value, cursor, &mut TraceSeen::new())
                        })
                        .or_else(|| call.args.get(*arg).map(value_label))
                        .unwrap_or_else(|| format!("arg{arg}"));
                    // Strip Deref projections (e.g. _1.* → _1) so the
                    // length term matches the contract's len(self) key.
                    let source = raw_source.split('.').next().unwrap_or(&raw_source);
                    let len_key = format!("len({source})");
                    let len_term = self.symbolic_len_term(&len_key);
                    self.place_terms.insert(destination.clone(), len_term);
                    self.assumptions.push(SmtPredicate::Eq(
                        SmtTerm::Place(destination.clone()),
                        SmtTerm::Value(len_key),
                    ));
                }
                crate::verify::call_summary::CallEffect::ReturnIsEmptyOfArg { arg } => {
                    let raw_source = call
                        .args
                        .get(*arg)
                        .and_then(|value| {
                            self.origin_key_for_value_before(value, cursor, &mut TraceSeen::new())
                        })
                        .or_else(|| call.args.get(*arg).map(value_label))
                        .unwrap_or_else(|| format!("arg{arg}"));
                    let source = raw_source.split('.').next().unwrap_or(&raw_source);
                    let len_key = format!("len({source})");
                    let len_term = self.symbolic_len_term(&len_key);
                    let zero = Int::from_u64(self.ctx, 0);
                    let one = Int::from_u64(self.ctx, 1);
                    let term = len_term._eq(&zero).ite(&one, &zero);
                    self.place_terms.insert(destination.clone(), term);
                    self.assumptions.push(SmtPredicate::Custom(format!(
                        "{} == ({len_key} == 0)",
                        place_label(&destination)
                    )));
                }
                crate::verify::call_summary::CallEffect::ReturnPointerFromArg { arg }
                | crate::verify::call_summary::CallEffect::ReturnAliasArg { arg } => {
                    let source_value = call.args.get(*arg);
                    if let Some(term) = source_value.and_then(|value| {
                        self.term_for_value_at(value, cursor, &mut TraceSeen::new())
                    }) {
                        self.place_terms.insert(destination.clone(), term);
                    }
                    let source = source_value
                        .map(value_label)
                        .unwrap_or_else(|| format!("arg{arg}"));
                    self.assumptions.push(SmtPredicate::Eq(
                        SmtTerm::Place(destination.clone()),
                        SmtTerm::Value(source),
                    ));
                }
                crate::verify::call_summary::CallEffect::ReturnConst { .. } => {}
                crate::verify::call_summary::CallEffect::ReturnTupleFieldLength {
                    field,
                    from_arg,
                } => {
                    if *field == 0 {
                        let cursor = self.call_definition_cursor(call);
                        if let Some(mid_term) = call
                            .args
                            .get(*from_arg)
                            .and_then(|v| self.term_for_value_at(v, cursor, &mut TraceSeen::new()))
                        {
                            let label = value_label(
                                call.args
                                    .get(*from_arg)
                                    .unwrap_or(&AbstractValue::Unknown(String::new())),
                            );
                            let dest_key = PlaceKey {
                                base: PlaceBaseKey::Local(call.destination.as_usize()),
                                fields: vec![0],
                            };
                            self.place_terms.insert(dest_key.clone(), mid_term);
                            self.assumptions.push(SmtPredicate::Eq(
                                SmtTerm::Place(dest_key),
                                SmtTerm::Value(label),
                            ));
                        }
                    }
                }
                crate::verify::call_summary::CallEffect::ReturnNonZero
                | crate::verify::call_summary::CallEffect::ReturnAligned { .. }
                | crate::verify::call_summary::CallEffect::ReadMemory { .. }
                | crate::verify::call_summary::CallEffect::WriteMemory { .. }
                | crate::verify::call_summary::CallEffect::ChecksIndexBoundsDisjoint { .. }
                | crate::verify::call_summary::CallEffect::ReturnBoundedRange { .. }
                | crate::verify::call_summary::CallEffect::ReturnLcmSplit { .. }
                | crate::verify::call_summary::CallEffect::OwnsInitMemory { .. }
                | crate::verify::call_summary::CallEffect::ForgetArgFacts { .. } => {}
            }
        }
    }

    /// Build an SMT term for a place.
    pub(crate) fn term_for_place(&mut self, place: &PlaceKey) -> Option<Int<'ctx>> {
        self.term_for_place_before(place, self.latest_cursor(), &mut TraceSeen::new())
    }

    /// Build an SMT term for a place using only definitions before `cursor`.
    fn term_for_place_before(
        &mut self,
        place: &PlaceKey,
        cursor: ValueCursor,
        seen: &mut TraceSeen,
    ) -> Option<Int<'ctx>> {
        let seen_key = (place.clone(), cursor);
        if !seen.insert(seen_key) {
            return None;
        }

        if !place.fields.is_empty() {
            if let Some(term) = self.projected_term_for_place(place, cursor, seen) {
                return Some(term);
            }
            if let Some(term) = self.place_terms.get(place) {
                return Some(term.clone());
            }
            let term = Int::new_const(self.ctx, place_name(place));
            self.place_terms.insert(place.clone(), term.clone());
            return Some(term);
        }

        if let Some(local) = place.local()
            && let Some(definition) = self.forward.latest_value_definition_before(local, cursor)
        {
            if let Some(term) = self.term_for_value_at(&definition.value, definition.ordinal, seen)
            {
                return Some(term);
            }
        }

        if let Some(value) = self.path_value_definition_before(place, cursor)
            && let Some(term) = self.term_for_value_at(&value, cursor, seen)
        {
            return Some(term);
        }

        if let Some(term) = self.place_terms.get(place) {
            return Some(term.clone());
        }

        // Use a shared per-local cache so every reference to the same MIR
        // local (e.g. parameter `mid`) produces the identical Z3 term.
        if place.fields.is_empty()
            && let Some(local) = place.local()
        {
            let id = local.as_usize();
            if let Some(term) = self.local_terms.get(&id) {
                let term = term.clone();
                self.place_terms.insert(place.clone(), term.clone());
                return Some(term);
            }
            let term = Int::new_const(self.ctx, place_name(place));
            self.local_terms.insert(id, term.clone());
            self.place_terms.insert(place.clone(), term.clone());
            return Some(term);
        }

        let term = Int::new_const(self.ctx, place_name(place));
        self.place_terms.insert(place.clone(), term.clone());
        Some(term)
    }

    /// Build terms for well-known aggregate projections.
    ///
    /// Checked integer arithmetic is represented as `(value, overflow)` in MIR.
    /// For numeric reasoning we can use field `0` as the mathematical result.
    /// Field `1` remains a fresh value, so overflow assertions do not become
    /// accidental constraints on the result itself.
    fn projected_term_for_place(
        &mut self,
        place: &PlaceKey,
        cursor: ValueCursor,
        seen: &mut TraceSeen,
    ) -> Option<Int<'ctx>> {
        let mut base = place.clone();
        base.fields.clear();
        let local = base.local()?;
        let definition = self.forward.latest_value_definition_before(local, cursor)?;
        let value = &definition.value;

        // Handle field projections from as_ptr_range / as_mut_ptr_range results.
        // Field 0 is the start pointer (== arg0's address).
        // Field 1 is the end pointer (== arg0's address + len of arg0).
        if let AbstractValue::CallResult(call) = value {
            let prim = PrimitiveCall::classify(&call.func);
            if prim == Some(PrimitiveCall::AsPtrRange) || prim == Some(PrimitiveCall::AsMutPtrRange)
            {
                let arg_index = if place.fields.as_slice() == [0] {
                    0 // field 0 = start = arg0.as_ptr()
                } else if place.fields.as_slice() == [1] {
                    0 // field 1 = end = arg0.as_ptr() + len (use base arg0 term)
                } else {
                    return None;
                };
                let call_cursor = self.call_definition_cursor(call);
                return call
                    .args
                    .get(arg_index)
                    .and_then(|arg| self.term_for_value_at(arg, call_cursor, seen));
            }
        }

        // Search for a Cast fact that maps this field projection directly to
        // a source value.  This handles field-level reassignments where the
        // local's latest definition points to a *different* field (e.g. _2's
        // latest def is from _2.1 but we are resolving _2.0) and aggregate
        // (enum variant) fields whose inner values are only reachable through
        // the decomposed Cast facts (e.g. Option::Some(f) → field 0).
        if let Some(term) = self.resolve_field_through_casts(place, definition.ordinal, seen) {
            return Some(term);
        }

        if place.fields.as_slice() != [0] {
            // For non-field-0 projections (e.g., field 1 for `tail`), try to
            // follow a struct move to another local and resolve the field there.
            if let AbstractValue::Place(other_place) = value {
                let mut alt_place = other_place.clone();
                alt_place.fields = place.fields.clone();
                if let Some(term) = self.term_for_place_before(&alt_place, definition.ordinal, seen)
                {
                    return Some(term);
                }
            }
            return None;
        }
        let (op, lhs, rhs) = match value {
            AbstractValue::Binary(op, lhs, rhs) => (op, lhs, rhs),
            AbstractValue::Place(other_place) => {
                // Follow a struct move: return.0 -> _2.0
                let mut alt_place = other_place.clone();
                alt_place.fields = place.fields.clone();
                if let Some(term) = self.term_for_place_before(&alt_place, definition.ordinal, seen)
                {
                    return Some(term);
                }
                return None;
            }
            _ => return None,
        };
        if !matches!(
            *op,
            BinOp::AddWithOverflow | BinOp::SubWithOverflow | BinOp::MulWithOverflow
        ) {
            return None;
        }
        if matches!(op, BinOp::MulWithOverflow) {
            if let Some(len_origin) = ptr_metadata_origin(lhs, self) {
                let len_key = format!("len({len_origin})");
                let len_term = self.symbolic_len_term(&len_key);
                let rhs_term = self.term_for_value_at(rhs, definition.ordinal, seen)?;
                return Some(Int::mul(self.ctx, &[len_term, rhs_term]));
            }
        }
        let lhs = self.term_for_value_at(lhs, definition.ordinal, seen)?;
        let rhs = self.term_for_value_at(rhs, definition.ordinal, seen)?;
        self.term_for_binary(*op, &lhs, &rhs)
    }

    /// Resolve a field projection by searching Cast facts, including
    /// progressive resolution for multi-field projections (e.g. a field-of-a-
    /// field where the intermediate is an enum-variant aggregate).
    fn resolve_field_through_casts(
        &mut self,
        place: &PlaceKey,
        cursor: ValueCursor,
        seen: &mut TraceSeen,
    ) -> Option<Int<'ctx>> {
        // 1) Direct Cast fact for the exact field projection.
        for fact in &self.forward.facts {
            if let StateFact::Cast { target, source, .. } = fact {
                if *target == *place {
                    let source = source.clone();
                    return self.term_for_value_at(&source, cursor, seen);
                }
            }
        }

        // 2) Progressive resolution: if the place has more than one field
        //    projection, try to resolve the prefix through a Cast fact, then
        //    continue with the remaining fields on the resolved source.
        if place.fields.len() > 1 {
            let mut prefix = place.clone();
            let last_field = prefix.fields.pop().unwrap_or(0);

            for fact in &self.forward.facts {
                if let StateFact::Cast { target, source, .. } = fact {
                    if *target == prefix {
                        if let AbstractValue::Place(p) = source {
                            let mut src_place = p.clone();
                            src_place.fields.push(last_field);
                            return self.term_for_place_before(&src_place, cursor, seen);
                        }
                        // If the source is a CallResult or other concrete value,
                        // try to resolve through the value itself first, and
                        // then project the last field.
                        let source = source.clone();
                        if let Some(term) = self.term_for_value_at(&source, cursor, seen) {
                            return Some(term);
                        }
                        break;
                    }
                }
            }
        }

        None
    }

    /// Build an SMT term for an abstract value.
    fn term_for_value(
        &mut self,
        value: &AbstractValue<'tcx>,
        seen: &mut TraceSeen,
    ) -> Option<Int<'ctx>> {
        self.term_for_value_at(value, self.latest_cursor(), seen)
    }

    /// Build an address expression for a call summarized as pointer arithmetic.
    fn term_for_pointer_arith_call(
        &mut self,
        call: &CallSummary<'tcx>,
        cursor: ValueCursor,
        seen: &mut TraceSeen,
    ) -> Option<Int<'ctx>> {
        let effect = call.effects.iter().find_map(|effect| match effect {
            crate::verify::call_summary::CallEffect::ReturnPointerAdd {
                base_arg,
                offset_arg,
                stride,
            } => Some((false, *base_arg, *offset_arg, *stride)),
            crate::verify::call_summary::CallEffect::ReturnPointerSub {
                base_arg,
                offset_arg,
                stride,
            } => Some((true, *base_arg, *offset_arg, *stride)),
            _ => None,
        });

        let (is_sub, base_arg, offset_arg, stride) = effect.or_else(|| {
            if is_pointer_add_call(&call.func) {
                Some((false, 0, 1, self.call_destination_stride(call)))
            } else if is_pointer_sub_call(&call.func) {
                Some((true, 0, 1, self.call_destination_stride(call)))
            } else {
                None
            }
        })?;

        let base = call.args.get(base_arg)?;
        let offset = call.args.get(offset_arg)?;
        let base = self.term_for_value_at(base, cursor, seen)?;
        let offset = self.term_for_value_at(offset, cursor, seen)?;
        let stride = Int::from_u64(self.ctx, stride.unwrap_or(1));
        let scaled_offset = Int::mul(self.ctx, &[offset, stride]);

        if is_sub {
            Some(Int::sub(self.ctx, &[base, scaled_offset]))
        } else {
            Some(Int::add(self.ctx, &[base, scaled_offset]))
        }
    }

    /// Build a stable `len(origin)` term for calls summarized as length reads.
    fn term_for_length_call(
        &mut self,
        call: &CallSummary<'tcx>,
        cursor: ValueCursor,
        seen: &mut TraceSeen,
    ) -> Option<Int<'ctx>> {
        let arg = call.effects.iter().find_map(|effect| {
            let crate::verify::call_summary::CallEffect::ReturnLengthOfArg { arg } = effect else {
                return None;
            };
            Some(*arg)
        })?;
        let source = call.args.get(arg)?;
        let source = self
            .origin_key_for_value_before(source, cursor, seen)
            .unwrap_or_else(|| value_label(source));
        let len_key = format!("len({source})");
        Some(self.symbolic_len_term(&len_key))
    }

    /// Return a cached Z3 integer symbol for a const generic parameter,
    /// keyed by its plain name (e.g. `N`).  Accepts either a plain name or a
    /// rustc debug string such as `Ty(usize, N/#1)` / `Param(N)`, so that a
    /// const parameter referenced from a MIR operand, a contract, and an array
    /// length all resolve to the same `const_<name>` symbol.
    fn const_param_symbol(&mut self, name_or_debug: &str) -> Int<'ctx> {
        let plain =
            const_param_name_from_debug(name_or_debug).unwrap_or_else(|| name_or_debug.to_string());
        let key = format!("const_{}", sanitize_smt_name(&plain));
        if let Some(term) = self.const_terms.get(&key) {
            return term.clone();
        }
        let term = Int::new_const(self.ctx, key.as_str());
        self.const_terms.insert(key, term.clone());
        term
    }

    /// Build an SMT term for an abstract value at a program point.
    fn term_for_value_at(
        &mut self,
        value: &AbstractValue<'tcx>,
        cursor: ValueCursor,
        seen: &mut TraceSeen,
    ) -> Option<Int<'ctx>> {
        match value {
            AbstractValue::ConstInt(value) => Some(Int::from_u64(self.ctx, *value as u64)),
            AbstractValue::ConstParam(name) => Some(self.const_param_symbol(name)),
            AbstractValue::Const(text) => {
                const_int_from_debug(text)
                    .map(|value| Int::from_u64(self.ctx, value as u64))
                    .or_else(|| {
                        // A constant operand may be a const generic parameter
                        // (e.g. debug `Ty(usize, N/#1)`).  Normalize its symbol
                        // to `const_<name>` so it unifies with the same const
                        // parameter referenced elsewhere (contracts, array
                        // lengths) instead of minting `const_Ty_usize__N__1_`.
                        if let Some(param) = const_param_name_from_debug(text) {
                            return Some(self.const_param_symbol(&param));
                        }
                        let name = sanitize_smt_name(text);
                        if name.is_empty() {
                            None
                        } else {
                            Some(Int::new_const(self.ctx, format!("const_{name}")))
                        }
                    })
            }
            AbstractValue::Place(place) => self.term_for_place_before(place, cursor, seen),
            AbstractValue::Cast(inner, _) => self.term_for_value_at(inner, cursor, seen),
            AbstractValue::Ref(place) | AbstractValue::RawPtr(place) => Some(Int::new_const(
                self.ctx,
                format!("addr_{}", place_name(place)),
            )),
            AbstractValue::Binary(op, lhs, rhs) => {
                let lhs = self.term_for_value_at(lhs, cursor, seen)?;
                let rhs = self.term_for_value_at(rhs, cursor, seen)?;
                self.term_for_binary(*op, &lhs, &rhs)
            }
            AbstractValue::CallResult(call) => {
                if let Some(term) = self.term_for_pointer_arith_call(call, cursor, seen) {
                    return Some(term);
                }
                if let Some(term) = self.term_for_length_call(call, cursor, seen) {
                    return Some(term);
                }
                if let Some(term) = self.term_for_numeric_arith_call(call, cursor, seen) {
                    return Some(term);
                }
                if is_as_ptr_call(&call.func) {
                    if let Some(source_arg) = call.effects.iter().find_map(|effect| match effect {
                        crate::verify::call_summary::CallEffect::ReturnPointerFromArg { arg }
                        | crate::verify::call_summary::CallEffect::ReturnAliasArg { arg } => {
                            Some(*arg)
                        }
                        _ => None,
                    }) {
                        let call_cursor = self.call_definition_cursor(call);
                        return self.term_for_value_at(
                            call.args.get(source_arg)?,
                            call_cursor,
                            seen,
                        );
                    }
                }
                // `Option/Result::expect/unwrap` yields the wrapped payload; the
                // error case diverges before any later checkpoint, so the value
                // is the inner term of the receiver on all reachable paths.
                if PrimitiveCall::classify(&call.func) == Some(PrimitiveCall::OptionUnwrap)
                    && let Some(inner) = call.args.first()
                {
                    return self.term_for_value_at(inner, cursor, seen);
                }
                let place = PlaceKey {
                    base: PlaceBaseKey::Local(call.destination.as_usize()),
                    fields: Vec::new(),
                };
                Some(Int::new_const(self.ctx, place_name(&place)))
            }
            AbstractValue::Unknown(_)
            | AbstractValue::ThreadLocal(_)
            | AbstractValue::Repeat(_)
            | AbstractValue::Nullary(_)
            | AbstractValue::Discriminant(_)
            | AbstractValue::Aggregate(_, _) => None,
            AbstractValue::Unary(op, inner) => match op {
                UnOp::PtrMetadata => {
                    let source = self
                        .origin_key_for_value_before(inner, cursor, seen)
                        .unwrap_or_else(|| value_label(inner));
                    let len_key = format!("len({source})");
                    Some(self.symbolic_len_term(&len_key))
                }
                _ => None,
            },
            #[cfg(not(rapx_rustc_ge_196))]
            AbstractValue::ShallowInitBox(_, _) => {
                let name = sanitize_smt_name(&value_label(value));
                if name.is_empty() {
                    None
                } else {
                    Some(Int::new_const(self.ctx, name))
                }
            }
        }
    }

    /// Build an SMT integer term from a property-independent diagnostic term.
    fn term_for_smt_term(&mut self, term: &SmtTerm) -> Option<Int<'ctx>> {
        match term {
            SmtTerm::Place(place) => self.term_for_place(place),
            SmtTerm::Value(name) => {
                if name.starts_with("len(") {
                    Some(self.symbolic_len_term(name))
                } else {
                    Some(Int::new_const(self.ctx, sanitize_smt_name(name)))
                }
            }
            SmtTerm::Const(value) => Some(Int::from_u64(self.ctx, *value)),
            SmtTerm::ConstParam(text) => {
                if sanitize_smt_name(text).is_empty() {
                    return None;
                }
                Some(self.const_param_symbol(text))
            }
            SmtTerm::Add(lhs, rhs) => {
                let lhs = self.term_for_smt_term(lhs)?;
                let rhs = self.term_for_smt_term(rhs)?;
                Some(Int::add(self.ctx, &[lhs, rhs]))
            }
            SmtTerm::Sub(lhs, rhs) => {
                let lhs = self.term_for_smt_term(lhs)?;
                let rhs = self.term_for_smt_term(rhs)?;
                Some(Int::sub(self.ctx, &[lhs, rhs]))
            }
            SmtTerm::Mul(lhs, rhs) => {
                let lhs = self.term_for_smt_term(lhs)?;
                let rhs = self.term_for_smt_term(rhs)?;
                Some(Int::mul(self.ctx, &[lhs, rhs]))
            }
            SmtTerm::Div(lhs, rhs) => {
                let lhs = self.term_for_smt_term(lhs)?;
                let rhs = self.term_for_smt_term(rhs)?;
                Some(lhs.div(&rhs))
            }
            SmtTerm::Rem(lhs, rhs) => {
                let lhs = self.term_for_smt_term(lhs)?;
                let rhs = self.term_for_smt_term(rhs)?;
                Some(lhs.modulo(&rhs))
            }
        }
    }

    /// Build a boolean term for a conjunction of shared predicates.
    fn bool_for_predicates(&mut self, predicates: &[SmtPredicate]) -> Option<Bool<'ctx>> {
        match predicates {
            [] => None,
            [predicate] => self.bool_for_predicate(predicate),
            predicates => {
                let bools = predicates
                    .iter()
                    .map(|predicate| self.bool_for_predicate(predicate))
                    .collect::<Option<Vec<_>>>()?;
                let refs = bools.iter().collect::<Vec<_>>();
                Some(Bool::and(self.ctx, &refs))
            }
        }
    }

    /// Build a boolean term from a shared diagnostic/query predicate.
    fn bool_for_predicate(&mut self, predicate: &SmtPredicate) -> Option<Bool<'ctx>> {
        match predicate {
            SmtPredicate::Eq(lhs, rhs) => {
                let lhs = self.term_for_smt_term(lhs)?;
                let rhs = self.term_for_smt_term(rhs)?;
                Some(lhs._eq(&rhs))
            }
            SmtPredicate::Ne(lhs, rhs) => {
                let lhs = self.term_for_smt_term(lhs)?;
                let rhs = self.term_for_smt_term(rhs)?;
                Some(lhs._eq(&rhs).not())
            }
            SmtPredicate::Le(lhs, rhs) => {
                let lhs = self.term_for_smt_term(lhs)?;
                let rhs = self.term_for_smt_term(rhs)?;
                Some(lhs.le(&rhs))
            }
            SmtPredicate::Lt(lhs, rhs) => {
                let lhs = self.term_for_smt_term(lhs)?;
                let rhs = self.term_for_smt_term(rhs)?;
                Some(lhs.lt(&rhs))
            }
            SmtPredicate::Ge(lhs, rhs) => {
                let lhs = self.term_for_smt_term(lhs)?;
                let rhs = self.term_for_smt_term(rhs)?;
                Some(lhs.ge(&rhs))
            }
            SmtPredicate::Gt(lhs, rhs) => {
                let lhs = self.term_for_smt_term(lhs)?;
                let rhs = self.term_for_smt_term(rhs)?;
                Some(lhs.gt(&rhs))
            }
            SmtPredicate::And(predicates) => self.bool_for_predicates(predicates),
            SmtPredicate::Divisible { term, modulus } => {
                let term = self.term_for_smt_term(term)?;
                let modulus = Int::from_u64(self.ctx, *modulus);
                let zero = Int::from_u64(self.ctx, 0);
                Some(term.modulo(&modulus)._eq(&zero))
            }
            SmtPredicate::InBounds {
                index,
                access_count,
                len,
            } => {
                let index = self.term_for_smt_term(index)?;
                let access_count = self.term_for_smt_term(access_count)?;
                let len = self.term_for_smt_term(len)?;
                let zero = Int::from_u64(self.ctx, 0);
                let covered_end = Int::add(self.ctx, &[index.clone(), access_count]);
                Some(Bool::and(
                    self.ctx,
                    &[&index.ge(&zero), &covered_end.le(&len)],
                ))
            }
            SmtPredicate::NonOverlapping {
                left,
                right,
                left_count,
                right_count,
                elem_size,
            } => {
                let left = self.term_for_smt_term(left)?;
                let right = self.term_for_smt_term(right)?;
                let left_count = self.term_for_smt_term(left_count)?;
                let right_count = self.term_for_smt_term(right_count)?;
                let elem_size = Int::from_u64(self.ctx, *elem_size);
                let left_end = Int::add(
                    self.ctx,
                    &[
                        left.clone(),
                        Int::mul(self.ctx, &[left_count, elem_size.clone()]),
                    ],
                );
                let right_end = Int::add(
                    self.ctx,
                    &[right.clone(), Int::mul(self.ctx, &[right_count, elem_size])],
                );
                Some(Bool::or(
                    self.ctx,
                    &[&left_end.le(&right), &right_end.le(&left)],
                ))
            }
            SmtPredicate::Not(predicate) => Some(self.bool_for_predicate(predicate)?.not()),
            SmtPredicate::Custom(_) => None,
        }
    }

    /// Assert Rust unsigned integer lower bounds for terms that appear in a
    /// numeric obligation.
    fn assert_unsigned_bounds_for_predicates(
        &mut self,
        solver: &Solver<'ctx>,
        predicates: &[SmtPredicate],
    ) {
        let mut seen = HashSet::new();
        for predicate in predicates {
            self.assert_unsigned_bounds_for_predicate(solver, predicate, &mut seen);
        }
    }

    fn assert_unsigned_bounds_for_predicate(
        &mut self,
        solver: &Solver<'ctx>,
        predicate: &SmtPredicate,
        seen: &mut HashSet<PlaceKey>,
    ) {
        match predicate {
            SmtPredicate::Eq(lhs, rhs)
            | SmtPredicate::Ne(lhs, rhs)
            | SmtPredicate::Le(lhs, rhs)
            | SmtPredicate::Lt(lhs, rhs)
            | SmtPredicate::Ge(lhs, rhs)
            | SmtPredicate::Gt(lhs, rhs) => {
                self.assert_unsigned_bounds_for_term(solver, lhs, seen);
                self.assert_unsigned_bounds_for_term(solver, rhs, seen);
            }
            SmtPredicate::And(predicates) => {
                for predicate in predicates {
                    self.assert_unsigned_bounds_for_predicate(solver, predicate, seen);
                }
            }
            SmtPredicate::Divisible { term, .. } => {
                self.assert_unsigned_bounds_for_term(solver, term, seen);
            }
            SmtPredicate::InBounds {
                index,
                access_count,
                len,
            } => {
                self.assert_unsigned_bounds_for_term(solver, index, seen);
                self.assert_unsigned_bounds_for_term(solver, access_count, seen);
                self.assert_unsigned_bounds_for_term(solver, len, seen);
            }
            SmtPredicate::NonOverlapping {
                left_count,
                right_count,
                ..
            } => {
                self.assert_unsigned_bounds_for_term(solver, left_count, seen);
                self.assert_unsigned_bounds_for_term(solver, right_count, seen);
            }
            SmtPredicate::Not(predicate) => {
                self.assert_unsigned_bounds_for_predicate(solver, predicate, seen);
            }
            SmtPredicate::Custom(_) => {}
        }
    }

    fn assert_unsigned_bounds_for_term(
        &mut self,
        solver: &Solver<'ctx>,
        term: &SmtTerm,
        seen: &mut HashSet<PlaceKey>,
    ) {
        match term {
            SmtTerm::Place(place) => {
                if !seen.insert(place.clone()) {
                    return;
                }
                let Some(ty) = self.place_ty(place) else {
                    return;
                };
                if !is_unsigned_integral_ty(ty) {
                    return;
                }
                let Some(int_term) = self.term_for_place(place) else {
                    return;
                };
                let zero = Int::from_u64(self.ctx, 0);
                solver.assert(&int_term.ge(&zero));
                self.assumptions.push(SmtPredicate::Ge(
                    SmtTerm::Place(place.clone()),
                    SmtTerm::Const(0),
                ));
            }
            SmtTerm::Add(lhs, rhs)
            | SmtTerm::Sub(lhs, rhs)
            | SmtTerm::Mul(lhs, rhs)
            | SmtTerm::Div(lhs, rhs)
            | SmtTerm::Rem(lhs, rhs) => {
                self.assert_unsigned_bounds_for_term(solver, lhs, seen);
                self.assert_unsigned_bounds_for_term(solver, rhs, seen);
            }
            SmtTerm::Value(name) if name.starts_with("len(") => {
                // Slice/array lengths are unsigned metadata: always >= 0.
                // Without this, `len(x) != 0` (from a `size == 0` guard) does
                // not imply `len(x) >= 1` in z3's unbounded integers, so a
                // zero-iteration `base < len` bound stays unprovable.
                let term = self.symbolic_len_term(name);
                let zero = Int::from_u64(self.ctx, 0);
                solver.assert(&term.ge(&zero));
                self.assumptions.push(SmtPredicate::Ge(
                    SmtTerm::Value(name.clone()),
                    SmtTerm::Const(0),
                ));
            }
            SmtTerm::Value(_) | SmtTerm::Const(_) | SmtTerm::ConstParam(_) => {}
        }
    }

    /// Build an SMT term for a pure numeric-arithmetic intrinsic result
    /// (`unchecked_mul`/`unchecked_add`/...), reconstructing the exact value
    /// from its operands so downstream range checks can relate it back to the
    /// source quantities (e.g. `self.len() * N` in `[[T; N]]::as_flattened`).
    fn term_for_numeric_arith_call(
        &mut self,
        call: &CallSummary<'tcx>,
        cursor: ValueCursor,
        seen: &mut TraceSeen,
    ) -> Option<Int<'ctx>> {
        if PrimitiveCall::classify(&call.func) != Some(PrimitiveCall::NumericArith) {
            return None;
        }
        let lhs = self.term_for_value_at(call.args.first()?, cursor, seen)?;
        let rhs = self.term_for_value_at(call.args.get(1)?, cursor, seen)?;
        let func = &call.func;
        let term = if func.contains("unchecked_mul") {
            Int::mul(self.ctx, &[lhs, rhs])
        } else if func.contains("unchecked_add") {
            Int::add(self.ctx, &[lhs, rhs])
        } else if func.contains("unchecked_sub") {
            Int::sub(self.ctx, &[lhs, rhs])
        } else if func.contains("unchecked_div") || func.contains("exact_div") {
            lhs.div(&rhs)
        } else if func.contains("unchecked_rem") {
            lhs.modulo(&rhs)
        } else if func.contains("checked_mul") {
            Int::mul(self.ctx, &[lhs, rhs])
        } else if func.contains("checked_add") {
            Int::add(self.ctx, &[lhs, rhs])
        } else if func.contains("checked_sub") {
            Int::sub(self.ctx, &[lhs, rhs])
        } else {
            return None;
        };
        Some(term)
    }

    /// Lower a binary MIR operation to an integer term.
    fn term_for_binary(&self, op: BinOp, lhs: &Int<'ctx>, rhs: &Int<'ctx>) -> Option<Int<'ctx>> {
        let one = Int::from_u64(self.ctx, 1);
        let zero = Int::from_u64(self.ctx, 0);
        Some(match op {
            BinOp::Add | BinOp::AddWithOverflow | BinOp::AddUnchecked => {
                Int::add(self.ctx, &[lhs.clone(), rhs.clone()])
            }
            BinOp::Sub | BinOp::SubWithOverflow | BinOp::SubUnchecked => {
                Int::sub(self.ctx, &[lhs.clone(), rhs.clone()])
            }
            BinOp::Mul | BinOp::MulWithOverflow | BinOp::MulUnchecked => {
                Int::mul(self.ctx, &[lhs.clone(), rhs.clone()])
            }
            BinOp::Div => lhs.div(rhs),
            BinOp::Rem => lhs.modulo(rhs),
            BinOp::Eq => lhs._eq(rhs).ite(&one, &zero),
            BinOp::Ne => lhs._eq(rhs).not().ite(&one, &zero),
            BinOp::Lt => lhs.lt(rhs).ite(&one, &zero),
            BinOp::Le => lhs.le(rhs).ite(&one, &zero),
            BinOp::Gt => lhs.gt(rhs).ite(&one, &zero),
            BinOp::Ge => lhs.ge(rhs).ite(&one, &zero),
            _ => return None,
        })
    }

    /// Return the byte stride for a typed pointer-add call destination.
    fn call_destination_stride(&self, call: &CallSummary<'tcx>) -> Option<u64> {
        let place = PlaceKey {
            base: PlaceBaseKey::Local(call.destination.as_usize()),
            fields: Vec::new(),
        };
        let destination_ty = self.place_ty(&place)?;
        let pointee = pointee_ty(destination_ty)?;
        self.type_layout(pointee).map(|(_, size)| size)
    }

    /// Return the MIR type for a simple place key.
    fn place_ty(&self, place: &PlaceKey) -> Option<Ty<'tcx>> {
        if !place.fields.is_empty() {
            return self.forward.facts.iter().find_map(|fact| {
                let StateFact::Cast { target, ty, .. } = fact else {
                    return None;
                };
                if target == place { Some(*ty) } else { None }
            });
        }
        let local = match place.base {
            PlaceBaseKey::Return => Local::from_usize(0),
            PlaceBaseKey::Local(local) => Local::from_usize(local),
            PlaceBaseKey::Arg(_) => return None,
        };
        Some(self.tcx.optimized_mir(self.checkpoint.caller).local_decls[local].ty)
    }

    fn type_layout(&self, ty: Ty<'tcx>) -> Option<(u64, u64)> {
        safe_type_layout(self.tcx, self.checkpoint.caller, ty)
    }

    /// Return the alignment guaranteed by a concrete or generic type.
    fn guaranteed_alignment(&self, ty: Ty<'tcx>) -> Option<u64> {
        if let Some((align, _)) = self.type_layout(ty).filter(|(align, _)| *align > 0) {
            return Some(align);
        }
        if let Some(alignments) = self.generic_candidate_alignments(ty) {
            return alignments.into_iter().min();
        }
        if matches!(
            ty.kind(),
            TyKind::Param(_) | TyKind::Array(..) | TyKind::Ref(..) | TyKind::RawPtr(..)
        ) {
            return Some(0);
        }
        None
    }

    fn generic_candidate_alignments(&self, ty: Ty<'tcx>) -> Option<Vec<u64>> {
        let candidates = GenericTypeCandidates::for_def(self.tcx, self.checkpoint.caller);
        let alignments = candidates
            .candidates_for_ty(ty)?
            .iter()
            .filter_map(|candidate| self.type_layout(*candidate).map(|(align, _)| align))
            .filter(|align| *align > 0)
            .collect::<Vec<_>>();
        if alignments.is_empty() {
            None
        } else {
            Some(alignments)
        }
    }

    /// Return the pointer-add call/effect that produced a place after copies/casts.
    fn pointer_add_call_for_place(&self, place: &PlaceKey) -> Option<CallSummary<'tcx>> {
        let value = self.resolved_value_for_place_before(
            place,
            self.latest_cursor(),
            &mut TraceSeen::new(),
        )?;
        match value {
            AbstractValue::CallResult(call)
                if call_has_pointer_add_effect(&call) || call_has_pointer_sub_effect(&call) =>
            {
                Some(call)
            }
            _ => None,
        }
    }

    /// True when `place` is a pointer whose provenance is a reference-derived
    /// `as_ptr`/`as_mut_ptr` result over a pointee type that matches `ty_name`.
    ///
    /// Pointers returned by `as_ptr`/`as_mut_ptr` are guaranteed to be aligned
    /// to their element type (the referent of a live reference is always
    /// well-aligned).  That is exactly the alignment such pointers are required
    /// to satisfy when handed to element-typed unsafe callees such as
    /// `ptr::copy_nonoverlapping`, so the `Align` obligation holds without any
    /// further path facts.  We require the pointee type to match the requested
    /// alignment type to avoid proving alignment for reinterpreting casts (e.g.
    /// a `*const u8` view of a `*const u32`).
    fn place_is_reference_aligned(&self, place: &PlaceKey, ty_name: &str) -> bool {
        let Some(value) = self.resolved_value_for_place(place, &mut TraceSeen::new()) else {
            return false;
        };
        self.value_is_reference_aligned(&value, ty_name, 0)
    }

    /// See [`place_is_reference_aligned`]; follows element-stride pointer
    /// arithmetic back to an `as_ptr`/`as_mut_ptr` base, since `p.add(k)` keeps
    /// the alignment of `p` for element strides.
    fn value_is_reference_aligned(
        &self,
        value: &AbstractValue<'tcx>,
        ty_name: &str,
        depth: usize,
    ) -> bool {
        if depth > 8 {
            return false;
        }
        let AbstractValue::CallResult(call) = value else {
            return false;
        };
        if is_as_ptr_call(&call.func) {
            let dest = PlaceKey {
                base: PlaceBaseKey::Local(call.destination.as_usize()),
                fields: Vec::new(),
            };
            let got = self
                .place_ty(&dest)
                .and_then(pointee_ty_str)
                .map(|s| normalize_init_ty_name(&s));
            return got.as_deref() == Some(normalize_init_ty_name(ty_name).as_str());
        }
        if PrimitiveCall::classify(&call.func)
            .is_some_and(PrimitiveCall::is_element_pointer_arithmetic)
        {
            // The offset must be measured in `ty_name`-sized elements for the
            // result to keep `ty_name` alignment.  A pointer of a different
            // pointee (e.g. `*const u8`) advanced by its own stride can land on
            // an address that is not `ty_name`-aligned, so reject those.
            let dest = PlaceKey {
                base: PlaceBaseKey::Local(call.destination.as_usize()),
                fields: Vec::new(),
            };
            let dest_pointee = self
                .place_ty(&dest)
                .and_then(pointee_ty_str)
                .map(|s| normalize_init_ty_name(&s));
            if dest_pointee.as_deref() != Some(normalize_init_ty_name(ty_name).as_str()) {
                return false;
            }
            if let Some(base) = call.args.first()
                && let Some(base_value) =
                    self.resolved_value_before(base, self.latest_cursor(), &mut TraceSeen::new())
            {
                return self.value_is_reference_aligned(&base_value, ty_name, depth + 1);
            }
        }
        false
    }

    /// Resolve copy/cast chains for a MIR place into the value at their source.
    fn resolved_value_for_place(
        &self,
        place: &PlaceKey,
        seen: &mut TraceSeen,
    ) -> Option<AbstractValue<'tcx>> {
        self.resolved_value_for_place_before(place, self.latest_cursor(), seen)
    }

    fn resolved_value_for_place_before(
        &self,
        place: &PlaceKey,
        cursor: ValueCursor,
        seen: &mut TraceSeen,
    ) -> Option<AbstractValue<'tcx>> {
        let seen_key = (place.clone(), cursor);
        if !seen.insert(seen_key) {
            return None;
        }
        if !place.fields.is_empty() {
            let mut base = place.clone();
            base.fields.clear();
            let local = base.local()?;
            if let Some(definition) = self.forward.latest_value_definition_before(local, cursor) {
                // Handle as_ptr_range / as_mut_ptr_range (call result)
                if let AbstractValue::CallResult(call) = &definition.value {
                    let prim = PrimitiveCall::classify(&call.func);
                    if prim == Some(PrimitiveCall::AsPtrRange)
                        || prim == Some(PrimitiveCall::AsMutPtrRange)
                    {
                        if let Some(source_arg) =
                            call.effects.iter().find_map(|effect| match effect {
                                crate::verify::call_summary::CallEffect::ReturnAliasArg { arg }
                                | crate::verify::call_summary::CallEffect::ReturnPointerFromArg {
                                    arg,
                                } => Some(*arg),
                                _ => None,
                            })
                        {
                            let call_cursor = self.call_definition_cursor(call);
                            if let Some(arg_value) = call.args.get(source_arg) {
                                return self.resolved_value_before(arg_value, call_cursor, seen);
                            }
                        }
                    }
                }
                // Handle inlined as_ptr_range (aggregate of as_ptr + add results)
                // Find Cast facts that connect field places to their source values
                if let AbstractValue::Aggregate(_, _) = &definition.value {
                    for fact in &self.forward.facts {
                        if let StateFact::Cast { target, source, .. } = fact {
                            if *target == *place {
                                return self.resolved_value_before(
                                    source,
                                    definition.ordinal,
                                    seen,
                                );
                            }
                        }
                    }
                }
            }
            return Some(AbstractValue::Place(place.clone()));
        }
        let local = place.local()?;
        if let Some(definition) = self.forward.latest_value_definition_before(local, cursor) {
            return self.resolved_value_before(&definition.value, definition.ordinal, seen);
        }
        if let Some(value) = self.path_value_definition_before(place, cursor) {
            return self.resolved_value_before(&value, cursor, seen);
        }
        None
    }

    /// Resolve copy/cast chains for an abstract value.
    fn resolved_value(
        &self,
        value: &AbstractValue<'tcx>,
        seen: &mut TraceSeen,
    ) -> Option<AbstractValue<'tcx>> {
        self.resolved_value_before(value, self.latest_cursor(), seen)
    }

    fn resolved_value_before(
        &self,
        value: &AbstractValue<'tcx>,
        cursor: ValueCursor,
        seen: &mut TraceSeen,
    ) -> Option<AbstractValue<'tcx>> {
        match value {
            AbstractValue::Place(place) => {
                self.resolved_value_for_place_before(place, cursor, seen)
            }
            AbstractValue::Cast(inner, _) => self.resolved_value_before(inner, cursor, seen),
            _ => Some(value.clone()),
        }
    }

    /// Recover a local definition directly from the expanded MIR path.
    ///
    /// Backward relevance keeps the proof slice intentionally small. When a
    /// pure call-argument temporary is not retained in the forward visit, SMT
    /// term construction can still recover its value by replaying assignments
    /// along the already-enumerated path up to the current cursor.
    fn path_value_definition_before(
        &self,
        place: &PlaceKey,
        cursor: ValueCursor,
    ) -> Option<AbstractValue<'tcx>> {
        if !place.fields.is_empty() {
            return None;
        }
        let local = place.local()?;
        let cutoff = self.path_cursor_cutoff(cursor);
        let body = self.tcx.optimized_mir(self.forward.checkpoint.caller);
        let mut latest = None;

        for step in &self.forward.path.steps {
            let PathStep::Block(block) = step else {
                continue;
            };
            let is_cutoff_block = *block == cutoff.block;
            let block_data = &body.basic_blocks[*block];

            for (statement_index, statement) in block_data.statements.iter().enumerate() {
                if is_cutoff_block
                    && let Some(cutoff_statement) = cutoff.statement_index
                    && statement_index >= cutoff_statement
                {
                    return latest;
                }

                let rustc_middle::mir::StatementKind::Assign(assign) = &statement.kind else {
                    continue;
                };
                let (target, rvalue) = &**assign;
                if target.local == local {
                    latest = abstract_value_from_rvalue(rvalue);
                }
            }

            if is_cutoff_block {
                return latest;
            }
        }

        latest
    }

    fn path_cursor_cutoff(&self, cursor: ValueCursor) -> PathCursorCutoff {
        if let Some(definition) = self.forward.value_definitions.get(cursor) {
            return PathCursorCutoff {
                block: definition.block,
                statement_index: definition.statement_index,
            };
        }

        PathCursorCutoff {
            block: self.forward.checkpoint.block,
            statement_index: None,
        }
    }

    /// Return a stable origin key for matching `as_ptr(source)` and `len(source)`.
    fn origin_key_for_value(
        &self,
        value: &AbstractValue<'tcx>,
        seen: &mut TraceSeen,
    ) -> Option<String> {
        self.origin_key_for_value_before(value, self.latest_cursor(), seen)
    }

    /// True when `place` is the pointer of a `from_raw_parts` reinterpret whose
    /// element count is an `align_to_offsets` output field and whose provenance
    /// is the same slice that fed `align_to_offsets`.  `align_to_offsets` is a
    /// trusted structural summary whose returned counts keep both reinterprets
    /// within the source allocation, so the range is allocated / in bounds.
    fn allocated_by_align_to_offsets(
        &self,
        checkpoint: &Checkpoint<'tcx>,
        place: &PlaceKey,
    ) -> bool {
        let caller = checkpoint.caller;
        if !self.tcx.is_mir_available(caller) {
            return false;
        }
        let Some(place_origin) =
            self.origin_key_for_value(&AbstractValue::Place(place.clone()), &mut TraceSeen::new())
        else {
            return false;
        };
        let body = self.tcx.optimized_mir(caller);
        let count_root = checkpoint
            .args
            .get(1)
            .and_then(operand_place)
            .and_then(|p| p.local())
            .map(|l| mir_copy_root(&body, Local::from_usize(l.as_usize())));

        for fact in &self.forward.facts {
            let StateFact::Call(call) = fact else {
                continue;
            };
            if !call.effects.iter().any(|e| {
                matches!(
                    e,
                    crate::verify::call_summary::CallEffect::ReturnLcmSplit { .. }
                )
            }) {
                continue;
            }
            let Some(recv) = call.args.first() else {
                continue;
            };
            let recv_origin = self.origin_key_for_value(recv, &mut TraceSeen::new());
            if recv_origin.as_deref() != Some(place_origin.as_str()) {
                continue;
            }
            // The count must be an output field (us_len / ts_len) of this call.
            if let Some(root) = count_root
                && mir_is_tuple_field_of(&body, root, call.destination)
            {
                return true;
            }
        }
        false
    }

    fn origin_key_for_value_before(
        &self,
        value: &AbstractValue<'tcx>,
        cursor: ValueCursor,
        seen: &mut TraceSeen,
    ) -> Option<String> {
        let resolved = self
            .resolved_value_before(value, cursor, seen)
            .unwrap_or_else(|| value.clone());
        match resolved {
            AbstractValue::Ref(place) | AbstractValue::RawPtr(place) => Some(place_label(&place)),
            AbstractValue::Place(place) => self
                .source_from_points_to(&place)
                .map(|source| place_label(&source))
                .or_else(|| {
                    // Follow PointsTo(pointer→source) recursively to find
                    // the ultimate origin (e.g. _5 → _6 → _1).
                    self.forward.facts.iter().find_map(|fact| match fact {
                        StateFact::PointsTo { pointer, source } if *pointer == place => self
                            .origin_key_for_value_before(
                                &AbstractValue::Place(source.clone()),
                                cursor,
                                seen,
                            ),
                        _ => None,
                    })
                })
                .or_else(|| Some(place_label(&place))),
            AbstractValue::Cast(inner, _) => self.origin_key_for_value_before(&inner, cursor, seen),
            #[cfg(not(rapx_rustc_ge_196))]
            AbstractValue::ShallowInitBox(_, _) => {
                // ShallowInitBox (Box::new) is a heap allocation.  When reached
                // via PointsTo tracing from a pointer (e.g. Box::into_raw),
                // use the original `value`'s place key as the origin so that
                // Phase 1 Allocated check can find the matching KnownAllocated
                // fact by place label.
                if let AbstractValue::Place(p) = value {
                    return Some(place_label(p));
                }
                Some(value_label(&resolved))
            }
            AbstractValue::CallResult(call) if is_as_ptr_call(&call.func) => {
                let source_arg = call.effects.iter().find_map(|effect| match effect {
                    crate::verify::call_summary::CallEffect::ReturnPointerFromArg { arg }
                    | crate::verify::call_summary::CallEffect::ReturnAliasArg { arg } => Some(*arg),
                    _ => None,
                })?;
                let call_cursor = self.call_definition_cursor(&call);
                self.origin_key_for_value_before(call.args.get(source_arg)?, call_cursor, seen)
            }
            AbstractValue::CallResult(call) => {
                if let Some(source_arg) = call.effects.iter().find_map(|effect| match effect {
                    crate::verify::call_summary::CallEffect::ReturnPointerFromArg { arg }
                    | crate::verify::call_summary::CallEffect::ReturnAliasArg { arg } => Some(*arg),
                    crate::verify::call_summary::CallEffect::ReturnPointerAdd {
                        base_arg, ..
                    }
                    | crate::verify::call_summary::CallEffect::ReturnPointerSub {
                        base_arg, ..
                    } => Some(*base_arg),
                    _ => None,
                }) {
                    let call_cursor = self.call_definition_cursor(&call);
                    return self.origin_key_for_value_before(
                        call.args.get(source_arg)?,
                        call_cursor,
                        seen,
                    );
                }
                let destination = PlaceKey {
                    base: PlaceBaseKey::Local(call.destination.as_usize()),
                    fields: Vec::new(),
                };
                Some(place_label(&destination))
            }
            _ => Some(value_label(&resolved)),
        }
    }

    /// Recover a length value from a path guard that mentions `index`.
    fn guarded_len_for_index(
        &self,
        base_origin: &str,
        index: &AbstractValue<'tcx>,
    ) -> Option<AbstractValue<'tcx>> {
        let index = self
            .resolved_value(index, &mut HashSet::new())
            .unwrap_or_else(|| index.clone());
        for fact in &self.forward.facts {
            let StateFact::BranchEq {
                value, equals: 1, ..
            } = fact
            else {
                continue;
            };
            let predicate = self
                .resolved_value(value, &mut HashSet::new())
                .unwrap_or_else(|| value.clone());
            let AbstractValue::Binary(op, lhs, rhs) = predicate else {
                continue;
            };
            match op {
                BinOp::Lt | BinOp::Le => {
                    if self.value_mentions(&lhs, &index)
                        && self.len_matches_origin(&rhs, base_origin)
                    {
                        return Some(*rhs);
                    }
                }
                BinOp::Gt | BinOp::Ge => {
                    if self.value_mentions(&rhs, &index)
                        && self.len_matches_origin(&lhs, base_origin)
                    {
                        return Some(*lhs);
                    }
                }
                _ => {}
            }
        }
        None
    }

    /// Return true when `haystack` contains the same resolved value as `needle`.
    fn value_mentions(&self, haystack: &AbstractValue<'tcx>, needle: &AbstractValue<'tcx>) -> bool {
        self.value_mentions_inner(haystack, needle, &mut HashSet::new())
    }

    fn value_mentions_inner(
        &self,
        haystack: &AbstractValue<'tcx>,
        needle: &AbstractValue<'tcx>,
        seen: &mut HashSet<(String, String)>,
    ) -> bool {
        let haystack = self
            .resolved_value(haystack, &mut HashSet::new())
            .unwrap_or_else(|| haystack.clone());
        let needle = self
            .resolved_value(needle, &mut HashSet::new())
            .unwrap_or_else(|| needle.clone());
        let haystack_label = value_label(&haystack);
        let needle_label = value_label(&needle);
        if haystack_label == needle_label {
            return true;
        }
        if !seen.insert((haystack_label, needle_label)) {
            return false;
        }
        match haystack {
            AbstractValue::Cast(inner, _) | AbstractValue::Unary(_, inner) => {
                self.value_mentions_inner(&inner, &needle, seen)
            }
            AbstractValue::Binary(_, lhs, rhs) => {
                self.value_mentions_inner(&lhs, &needle, seen)
                    || self.value_mentions_inner(&rhs, &needle, seen)
            }
            _ => false,
        }
    }

    /// Return true when a length-like value is the metadata/len of `base_origin`.
    fn len_matches_origin(&self, len: &AbstractValue<'tcx>, base_origin: &str) -> bool {
        self.len_matches_origin_inner(len, base_origin, &mut HashSet::new())
    }

    fn len_matches_origin_inner(
        &self,
        len: &AbstractValue<'tcx>,
        base_origin: &str,
        seen: &mut HashSet<String>,
    ) -> bool {
        let label = value_label(len);
        if !seen.insert(label) {
            return false;
        }
        let resolved = self
            .resolved_value(len, &mut HashSet::new())
            .unwrap_or_else(|| len.clone());
        match resolved {
            AbstractValue::Place(place) => value_for_place(self.forward, &place)
                .is_some_and(|value| self.len_matches_origin_inner(value, base_origin, seen)),
            AbstractValue::Unary(UnOp::PtrMetadata, inner) => self
                .origin_key_for_value(&inner, &mut HashSet::new())
                .is_some_and(|origin| origin == base_origin),
            AbstractValue::CallResult(call) => call.effects.iter().any(|effect| {
                let crate::verify::call_summary::CallEffect::ReturnLengthOfArg { arg } = effect
                else {
                    return false;
                };
                call.args
                    .get(*arg)
                    .and_then(|value| self.origin_key_for_value(value, &mut HashSet::new()))
                    .is_some_and(|origin| origin == base_origin)
            }),
            _ => false,
        }
    }

    /// Return the source place recorded by a `PointsTo(pointer, source)` fact.
    fn source_from_points_to(&self, pointer: &PlaceKey) -> Option<PlaceKey> {
        self.forward
            .facts
            .iter()
            .find_map(|fact| match fact {
                StateFact::PointsTo {
                    pointer: fact_pointer,
                    source,
                } if fact_pointer == pointer => Some(source.clone()),
                _ => None,
            })
            .or_else(|| {
                if pointer.fields.is_empty() {
                    return None;
                }
                let mut base = pointer.clone();
                base.fields.clear();
                self.forward.facts.iter().find_map(|fact| match fact {
                    StateFact::PointsTo {
                        pointer: fact_pointer,
                        source,
                    } if *fact_pointer == base => Some(source.clone()),
                    _ => None,
                })
            })
    }

    /// Candidate address/value terms for an `Init` target.
    ///
    /// Pointer targets use their value term.  By-value `MaybeUninit<T>` targets
    /// may be moved into a temporary before `assume_init`; in that case the
    /// relevant initialized storage is the address of the original place.
    fn init_target_terms(&mut self, place: &PlaceKey) -> Vec<Int<'ctx>> {
        let mut terms = Vec::new();
        if let Some(term) = self.term_for_place(place) {
            terms.push(term);
        }
        if let Some(term) = self.storage_addr_for_place(place, &mut HashSet::new()) {
            if !terms.iter().any(|existing| existing == &term) {
                terms.push(term);
            }
        }
        terms
    }

    /// Candidate address/value terms for a known initialized write.
    fn init_source_terms(&mut self, place: &PlaceKey) -> Vec<Int<'ctx>> {
        let mut terms = Vec::new();
        if let Some(term) = self.term_for_place(place) {
            terms.push(term);
        }
        if let Some(source) = self.source_from_points_to(place)
            && let Some(term) = self.storage_addr_for_place(&source, &mut HashSet::new())
            && !terms.iter().any(|existing| existing == &term)
        {
            terms.push(term);
        }
        terms
    }

    /// Return the address of the storage represented by `place`.
    fn storage_addr_for_place(
        &mut self,
        place: &PlaceKey,
        seen: &mut HashSet<PlaceKey>,
    ) -> Option<Int<'ctx>> {
        if !seen.insert(place.clone()) {
            return None;
        }
        if let Some(value) = value_for_place(self.forward, place) {
            match &value {
                AbstractValue::Place(inner) => {
                    return self.storage_addr_for_place(inner, seen);
                }
                AbstractValue::Cast(inner, _) => {
                    if let AbstractValue::Place(inner_place) = inner.as_ref() {
                        return self.storage_addr_for_place(inner_place, seen);
                    }
                }
                _ => {}
            }
        }
        if let Some(source) = self.source_from_points_to(place) {
            return self.storage_addr_for_place(&source, seen);
        }
        Some(Int::new_const(
            self.ctx,
            format!("addr_{}", place_name(place)),
        ))
    }

    /// Find a retained `len(source)` call whose source matches `origin_key`.
    fn bounds_len_for_origin(
        &mut self,
        origin_key: &str,
        index: Option<&AbstractValue<'tcx>>,
    ) -> Option<(Int<'ctx>, SmtTerm)> {
        if let Some(len_place) = self.len_place_for_origin(origin_key) {
            return Some((self.term_for_place(&len_place)?, SmtTerm::Place(len_place)));
        }
        if let Some(index) = index
            && let Some(len_value) = self.guarded_len_for_index(origin_key, index)
        {
            return Some((
                self.term_for_value(&len_value, &mut HashSet::new())?,
                SmtTerm::Value(value_label(&len_value)),
            ));
        }
        let result = self
            .allocated_len_for_origin(origin_key)
            .filter(|&len| len > 0)
            .map(|len| (Int::from_u64(self.ctx, len), SmtTerm::Const(len)))
            .or_else(|| {
                // A fixed array `[E; N]` (possibly wrapped in `MaybeUninit`) has a
                // statically known element count `N`.  When `N` is a const-generic
                // parameter the concrete value is unavailable, but the symbolic
                // `ConstParam(N)` bound lets callers prove array writes `i < N`
                // (e.g. the `for i in 0..N` loop in get_disjoint_unchecked_mut).
                if let Some(param) = self.array_len_param_for_origin(origin_key) {
                    let term = self.const_param_symbol(&param);
                    return Some((term, SmtTerm::ConstParam(param)));
                }
                if self.is_maybe_uninit_origin(origin_key) {
                    let len_term = Int::from_u64(self.ctx, u64::MAX / 8);
                    Some((len_term, SmtTerm::Const(u64::MAX / 8)))
                } else if self.is_slice_pointer_origin(origin_key) {
                    let len_key = format!("len({})", origin_key);
                    let len_term = self.symbolic_len_term(&len_key);
                    Some((len_term, SmtTerm::Value(len_key)))
                } else {
                    None
                }
            });
        result
    }

    /// The const-generic length parameter of a fixed-array allocation object
    /// (optionally under references / `MaybeUninit`), if any.
    fn array_len_param_for_origin(&self, origin_key: &str) -> Option<String> {
        for fact in &self.forward.facts {
            let StateFact::KnownAllocated { object, .. } = fact else {
                continue;
            };
            if place_label(object) != origin_key {
                continue;
            }
            let local = object.local()?;
            let ty = self.place_ty(&PlaceKey {
                base: PlaceBaseKey::Local(local.as_usize()),
                fields: Vec::new(),
            })?;
            if let Some(param) = array_const_len_param(ty) {
                return Some(param);
            }
        }
        None
    }

    /// Return true if `origin_key` is the source of an `as_ptr`-like call
    /// (suggesting it is a slice / reference whose internal pointer was
    /// extracted).  For these origins a symbolic length term is safe because
    /// the length is naturally bounded by the reference type.
    fn is_slice_pointer_origin(&self, origin_key: &str) -> bool {
        self.forward.facts.iter().any(|fact| {
            let StateFact::Call(call) = fact else {
                return false;
            };
            let is_ptr_like = is_as_ptr_call(&call.func);
            let is_ptr_range = PrimitiveCall::classify(&call.func).is_some_and(|p| {
                matches!(p, PrimitiveCall::AsPtrRange | PrimitiveCall::AsMutPtrRange)
            });
            (is_ptr_like || is_ptr_range)
                && call.effects.iter().any(|effect| {
                    matches!(
                        effect,
                        crate::verify::call_summary::CallEffect::ReturnAliasArg { .. }
                            | crate::verify::call_summary::CallEffect::ReturnPointerFromArg { .. }
                    )
                })
                && call.args.iter().any(|arg| {
                    self.origin_key_for_value(arg, &mut HashSet::new())
                        .is_some_and(|key| key == origin_key)
                })
        })
    }

    /// Return true if the allocation for `origin_key` is a `MaybeUninit`
    /// wrapper (dynamic-length array).  These have `elements == 0` in
    /// KnownAllocated and should use a symbolic/sentinel length.
    fn is_maybe_uninit_origin(&self, origin_key: &str) -> bool {
        self.forward.facts.iter().any(|fact| {
            if let StateFact::KnownAllocated {
                object,
                ty_name,
                elements,
                ..
            } = fact
            {
                *elements == 0
                    && (place_label(object) == origin_key)
                    && ty_name.contains("MaybeUninit")
            } else {
                false
            }
        })
    }

    fn len_place_for_origin(&self, origin_key: &str) -> Option<PlaceKey> {
        for fact in &self.forward.facts {
            let StateFact::Call(call) = fact else {
                continue;
            };
            let Some(source_arg) = call.effects.iter().find_map(|effect| {
                let crate::verify::call_summary::CallEffect::ReturnLengthOfArg { arg } = effect
                else {
                    return None;
                };
                Some(*arg)
            }) else {
                continue;
            };
            let Some(source) = call.args.get(source_arg) else {
                continue;
            };
            let Some(key) = self.origin_key_for_value(source, &mut HashSet::new()) else {
                continue;
            };
            if key == origin_key {
                return Some(PlaceKey {
                    base: PlaceBaseKey::Local(call.destination.as_usize()),
                    fields: Vec::new(),
                });
            }
        }
        None
    }

    fn allocated_len_for_origin(&self, origin_key: &str) -> Option<u64> {
        self.forward.facts.iter().find_map(|fact| match fact {
            StateFact::KnownAllocated {
                place,
                object,
                elements,
                ty_name,
                ..
            } if place_label(object) == origin_key || place_label(place) == origin_key => {
                if *elements == 0 || (ty_name.contains("MaybeUninit") && ty_name.contains('[')) {
                    return None;
                }
                Some(*elements)
            }
            _ => None,
        })
    }

    /// When a KnownAllocated fact directly or transitively covers the target
    /// place, return the fact's type name so the caller can short-circuit
    /// the full SMT bounds proof.  The trace never crosses pointer-arithmetic
    /// results (they may point past the object base) and skips facts whose
    /// allocation object has been dropped or gone out of scope.
    fn allocated_ty_via_known_fact(
        &self,
        place: &PlaceKey,
        required_elements: &SmtTerm,
    ) -> Option<String> {
        let required = match required_elements {
            SmtTerm::Const(n) => *n,
            _ => return None,
        };
        if required == 0 {
            return None;
        }
        let mut visited: crate::compat::FxHashSet<PlaceKey> = Default::default();
        let mut queue = vec![place.clone()];
        while let Some(cur) = queue.pop() {
            if !visited.insert(cur.clone()) {
                continue;
            }
            if self.place_defined_by_pointer_arith(&cur) {
                continue;
            }
            if cur.fields.is_empty() {
                if let Some(local) = cur.local() {
                    if let Some(value) = self.forward.values.get(&local) {
                        let mut cursor = value;
                        let root = loop {
                            match cursor {
                                AbstractValue::Place(p)
                                | AbstractValue::Ref(p)
                                | AbstractValue::RawPtr(p) => break p.clone(),
                                AbstractValue::Cast(inner, _) => cursor = inner.as_ref(),
                                _ => {
                                    break PlaceKey {
                                        base: crate::verify::def_use::PlaceBaseKey::Local(0),
                                        fields: Vec::new(),
                                    };
                                }
                            }
                        };
                        if root.local().is_some() {
                            queue.push(root);
                        }
                    }
                }
            }
            for fact in &self.forward.facts {
                let StateFact::KnownAllocated {
                    place: alloc_place,
                    object,
                    elements,
                    ty_name,
                    ..
                } = fact
                else {
                    continue;
                };
                if allocation_object_invalidated(self.forward, object, alloc_place) {
                    continue;
                }
                if self.allocation_freed_by_owner_drop(object) {
                    continue;
                }
                if self.allocation_dropped_on_path(object, alloc_place) {
                    continue;
                }
                if *object == cur && *elements >= required {
                    return Some(ty_name.clone());
                }
                if *alloc_place == cur && *elements >= required {
                    return Some(ty_name.clone());
                }
            }
            for fact in &self.forward.facts {
                let StateFact::PointsTo { pointer, source } = fact else {
                    continue;
                };
                if *pointer == cur {
                    queue.push(source.clone());
                }
            }
            for fact in &self.forward.facts {
                let StateFact::Cast { target, source, .. } = fact else {
                    continue;
                };
                if *target == cur {
                    if let AbstractValue::Place(p) = source {
                        queue.push(p.clone());
                    }
                }
            }
        }
        None
    }

    /// Return true when an owning wrapper sharing the allocation's provenance
    /// root is dropped on the executed path *before* the checkpoint.  This
    /// consults the full MIR body, because the backward slicer may prune the
    /// drop (it does not define the checked pointer) even though it frees the
    /// underlying memory.
    fn allocation_dropped_on_path(&self, object: &PlaceKey, alloc_place: &PlaceKey) -> bool {
        use crate::verify::path_extractor::PathStep;
        use rustc_middle::mir::TerminatorKind;

        let caller = self.checkpoint.caller;
        let body = self.tcx.optimized_mir(caller);
        let checkpoint_block = self.forward.checkpoint.block;
        let Some(obj_local) = object.local().or_else(|| alloc_place.local()) else {
            return false;
        };
        let parents = body_value_parents(self.tcx, caller);
        let obj_root = follow_value_parents(&parents, obj_local);

        for step in &self.forward.path.steps {
            let PathStep::Block(bb) = step else {
                break;
            };
            if *bb == checkpoint_block {
                break;
            }
            let Some(data) = body.basic_blocks.get(*bb) else {
                continue;
            };
            let Some(terminator) = &data.terminator else {
                continue;
            };
            let dropped_local = match &terminator.kind {
                TerminatorKind::Drop { place, .. } => Some(place.local),
                TerminatorKind::Call { func, args, .. } => {
                    let name = crate::verify::call_summary::call_name(self.tcx, func);
                    if name.ends_with("mem::drop")
                        || name == "std::mem::drop"
                        || name.contains("drop_in_place")
                    {
                        args.first().and_then(|arg| match &arg.node {
                            Operand::Copy(place) | Operand::Move(place) => Some(place.local),
                            _ => None,
                        })
                    } else {
                        None
                    }
                }
                _ => None,
            };
            let Some(dropped_local) = dropped_local else {
                continue;
            };
            let dropped_ty = body.local_decls[dropped_local].ty;
            if !is_owning_wrapper_ty(&format!("{dropped_ty:?}")) {
                continue;
            }
            if follow_value_parents(&parents, dropped_local) == obj_root {
                return true;
            }
        }
        false
    }

    /// Return true when the place's local is the destination of a
    /// pointer-arithmetic primitive call on this path.
    fn place_defined_by_pointer_arith(&self, place: &PlaceKey) -> bool {
        let Some(local) = place.local() else {
            return false;
        };
        self.forward.facts.iter().any(|fact| {
            let StateFact::Call(call) = fact else {
                return false;
            };
            call.destination == local
                && crate::verify::primitive::PrimitiveCall::classify(&call.func)
                    .is_some_and(|p| p.is_pointer_arithmetic())
        })
    }

    /// Return true when an owning wrapper (Box/Vec/CString/...) that carries
    /// this allocation object was dropped earlier on the path, freeing the
    /// underlying memory even though the object local itself stays in scope.
    fn allocation_freed_by_owner_drop(&self, object: &PlaceKey) -> bool {
        self.forward.facts.iter().any(|fact| {
            let dropped = match fact {
                StateFact::Drop(place) => place.clone(),
                StateFact::Call(call)
                    if call.func.ends_with("mem::drop")
                        || call.func.ends_with("::drop")
                        || call.func.contains("drop_in_place") =>
                {
                    let Some(root) = call.args.first().and_then(|value| {
                        let mut inner = value;
                        loop {
                            match inner {
                                AbstractValue::Place(p)
                                | AbstractValue::Ref(p)
                                | AbstractValue::RawPtr(p) => break Some(p.clone()),
                                AbstractValue::Cast(v, _) => inner = v.as_ref(),
                                _ => break None,
                            }
                        }
                    }) else {
                        return false;
                    };
                    root
                }
                _ => return false,
            };
            let mut roots = vec![dropped.clone()];
            let mut cursor = dropped.clone();
            for _ in 0..8 {
                if !cursor.fields.is_empty() {
                    break;
                }
                let Some(local) = cursor.local() else {
                    break;
                };
                let Some(value) = self.forward.values.get(&local) else {
                    break;
                };
                let mut inner = value;
                let next = loop {
                    match inner {
                        AbstractValue::Place(p)
                        | AbstractValue::Ref(p)
                        | AbstractValue::RawPtr(p) => break Some(p.clone()),
                        AbstractValue::Cast(v, _) => inner = v.as_ref(),
                        _ => break None,
                    }
                };
                let Some(next) = next else {
                    break;
                };
                if roots.contains(&next) {
                    break;
                }
                roots.push(next.clone());
                cursor = next;
            }

            roots.iter().any(|dropped_root| {
                if dropped_root.overlaps(object) || object.overlaps(dropped_root) {
                    return true;
                }
                self.forward.facts.iter().any(|owner| {
                    matches!(owner, StateFact::KnownAllocated { place, object: owner_object, ty_name, .. }
                        if owner_object == object
                            && (place.overlaps(dropped_root) || dropped_root.overlaps(place))
                            && is_owning_wrapper_ty(ty_name))
                })
            })
        })
    }

    /// Fallback for `pointer_bounds_for_place` when origin-based tracing
    /// fails (e.g. loop-carried definitions missed by the backward slicer).
    /// Walks PointsTo links from `place` and collects the elements count
    /// from any `KnownAllocated` fact whose object is reachable.
    fn allocated_bounds_via_points_to(
        &mut self,
        place: &PlaceKey,
        _value: &AbstractValue<'tcx>,
        _origin_key: &str,
    ) -> Option<(Int<'ctx>, SmtTerm)> {
        let mut visited: crate::compat::FxHashSet<PlaceKey> = Default::default();
        let mut queue = vec![place.clone()];
        while let Some(cur) = queue.pop() {
            if !visited.insert(cur.clone()) {
                continue;
            }
            for fact in &self.forward.facts {
                let StateFact::KnownAllocated {
                    place: alloc_place,
                    object,
                    elements,
                    ..
                } = fact
                else {
                    continue;
                };
                if *object == cur || *alloc_place == cur {
                    if *elements > 0 {
                        let len_term = SmtTerm::Const(*elements);
                        let len_int = Int::from_u64(self.ctx, *elements);
                        return Some((len_int, len_term));
                    }
                }
            }
            for fact in &self.forward.facts {
                let StateFact::PointsTo { pointer, source } = fact else {
                    continue;
                };
                if *pointer == cur {
                    queue.push(source.clone());
                }
            }
            // Also follow Cast links — copies that transfer a pointer
            // value (e.g. `_17 = Copy(_8)`) which may be the only link
            // to a PointsTo-backed allocation when the backward slicer
            // does not capture the intermediate copy statement.
            for fact in &self.forward.facts {
                let StateFact::Cast { target, source, .. } = fact else {
                    continue;
                };
                if *target == cur {
                    if let AbstractValue::Place(p) = source {
                        queue.push(p.clone());
                    }
                }
            }
        }
        None
    }

    fn origin_is_initialized_for_ty(&self, origin_key: &str, required_ty_name: &str) -> bool {
        if self.forward.facts.iter().any(|fact| {
            let StateFact::KnownAllocated {
                place,
                object,
                ty_name,
                ..
            } = fact
            else {
                return false;
            };
            if place_label(object) != origin_key && place_label(place) != origin_key {
                return false;
            }
            if ty_name.contains("MaybeUninit") {
                return false;
            }
            init_type_compatible(ty_name, required_ty_name)
                || self
                    .initialized_element_ty_for_place(object)
                    .is_some_and(|elem| init_type_compatible(&elem, required_ty_name))
        }) {
            return true;
        }
        if let Some(local_index) = origin_key
            .strip_prefix('_')
            .and_then(|s| s.parse::<usize>().ok())
        {
            let local = rustc_middle::mir::Local::from_usize(local_index);
            let ty = self.tcx.optimized_mir(self.checkpoint.caller).local_decls[local].ty;
            if let Some(elem_ty_name) = initialized_element_ty_name(ty) {
                if init_type_compatible(&elem_ty_name, required_ty_name) {
                    return true;
                }
            }
        }
        false
    }

    fn initialized_element_ty_for_place(&self, place: &PlaceKey) -> Option<String> {
        let ty = self.place_ty(place)?;
        initialized_element_ty_name(ty)
    }
}

/// Recovered index and length terms for a first-cut in-bounds proof.
pub(crate) struct PointerBounds<'ctx> {
    index: Int<'ctx>,
    len: Int<'ctx>,
    index_term: SmtTerm,
    len_term: SmtTerm,
    origin_key: String,
}

/// Convert an operand into a place key when it names a MIR place.
pub(crate) fn operand_place(operand: &Operand<'_>) -> Option<PlaceKey> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => Some(PlaceKey::from_mir_place(place)),
        Operand::Constant(_) => None,
        #[cfg(rapx_rustc_ge_196)]
        Operand::RuntimeChecks(_) => None,
    }
}

fn contract_expr_from_place_key<'tcx>(place: PlaceKey) -> ContractExpr<'tcx> {
    let base = match place.base {
        PlaceBaseKey::Return => PlaceBase::Return,
        PlaceBaseKey::Local(local) => PlaceBase::Local(local),
        PlaceBaseKey::Arg(arg) => PlaceBase::Arg(arg),
    };
    let projections = place
        .fields
        .into_iter()
        .map(|index| ContractProjection::Field { index, ty: None })
        .collect();
    ContractExpr::Place(ContractPlace { base, projections })
}

/// Return the abstract value assigned to a place when it is tracked by local.
fn value_for_place<'a, 'tcx>(
    forward: &'a ForwardVisitResult<'tcx>,
    place: &PlaceKey,
) -> Option<&'a AbstractValue<'tcx>> {
    let local = place.local()?;
    forward.values.get(&local)
}

/// Base local of a pointer/reference/place abstract value.
fn abstract_value_base_local(value: &AbstractValue<'_>) -> Option<Local> {
    match value {
        AbstractValue::Place(p) | AbstractValue::Ref(p) | AbstractValue::RawPtr(p) => p.local(),
        AbstractValue::Cast(inner, _) => abstract_value_base_local(inner),
        _ => None,
    }
}

/// Follow copy/reference/cast chains through the caller MIR to the root local
/// backing `start`.  Unlike [`resolve_root_local`], this does not depend on the
/// forward slice retaining the intermediate definitions, so it can relate a
/// call's argument (`&indices`) to a later use of the same array.
fn resolve_root_local_mir(
    tcx: TyCtxt<'_>,
    caller: rustc_hir::def_id::DefId,
    start: Local,
) -> Local {
    let body = tcx.optimized_mir(caller);
    let mut cur = start;
    let mut seen = HashSet::new();
    while seen.insert(cur) {
        let mut next = None;
        for bb in body.basic_blocks.iter() {
            for stmt in &bb.statements {
                let rustc_middle::mir::StatementKind::Assign(assign) = &stmt.kind else {
                    continue;
                };
                let (dest, rvalue) = &**assign;
                if dest.local != cur || !dest.projection.is_empty() {
                    continue;
                }
                next = rvalue_base_local(rvalue);
            }
        }
        match next {
            Some(n) if n != cur => cur = n,
            _ => break,
        }
    }
    cur
}

/// Base local flowing into a place from a reference/copy/cast rvalue.
fn rvalue_base_local(rvalue: &Rvalue<'_>) -> Option<Local> {
    match rvalue {
        Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) | Rvalue::CopyForDeref(place) => {
            Some(place.local)
        }
        Rvalue::Use(Operand::Copy(place) | Operand::Move(place), ..)
        | Rvalue::Cast(_, Operand::Copy(place) | Operand::Move(place), _) => Some(place.local),
        _ => None,
    }
}

/// Return the pointee type of raw pointers and references.
fn pointee_ty<'tcx>(ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
    match ty.kind() {
        TyKind::RawPtr(ty, _) | TyKind::Ref(_, ty, _) => Some(*ty),
        _ => None,
    }
}

/// Return a string label for the pointee type, for type-level alias checks.
fn pointee_ty_str<'tcx>(ty: Ty<'tcx>) -> Option<String> {
    match ty.kind() {
        TyKind::RawPtr(inner, _) | TyKind::Ref(_, inner, _) => Some(format!("{inner:?}")),
        _ => None,
    }
}

fn is_len_carrying_ty(ty: Ty<'_>) -> bool {
    match ty.kind() {
        TyKind::Ref(_, inner, _) => is_len_carrying_ty(*inner),
        TyKind::Slice(_) | TyKind::Str => true,
        _ => false,
    }
}

/// The name of the const-generic length parameter of a fixed array `[E; N]`,
/// looking through references and a `MaybeUninit` wrapper.  Returns `None` for
/// concrete lengths or non-array types.
fn array_const_len_param(ty: Ty<'_>) -> Option<String> {
    match ty.kind() {
        TyKind::Array(_, len) => match len.kind() {
            ConstKind::Param(param) => Some(param.name.to_string()),
            _ => None,
        },
        TyKind::Ref(_, inner, _) => array_const_len_param(*inner),
        TyKind::Adt(_, args) if format!("{ty:?}").contains("MaybeUninit") => args
            .first()
            .and_then(|arg| match arg.kind() {
                GenericArgKind::Type(ty) => Some(ty),
                _ => None,
            })
            .and_then(array_const_len_param),
        _ => None,
    }
}

/// Follow `local = move/copy other` (no projections) to the root local.
fn mir_copy_root<'tcx>(body: &rustc_middle::mir::Body<'tcx>, mut local: Local) -> Local {
    for _ in 0..16 {
        let mut next = None;
        for bb in body.basic_blocks.iter() {
            for stmt in &bb.statements {
                let StatementKind::Assign(assign) = &stmt.kind else {
                    continue;
                };
                let (dest, rvalue) = assign.as_ref();
                if dest.local != local || !dest.projection.is_empty() {
                    continue;
                }
                if let Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..) = rvalue
                    && src.projection.is_empty()
                {
                    next = Some(src.local);
                }
            }
        }
        match next {
            Some(n) if n != local => local = n,
            _ => return local,
        }
    }
    local
}

/// Find the destination of `MaybeUninit::as_mut_ptr(&mut arr)` for `arr_local`.
fn find_as_mut_ptr_of<'tcx>(
    body: &rustc_middle::mir::Body<'tcx>,
    arr_local: Local,
    tcx: TyCtxt<'tcx>,
) -> Option<Local> {
    for data in body.basic_blocks.iter() {
        let Some(term) = &data.terminator else {
            continue;
        };
        let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &term.kind
        else {
            continue;
        };
        let name = crate::verify::call_summary::call_name(tcx, func);
        if !name.contains("as_mut_ptr") {
            continue;
        }
        let Some(arg_local) = args.first().and_then(|a| a.node.place()).map(|p| p.local) else {
            continue;
        };
        // arg is `&mut arr` (or a copy chain to it).
        if mir_ref_root(body, arg_local) == arr_local {
            return Some(destination.local);
        }
    }
    None
}

/// Follow `local = &mut x` / copies to the referenced root local.
fn mir_ref_root<'tcx>(body: &rustc_middle::mir::Body<'tcx>, mut local: Local) -> Local {
    for _ in 0..16 {
        let mut next = None;
        for bb in body.basic_blocks.iter() {
            for stmt in &bb.statements {
                let StatementKind::Assign(assign) = &stmt.kind else {
                    continue;
                };
                let (dest, rvalue) = assign.as_ref();
                if dest.local != local || !dest.projection.is_empty() {
                    continue;
                }
                match rvalue {
                    Rvalue::Ref(_, _, src) | Rvalue::RawPtr(_, src) => next = Some(src.local),
                    Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..)
                        if src.projection.is_empty() =>
                    {
                        next = Some(src.local)
                    }
                    _ => {}
                }
            }
        }
        match next {
            Some(n) if n != local => local = n,
            _ => return local,
        }
    }
    local
}

/// If `ptr_local` is `base.add(idx)` (an element `ptr::add` call), return
/// `(idx_local, base_local)`.
fn pointer_add_index_and_base<'tcx>(
    body: &rustc_middle::mir::Body<'tcx>,
    ptr_local: Local,
    tcx: TyCtxt<'tcx>,
) -> Option<(Local, Local)> {
    let ptr_local = mir_copy_root(body, ptr_local);
    for data in body.basic_blocks.iter() {
        let Some(term) = &data.terminator else {
            continue;
        };
        let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &term.kind
        else {
            continue;
        };
        if destination.local != ptr_local {
            continue;
        }
        let name = crate::verify::call_summary::call_name(tcx, func);
        // Element-stride add only (byte variants change alignment/stride).
        if !(name.ends_with("::add") || name.contains("::add::")) {
            return None;
        }
        let base = args.first().and_then(|a| a.node.place())?.local;
        let idx = args.get(1).and_then(|a| a.node.place())?.local;
        return Some((idx, base));
    }
    None
}

/// Follow `ptr::cast` / copies to the root pointer local.
fn mir_ptr_cast_root<'tcx>(
    body: &rustc_middle::mir::Body<'tcx>,
    mut local: Local,
    tcx: TyCtxt<'tcx>,
) -> Local {
    for _ in 0..16 {
        let root = mir_copy_root(body, local);
        let mut next = None;
        for data in body.basic_blocks.iter() {
            let Some(term) = &data.terminator else {
                continue;
            };
            let TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } = &term.kind
            else {
                continue;
            };
            if destination.local != root {
                continue;
            }
            if crate::verify::call_summary::call_name(tcx, func).contains("::cast")
                && let Some(src) = args.first().and_then(|a| a.node.place())
            {
                next = Some(src.local);
            }
        }
        match next {
            Some(n) if n != root => local = n,
            _ => return root,
        }
    }
    local
}

/// Find `opt` such that `idx = copy ((opt as Some).0)`.
fn mir_some_payload_source<'tcx>(
    body: &rustc_middle::mir::Body<'tcx>,
    idx_local: Local,
) -> Option<Local> {
    for bb in body.basic_blocks.iter() {
        for stmt in &bb.statements {
            let StatementKind::Assign(assign) = &stmt.kind else {
                continue;
            };
            let (dest, rvalue) = assign.as_ref();
            if dest.local != idx_local || !dest.projection.is_empty() {
                continue;
            }
            if let Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..) = rvalue
                && src
                    .projection
                    .iter()
                    .any(|p| matches!(p, ProjectionElem::Downcast(..)))
                && src
                    .projection
                    .iter()
                    .any(|p| matches!(p, ProjectionElem::Field(..)))
            {
                return Some(src.local);
            }
        }
    }
    None
}

/// Find `opt = Iterator::next(&mut r)` with `r: Range`; return `(header, r)`.
fn mir_range_next_call<'tcx>(
    body: &rustc_middle::mir::Body<'tcx>,
    opt_local: Local,
    tcx: TyCtxt<'tcx>,
) -> Option<(BasicBlock, Local)> {
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        let Some(term) = &data.terminator else {
            continue;
        };
        let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &term.kind
        else {
            continue;
        };
        if destination.local != opt_local {
            continue;
        }
        if !crate::verify::call_summary::call_name(tcx, func).contains("::next") {
            return None;
        }
        let arg_local = args.first().and_then(|a| a.node.place())?.local;
        let range_local = mir_ref_root(body, arg_local);
        let is_range = body
            .local_decls
            .get(range_local)
            .map(|d| {
                let s = format!("{:?}", d.ty);
                s.contains("Range<") && !s.contains("RangeInclusive")
            })
            .unwrap_or(false);
        return is_range.then_some((bb, range_local));
    }
    None
}

/// Recover the const-generic name of a `Range { start, end }`'s `end`, tracing
/// through copies and the `into_iter` identity.
fn mir_range_end_param<'tcx>(
    body: &rustc_middle::mir::Body<'tcx>,
    range_local: Local,
    tcx: TyCtxt<'tcx>,
) -> Option<String> {
    let mut local = range_local;
    for _ in 0..8 {
        for bb in body.basic_blocks.iter() {
            for stmt in &bb.statements {
                let StatementKind::Assign(assign) = &stmt.kind else {
                    continue;
                };
                let (dest, rvalue) = assign.as_ref();
                if dest.local != local || !dest.projection.is_empty() {
                    continue;
                }
                if let Rvalue::Aggregate(_, operands) = rvalue
                    && let Some(end) = operands.iter().nth(1)
                    && let Some(param) = const_operand_param_name(end)
                {
                    return Some(param);
                }
            }
        }
        let mut next = None;
        for bb in body.basic_blocks.iter() {
            for stmt in &bb.statements {
                let StatementKind::Assign(assign) = &stmt.kind else {
                    continue;
                };
                let (dest, rvalue) = assign.as_ref();
                if dest.local != local || !dest.projection.is_empty() {
                    continue;
                }
                if let Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..) = rvalue
                    && src.projection.is_empty()
                {
                    next = Some(src.local);
                }
            }
            if let Some(term) = &bb.terminator
                && let TerminatorKind::Call {
                    func,
                    args,
                    destination,
                    ..
                } = &term.kind
                && destination.local == local
                && crate::verify::call_summary::call_name(tcx, func).contains("into_iter")
                && let Some(src) = args.first().and_then(|a| a.node.place())
            {
                next = Some(src.local);
            }
        }
        match next {
            Some(n) if n != local => local = n,
            _ => return None,
        }
    }
    None
}

/// Extract the const-generic parameter name of a constant operand such as
/// `const N` (debug forms `N` or `Ty(usize, N/#1)`).
fn const_operand_param_name(operand: &Operand<'_>) -> Option<String> {
    let Operand::Constant(c) = operand else {
        return None;
    };
    let text = format!("{:?}", c.const_);
    // Newer rustc: `Ty(usize, N/#1)`; extract the `N` before `/#`.
    if let Some(open) = text.find('(')
        && let Some(close) = text.rfind(')')
        && open < close
    {
        let inner = &text[open + 1..close];
        if let Some(last) = inner.rsplit(',').next() {
            let last = last.trim();
            if let Some((name, index)) = last.split_once("/#")
                && !index.is_empty()
                && index.bytes().all(|b| b.is_ascii_digit())
                && !name.is_empty()
                && name.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_')
            {
                return Some(name.to_string());
            }
        }
    }
    // Bare identifier form.
    let t = text.trim();
    if !t.is_empty()
        && t.bytes()
            .next()
            .is_some_and(|b| b.is_ascii_alphabetic() || b == b'_')
        && t.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_')
    {
        return Some(t.to_string());
    }
    None
}

/// True when the write block `write_bb` dominates every back-edge into the loop
/// header `header` (i.e. the write runs on every iteration), so all indices are
/// covered.
fn loop_write_covers<'tcx>(
    body: &rustc_middle::mir::Body<'tcx>,
    header: BasicBlock,
    write_bb: BasicBlock,
) -> bool {
    let dominators = body.basic_blocks.dominators();
    let preds = body.basic_blocks.predecessors();
    let mut saw_latch = false;
    for &pred in &preds[header] {
        // A latch is a predecessor of the header that the header dominates
        // (i.e. lies inside the loop).
        if dominators.dominates(header, pred) {
            saw_latch = true;
            if !dominators.dominates(write_bb, pred) {
                return false;
            }
        }
    }
    saw_latch
}

fn initialized_element_ty_name<'tcx>(ty: Ty<'tcx>) -> Option<String> {
    let ty_name = format!("{ty:?}");
    if ty_name.contains("MaybeUninit") {
        return None;
    }
    match ty.kind() {
        TyKind::Ref(_, inner, _) | TyKind::RawPtr(inner, _) => {
            initialized_element_ty_name(*inner).or_else(|| Some(format!("{inner:?}")))
        }
        TyKind::Array(elem, _) | TyKind::Slice(elem) => Some(format!("{elem:?}")),
        TyKind::Adt(def, args) => {
            let def_name = format!("{:?}", def.did());
            let is_vec = def_name.contains("Vec")
                || ty_name.starts_with("std::vec::Vec<")
                || ty_name.starts_with("alloc::vec::Vec<")
                || ty_name.starts_with("Vec<");
            if is_vec {
                return args.iter().find_map(|arg| match arg.kind() {
                    GenericArgKind::Type(ty) => Some(format!("{ty:?}")),
                    _ => None,
                });
            }
            Some(ty_name)
        }
        _ => Some(ty_name),
    }
}

fn is_unsigned_integral_ty(ty: Ty<'_>) -> bool {
    matches!(ty.kind(), TyKind::Uint(_))
}

/// Return true when a call summary is a typed pointer addition.
fn is_pointer_add_call(func: &str) -> bool {
    PrimitiveCall::classify(func).is_some_and(PrimitiveCall::is_pointer_add_like)
}

/// Return true when a call summary is a typed pointer subtraction.
fn is_pointer_sub_call(func: &str) -> bool {
    PrimitiveCall::classify(func).is_some_and(PrimitiveCall::is_pointer_sub_like)
}

/// Return true when a call summary extracts a pointer from a slice-like object.
pub(crate) fn is_as_ptr_call(func: &str) -> bool {
    PrimitiveCall::classify(func).is_some_and(PrimitiveCall::is_as_ptr_like)
}

/// Return true when a call summary carries pointer-add semantics.
fn call_has_pointer_add_effect(call: &CallSummary<'_>) -> bool {
    call.effects.iter().any(|effect| {
        matches!(
            effect,
            crate::verify::call_summary::CallEffect::ReturnPointerAdd { .. }
        )
    })
}

fn call_has_pointer_sub_effect(call: &CallSummary<'_>) -> bool {
    call.effects.iter().any(|effect| {
        matches!(
            effect,
            crate::verify::call_summary::CallEffect::ReturnPointerSub { .. }
        )
    })
}

fn abstract_value_from_rvalue<'tcx>(rvalue: &Rvalue<'tcx>) -> Option<AbstractValue<'tcx>> {
    Some(match rvalue {
        Rvalue::Use(operand, ..) => abstract_value_from_operand(operand),
        Rvalue::Repeat(operand, _) => {
            AbstractValue::Repeat(Box::new(abstract_value_from_operand(operand)))
        }
        Rvalue::Ref(_, _, place) => AbstractValue::Ref(PlaceKey::from_mir_place(place)),
        Rvalue::RawPtr(_, place) => AbstractValue::RawPtr(PlaceKey::from_mir_place(place)),
        Rvalue::Cast(_, operand, ty) => {
            AbstractValue::Cast(Box::new(abstract_value_from_operand(operand)), *ty)
        }
        Rvalue::BinaryOp(op, pair) => {
            let (lhs, rhs) = &**pair;
            AbstractValue::Binary(
                *op,
                Box::new(abstract_value_from_operand(lhs)),
                Box::new(abstract_value_from_operand(rhs)),
            )
        }
        Rvalue::UnaryOp(op, operand) => {
            AbstractValue::Unary(*op, Box::new(abstract_value_from_operand(operand)))
        }
        Rvalue::CopyForDeref(place) => AbstractValue::Place(PlaceKey::from_mir_place(place)),
        Rvalue::ThreadLocalRef(def_id) => AbstractValue::ThreadLocal(format!("{def_id:?}")),
        #[cfg(all(rapx_rustc_ge_193, not(rapx_rustc_ge_196)))]
        Rvalue::NullaryOp(op) => AbstractValue::Nullary(format!("{op:?}")),
        #[cfg(all(not(rapx_rustc_ge_193), not(rapx_rustc_ge_196)))]
        Rvalue::NullaryOp(op, _) => AbstractValue::Nullary(format!("{op:?}")),
        Rvalue::Discriminant(place) => AbstractValue::Discriminant(PlaceKey::from_mir_place(place)),
        Rvalue::Aggregate(kind, operands) => {
            AbstractValue::Aggregate(format!("{kind:?}"), operands.len())
        }
        #[cfg(not(rapx_rustc_ge_196))]
        Rvalue::ShallowInitBox(operand, ty) => {
            AbstractValue::ShallowInitBox(Box::new(abstract_value_from_operand(operand)), *ty)
        }
        _ => return None,
    })
}

fn infer_element_ty<'tcx>(ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
    match ty.kind() {
        TyKind::Slice(elem_ty) => Some(*elem_ty),
        TyKind::Array(elem_ty, _) => Some(*elem_ty),
        TyKind::Ref(_, inner, _) => infer_element_ty(*inner),
        TyKind::RawPtr(inner_ty, _) => infer_element_ty(*inner_ty),
        _ => Some(ty),
    }
}

fn abstract_value_from_operand<'tcx>(operand: &Operand<'tcx>) -> AbstractValue<'tcx> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => {
            AbstractValue::Place(PlaceKey::from_mir_place(place))
        }
        Operand::Constant(constant) => {
            let text = format!("{:?}", constant.const_);
            const_int_from_debug(&text)
                .map(AbstractValue::ConstInt)
                .unwrap_or(AbstractValue::Const(text))
        }
        #[cfg(rapx_rustc_ge_196)]
        Operand::RuntimeChecks(_) => AbstractValue::Unknown("runtime-checks".to_string()),
    }
}

/// Stable SMT variable name for a place key.
fn place_name(place: &PlaceKey) -> String {
    let base = match place.base {
        PlaceBaseKey::Return => "return".to_string(),
        PlaceBaseKey::Local(local) => format!("local_{local}"),
        PlaceBaseKey::Arg(arg) => format!("arg_{arg}"),
    };
    if place.fields.is_empty() {
        base
    } else {
        format!(
            "{}_{}",
            base,
            place
                .fields
                .iter()
                .map(|field| field.to_string())
                .collect::<Vec<_>>()
                .join("_")
        )
    }
}

/// Compact human-readable label for a MIR place key.
pub(crate) fn place_label(place: &PlaceKey) -> String {
    let base = match place.base {
        PlaceBaseKey::Return => "return".to_string(),
        PlaceBaseKey::Local(local) => format!("_{local}"),
        PlaceBaseKey::Arg(arg) => format!("arg{arg}"),
    };
    if place.fields.is_empty() {
        base
    } else {
        format!(
            "{}.{}",
            base,
            place
                .fields
                .iter()
                .map(|field| field.to_string())
                .collect::<Vec<_>>()
                .join(".")
        )
    }
}

/// Compact human-readable label for an abstract value.
pub(crate) fn value_label(value: &AbstractValue<'_>) -> String {
    match value {
        AbstractValue::Unknown(text) => format!("unknown({text})"),
        AbstractValue::Place(place) => place_label(place),
        AbstractValue::Ref(place) => format!("&{}", place_label(place)),
        AbstractValue::RawPtr(place) => format!("raw({})", place_label(place)),
        AbstractValue::ThreadLocal(name) => format!("thread_local({name})"),
        AbstractValue::ConstInt(value) => value.to_string(),
        AbstractValue::ConstParam(name) => format!("const_{name}"),
        AbstractValue::Const(text) => const_int_from_debug(text)
            .map(|value| value.to_string())
            .unwrap_or_else(|| text.trim().to_string()),
        AbstractValue::Repeat(inner) => format!("repeat({})", value_label(inner)),
        AbstractValue::Cast(inner, ty) => format!("cast({}, {ty:?})", value_label(inner)),
        AbstractValue::Unary(op, inner) => format!("{op:?}({})", value_label(inner)),
        AbstractValue::Binary(op, lhs, rhs) => {
            format!(
                "({} {} {})",
                value_label(lhs),
                binop_label(*op),
                value_label(rhs)
            )
        }
        AbstractValue::Nullary(name) => name.clone(),
        AbstractValue::Discriminant(place) => format!("discriminant({})", place_label(place)),
        AbstractValue::Aggregate(name, len) => format!("{name}[{len}]"),
        #[cfg(not(rapx_rustc_ge_196))]
        AbstractValue::ShallowInitBox(inner, ty) => {
            format!("box({}, {ty:?})", value_label(inner))
        }
        AbstractValue::CallResult(call) if is_pointer_add_call(&call.func) => {
            let base = call
                .args
                .first()
                .map(value_label)
                .unwrap_or_else(|| "?".to_string());
            let index = call
                .args
                .get(1)
                .map(value_label)
                .unwrap_or_else(|| "?".to_string());
            format!("{base}.add({index})")
        }
        AbstractValue::CallResult(call) => {
            let destination = PlaceKey {
                base: PlaceBaseKey::Local(call.destination.as_usize()),
                fields: Vec::new(),
            };
            format!(
                "{} = call({})",
                place_label(&destination),
                short_func_name(&call.func)
            )
        }
    }
}

fn smt_term_for_value(value: &AbstractValue<'_>) -> Option<SmtTerm> {
    match value {
        AbstractValue::ConstInt(value) => u64::try_from(*value).ok().map(SmtTerm::Const),
        AbstractValue::Const(text) => const_int_from_debug(text)
            .and_then(|value| u64::try_from(value).ok())
            .map(SmtTerm::Const)
            .or_else(|| {
                let name = sanitize_smt_name(text);
                if name.is_empty() {
                    None
                } else {
                    Some(SmtTerm::Value(format!("const_{name}")))
                }
            }),
        AbstractValue::Place(place) => Some(SmtTerm::Place(place.clone())),
        AbstractValue::Cast(inner, _) => smt_term_for_value(inner),
        AbstractValue::Binary(op, lhs, rhs) => {
            let lhs = Box::new(smt_term_for_value(lhs)?);
            let rhs = Box::new(smt_term_for_value(rhs)?);
            match op {
                BinOp::Add | BinOp::AddWithOverflow => Some(SmtTerm::Add(lhs, rhs)),
                BinOp::Sub | BinOp::SubWithOverflow => Some(SmtTerm::Sub(lhs, rhs)),
                BinOp::Mul | BinOp::MulWithOverflow => Some(SmtTerm::Mul(lhs, rhs)),
                BinOp::Div => Some(SmtTerm::Div(lhs, rhs)),
                BinOp::Rem => Some(SmtTerm::Rem(lhs, rhs)),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Render a compact binary operator label.
fn binop_label(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::Rem => "%",
        BinOp::Eq => "==",
        BinOp::Ne => "!=",
        BinOp::Lt => "<",
        BinOp::Le => "<=",
        BinOp::Gt => ">",
        BinOp::Ge => ">=",
        _ => "?",
    }
}

/// Return the final path segment of a rustc debug function name.
fn short_func_name(func: &str) -> String {
    func.rsplit("::")
        .next()
        .unwrap_or(func)
        .trim_matches('"')
        .to_string()
}

/// Extract a const generic parameter name, e.g. `Param(N)` → `"N"`.
fn const_param_name_from_debug(text: &str) -> Option<String> {
    let text = text.trim();
    // Format: Param(N)
    if let Some(rest) = text.find("Param(").map(|i| &text[i + 6..]) {
        let end = rest.find(')')?;
        let name = rest[..end].trim().to_string();
        if !name.is_empty() {
            return Some(name);
        }
    }
    // Format: Ty(usize, N/#1)  or  Ty(usize, N)
    if let Some(rest) = text.strip_prefix("Ty(") {
        let comma = rest.find(',')?;
        let after_comma = rest[comma + 1..].trim();
        let end = after_comma.find(')').unwrap_or(after_comma.len());
        let name = after_comma[..end].trim();
        // Strip trailing /#N index if present
        if let Some(slash) = name.rfind('/') {
            let name = name[..slash].trim();
            if !name.is_empty() {
                return Some(name.to_string());
            }
        }
        if !name.is_empty() {
            return Some(name.to_string());
        }
    }
    None
}

/// Extract a small integer constant from rustc's debug representation.
fn const_int_from_debug(text: &str) -> Option<u128> {
    let text = text.trim();
    if text == "const true" {
        return Some(1);
    }
    if text == "const false" {
        return Some(0);
    }
    if let Some(rest) = text.strip_prefix("const ") {
        let digits = rest
            .chars()
            .take_while(|ch| ch.is_ascii_digit())
            .collect::<String>();
        if digits.is_empty() {
            return None;
        }
        return digits.parse().ok();
    }

    let scalar = text.strip_prefix("Val(Scalar(0x")?;
    let digits = scalar
        .chars()
        .take_while(|ch| ch.is_ascii_hexdigit())
        .collect::<String>();
    if digits.is_empty() {
        None
    } else {
        u128::from_str_radix(&digits, 16).ok()
    }
}

fn init_type_compatible(init_ty_name: &str, required_ty_name: &str) -> bool {
    let n_init = normalize_init_ty_name(init_ty_name);
    let n_req = normalize_init_ty_name(required_ty_name);
    if n_init == n_req {
        // Block a slice/array KnownInit (from the return value of
        // from_raw_parts itself) from proving a scalar Init requirement
        // for the same call's input pointer.
        let init_is_slice =
            init_ty_name.trim().starts_with('[') && init_ty_name.trim().ends_with(']');
        let req_is_slice =
            required_ty_name.trim().starts_with('[') && required_ty_name.trim().ends_with(']');
        if init_is_slice && !req_is_slice {
            return false;
        }
        return true;
    }
    if let Some(array_elem) = array_elem_type(required_ty_name) {
        if init_type_compatible(init_ty_name, &array_elem) {
            return true;
        }
    }
    // Scalars have all-bit-patterns-valid init.
    // Larger init types can cover smaller required types.
    if is_trivial_init_type(init_ty_name) && is_trivial_init_type(required_ty_name) {
        let is = scalar_size_bytes(init_ty_name);
        let rs = scalar_size_bytes(required_ty_name);
        if is >= rs {
            return true;
        }
    }
    false
}

fn is_trivial_init_type(ty_name: &str) -> bool {
    let n = normalize_init_ty_name(ty_name);
    matches!(
        n.as_str(),
        "u8" | "u16"
            | "u32"
            | "u64"
            | "u128"
            | "usize"
            | "i8"
            | "i16"
            | "i32"
            | "i64"
            | "i128"
            | "isize"
            | "f32"
            | "f64"
    ) || n.starts_with("*const ")
        || n.starts_with("*mut ")
}

fn scalar_size_bytes(ty_name: &str) -> u64 {
    let n = normalize_init_ty_name(ty_name);
    match n.as_str() {
        "u8" | "i8" => 1,
        "u16" | "i16" => 2,
        "u32" | "i32" | "f32" => 4,
        "u64" | "i64" | "f64" => 8,
        "u128" | "i128" => 16,
        _ => {
            if n.starts_with("*const ") || n.starts_with("*mut ") {
                8 // assume 64-bit pointers
            } else {
                0
            }
        }
    }
}

fn init_elem_size_ratio(init_ty_name: &str, required_ty_name: &str) -> u64 {
    let is = scalar_size_bytes(init_ty_name);
    let rs = scalar_size_bytes(required_ty_name);
    if is > 0 && rs > 0 && is >= rs && is % rs == 0 {
        is / rs
    } else if is > 0 && rs > 0 {
        0
    } else {
        1
    }
}

fn allocated_type_compatible(allocated_ty_name: &str, required_ty_name: &str) -> bool {
    if normalize_init_ty_name(allocated_ty_name) == normalize_init_ty_name(required_ty_name) {
        return true;
    }
    // Box<T> allocation is compatible with T: into_raw transfers ownership
    // to a raw pointer that points to the inner allocation.
    let box_inner = allocated_ty_name
        .strip_prefix("std::boxed::Box<")
        .or_else(|| allocated_ty_name.strip_prefix("alloc::boxed::Box<"))
        .or_else(|| allocated_ty_name.strip_prefix("Box<"));
    if let Some(rest) = box_inner {
        if let Some(inner_end) = rest.rfind('>') {
            let inner_ty = &rest[..inner_end];
            if let Some(comma) = inner_ty.find(", ") {
                return allocated_type_compatible(&inner_ty[..comma], required_ty_name);
            }
            return allocated_type_compatible(inner_ty, required_ty_name);
        }
    }
    if let Some(array_elem) = array_elem_type(required_ty_name) {
        if allocated_type_compatible(allocated_ty_name, &array_elem) {
            return true;
        }
    }
    false
}

fn array_elem_type(ty_name: &str) -> Option<String> {
    let name = ty_name.trim();
    if name.starts_with('[') && name.ends_with(']') {
        let inner = &name[1..name.len() - 1];
        if let Some(semi) = inner.rfind("; ") {
            return Some(format!(" {}", &inner[..semi]));
        }
    }
    None
}
/// Owning wrapper types whose drop frees the carried allocation.
fn is_owning_wrapper_ty(ty_name: &str) -> bool {
    ty_name.contains("Box<")
        || ty_name.contains("Vec<")
        || ty_name.contains("String")
        || ty_name.contains("CString")
}

/// Build a body-wide value-provenance map: each local points to the local it
/// was derived from via copies, casts, refs, or pointer/ownership-transfer
/// calls (`into_raw`, `from_raw`, `as_ptr`, ...).
fn body_value_parents<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: rustc_hir::def_id::DefId,
) -> crate::compat::FxHashMap<Local, Local> {
    use rustc_middle::mir::TerminatorKind;

    let mut parents: crate::compat::FxHashMap<Local, Local> = Default::default();
    let body = tcx.optimized_mir(def_id);
    for data in body.basic_blocks.iter() {
        for statement in &data.statements {
            let StatementKind::Assign(assign) = &statement.kind else {
                continue;
            };
            let (target, rvalue) = assign.as_ref();
            let source = match rvalue {
                Rvalue::Use(Operand::Copy(place) | Operand::Move(place), ..)
                | Rvalue::Cast(_, Operand::Copy(place) | Operand::Move(place), _)
                | Rvalue::Ref(_, _, place)
                | Rvalue::RawPtr(_, place)
                | Rvalue::CopyForDeref(place) => Some(place.local),
                _ => None,
            };
            if let Some(source) = source {
                parents.entry(target.local).or_insert(source);
            }
        }
        let Some(terminator) = &data.terminator else {
            continue;
        };
        let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &terminator.kind
        else {
            continue;
        };
        let name = crate::verify::call_summary::call_name(tcx, func);
        let transfers = name.contains("into_raw")
            || crate::verify::call_summary::is_ownership_reconstruction(&name)
            || PrimitiveCall::classify(&name).is_some_and(|p| p.is_as_ptr_like());
        if !transfers {
            continue;
        }
        let Some(source) = args.first().and_then(|arg| match &arg.node {
            Operand::Copy(place) | Operand::Move(place) => Some(place.local),
            _ => None,
        }) else {
            continue;
        };
        parents.entry(destination.local).or_insert(source);
    }
    parents
}

/// Follow the provenance map to the root local (with a cycle guard).
fn follow_value_parents(parents: &crate::compat::FxHashMap<Local, Local>, start: Local) -> Local {
    let mut current = start;
    let mut seen = std::collections::HashSet::new();
    while seen.insert(current) {
        let Some(next) = parents.get(&current) else {
            break;
        };
        current = *next;
    }
    current
}

fn allocation_object_invalidated<'tcx>(
    forward: &ForwardVisitResult<'tcx>,
    object: &PlaceKey,
    alloc_place: &PlaceKey,
) -> bool {
    forward.facts.iter().any(|fact| match fact {
        StateFact::LocalDead(local) => {
            object.local() == Some(*local)
                // A KnownAllocated fact referencing a dead object is still
                // valid when a PointsTo link transfers the allocation from
                // the (now dead) wrapper to a live pointer (e.g. Box into_raw).
                && !forward.facts.iter().any(|f| {
                    matches!(f, StateFact::PointsTo { pointer, source }
                        if *pointer == *alloc_place && *source == *object)
                })
        }
        StateFact::Drop(place) => place.overlaps(object) || object.overlaps(place),
        _ => false,
    })
}

fn normalize_init_ty_name(ty_name: &str) -> String {
    let ty_name = ty_name.trim();
    if let Some(rest) = ty_name.strip_prefix('[')
        && rest.ends_with(']')
    {
        let inner = &rest[..rest.len() - 1];
        if let Some(semi_pos) = inner.rfind("; ") {
            return normalize_init_ty_name(&inner[..semi_pos]);
        }
        // Slice type [T] — same alignment as T.
        return normalize_init_ty_name(inner);
    }
    let mut result = ty_name.to_string();
    while let Some(slash) = result.rfind('/')
        && slash + 1 < result.len()
        && result[slash + 1..].starts_with('#')
    {
        let trimmed = result[..slash].to_string();
        if let Some(after_hash) = result[slash + 2..].chars().next()
            && after_hash.is_ascii_digit()
        {
            result = trimmed;
            continue;
        }
        break;
    }
    result
}

/// Stable SMT identifier for diagnostic-only symbolic terms.
fn sanitize_smt_name(name: &str) -> String {
    name.chars()
        .map(|ch| {
            if ch.is_ascii_alphanumeric() || ch == '_' {
                ch
            } else {
                '_'
            }
        })
        .collect()
}

fn ptr_metadata_origin<'tcx>(
    value: &AbstractValue<'tcx>,
    model: &SmtModel<'_, '_, 'tcx>,
) -> Option<String> {
    let resolved = model
        .resolved_value(value, &mut TraceSeen::new())
        .unwrap_or_else(|| value.clone());
    match &resolved {
        AbstractValue::Unary(UnOp::PtrMetadata, inner) => {
            let cursor = model.latest_cursor();
            model.origin_key_for_value_before(inner, cursor, &mut TraceSeen::new())
        }
        AbstractValue::CallResult(call) => {
            if call.effects.iter().any(|e| {
                matches!(
                    e,
                    crate::verify::call_summary::CallEffect::ReturnLengthOfArg { .. }
                )
            }) {
                let arg = call.effects.iter().find_map(|e| match e {
                    crate::verify::call_summary::CallEffect::ReturnLengthOfArg { arg } => {
                        Some(*arg)
                    }
                    _ => None,
                })?;
                let call_cursor = model.call_definition_cursor(call);
                let source = call.args.get(arg)?;
                model.origin_key_for_value_before(source, call_cursor, &mut TraceSeen::new())
            } else {
                None
            }
        }
        _ => None,
    }
}

fn pointee_stride_from_types<'tcx>(
    tcx: TyCtxt<'tcx>,
    src_pointee: Ty<'tcx>,
    dst_pointee: Ty<'tcx>,
) -> Option<SmtTerm> {
    use rustc_middle::ty::ConstKind;
    if src_pointee == dst_pointee {
        return Some(SmtTerm::Const(1));
    }
    if let TyKind::Array(elem, len) = src_pointee.kind()
        && *elem == dst_pointee
    {
        return len
            .try_to_target_usize(tcx)
            .map(SmtTerm::Const)
            .or_else(|| {
                if let ConstKind::Param(param) = len.kind() {
                    Some(SmtTerm::ConstParam(param.name.to_string()))
                } else {
                    None
                }
            });
    }
    None
}

/// True when `root` is defined as a field (any index) of `tuple_dest`.
fn mir_is_tuple_field_of<'tcx>(
    body: &rustc_middle::mir::Body<'tcx>,
    root: Local,
    tuple_dest: Local,
) -> bool {
    for bb in body.basic_blocks.iter() {
        for stmt in &bb.statements {
            let StatementKind::Assign(assign) = &stmt.kind else {
                continue;
            };
            let (dest, rvalue) = assign.as_ref();
            if dest.local != root || !dest.projection.is_empty() {
                continue;
            }
            if let Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..) = rvalue
                && src.local == tuple_dest
                && src.projection.len() == 1
                && matches!(src.projection[0], ProjectionElem::Field(..))
            {
                return true;
            }
        }
    }
    false
}
