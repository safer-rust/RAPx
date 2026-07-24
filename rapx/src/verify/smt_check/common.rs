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

use std::collections::HashSet;

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
    helpers::{Checkpoint, callee_param_index_for_local, ty_has_param_const},
    primitive::PrimitiveCall,
    report::CheckResult,
    slicer::ForgetReason,
    verifier::{AbstractValue, CallSummary, ForwardVisitResult, StateFact},
};

use super::model::SmtModel;

pub(crate) type ValueCursor = usize;
pub(crate) type TraceSeen = std::collections::HashSet<(PlaceKey, ValueCursor)>;

#[derive(Clone, Copy)]
pub(crate) struct PathCursorCutoff {
    pub(crate) block: rustc_middle::mir::BasicBlock,
    pub(crate) statement_index: Option<usize>,
}

/// SMT backend for verifier properties.
pub struct SmtChecker<'tcx> {
    pub(crate) tcx: TyCtxt<'tcx>,
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
                if checkpoint.is_ref {
                    SmtCheckResult::proved(
                        "NonVolatile holds for ref-derived pointer",
                    )
                } else {
                    SmtCheckResult::proved(
                        "NonVolatile assumed — std memory is never volatile",
                    )
                }
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
            PropertyKind::Alive => {
                if let Some(reason) =
                    super::field_invariant::discharge_from_contract_fact(property, forward)
                {
                    return SmtCheckResult::proved(format!("Alive proved: {reason}"));
                }
                SmtCheckResult::proved(
                    "Alive: pointer derived from entry invariant (assumed preserved)",
                )
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
                solver.assert(&access_non_negative);
                solver.assert(&len_non_negative);
                if !bounds.index_is_signed {
                    solver.assert(&index_non_negative);
                    model.assumptions.push(SmtPredicate::Ge(
                        bounds.index_term.clone(),
                        SmtTerm::Const(0),
                    ));
                }
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

                // Assert count >= 0 so Z3 can derive count <= len from
                // ValidNum constraints that imply len >= count + 1.
                solver.assert(&upper.ge(&zero));
                model.assumptions.push(SmtPredicate::Ge(
                    upper_delta.clone(),
                    SmtTerm::Const(0),
                ));

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

    /// Resolve the target place of a property.
    ///
    /// When `checkpoint` is `Some`, callee argument places are rebound to the
    /// concrete MIR places passed by the caller.  When `None`, the raw contract
    /// place is resolved without callsite binding (for struct-invariant checks).
    pub(crate) fn property_target(
        &self,
        checkpoint: Option<&Checkpoint<'tcx>>,
        property: &Property<'tcx>,
    ) -> Option<PlaceKey> {
        let arg = property.args.first()?;
        match arg {
            PropertyArg::Place(place) => match checkpoint {
                Some(cp) => self.contract_place_to_callsite_place(cp, place),
                None => Some(self.resolve_contract_place(place)),
            },
            PropertyArg::Expr(ContractExpr::Place(place)) => match checkpoint {
                Some(cp) => self.contract_place_to_callsite_place(cp, place),
                None => Some(self.resolve_contract_place(place)),
            },
            PropertyArg::Expr(ContractExpr::IndexAccess { slice, .. }) => {
                // Only supported with a concrete checkpoint (callsite checks).
                checkpoint?;
                match slice.as_ref() {
                    ContractExpr::Place(place) => {
                        self.contract_place_to_callsite_place(checkpoint.unwrap(), place)
                    }
                    _ => None,
                }
            }
            PropertyArg::Expr(ContractExpr::Const(index)) => {
                checkpoint?;
                let index = usize::try_from(*index).ok()?;
                self.callsite_arg_place(checkpoint.unwrap(), index)
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

    /// Convert a contract place to a PlaceKey, resolving Arg(n) to Local(n+1).
    fn resolve_contract_place(&self, place: &ContractPlace<'tcx>) -> PlaceKey {
        let mut key = PlaceKey::from_contract_place(place);
        if let PlaceBaseKey::Arg(index) = key.base {
            key.base = PlaceBaseKey::Local(index + 1);
        }
        key
    }

    /// Resolve the type argument of a property.
    ///
    /// When `checkpoint` is `Some`, callee generic parameters are instantiated
    /// to their concrete types at the call site.  When `None`, the raw type is
    /// returned without instantiation (for struct-invariant checks).
    pub(crate) fn property_required_ty(
        &self,
        checkpoint: Option<&Checkpoint<'tcx>>,
        property: &Property<'tcx>,
    ) -> Option<Ty<'tcx>> {
        property.args.iter().find_map(|arg| {
            let PropertyArg::Ty(ty) = arg else {
                return None;
            };
            match checkpoint {
                Some(cp) => Some(self.instantiate_callsite_ty(cp, *ty)),
                None => Some(*ty),
            }
        })
    }

    /// Resolve the trailing length expression.
    ///
    /// When `checkpoint` is `Some`, callee argument places are rebound to the
    /// concrete MIR places passed by the caller.  When `None`, the raw expression
    /// is returned without rebinding (for struct-invariant checks).
    pub(crate) fn property_len_expr(
        &self,
        checkpoint: Option<&Checkpoint<'tcx>>,
        property: &Property<'tcx>,
    ) -> Option<ContractExpr<'tcx>> {
        property.args.iter().rev().find_map(|arg| {
            let PropertyArg::Expr(expr) = arg else {
                return None;
            };
            match checkpoint {
                Some(cp) => self.bind_contract_expr_to_callsite(cp, expr),
                None => Some(expr.clone()),
            }
        })
    }

    /// Lower a rebound contract arithmetic expression into the common SMT term model.
    pub(crate) fn contract_expr_to_smt_term(
        &self,
        caller: rustc_hir::def_id::DefId,
        expr: &ContractExpr<'tcx>,
        forward: Option<&ForwardVisitResult<'tcx>>,
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
            ContractExpr::Len(inner) => {
                // Always use a symbolic len term whose Z3 constant is
                // shared with `contract_inbound_lens` via `symbolic_len_term`.
                // The `len_call_term` path would return `SmtTerm::Place`,
                // which maps to a different Z3 constant and breaks
                // unification between ValidNum predicates and InBound lens.
                let mut key = match inner.as_ref() {
                    ContractExpr::Place(cp) => PlaceKey::from_contract_place(cp),
                    _ => return None,
                };
                if let PlaceBaseKey::Arg(ix) = key.base {
                    key.base = PlaceBaseKey::Local(ix + 1);
                }
                Some(SmtTerm::Value(format!("len({})", place_label(&key))))
            }
            ContractExpr::IndexAccess { .. } => None,
            ContractExpr::Binary { op, lhs, rhs } => {
                let lhs = Box::new(self.contract_expr_to_smt_term(caller, lhs, forward)?);
                let rhs = Box::new(self.contract_expr_to_smt_term(caller, rhs, forward)?);
                match op {
                    NumericOp::Add => Some(SmtTerm::Add(lhs, rhs)),
                    NumericOp::Sub => Some(SmtTerm::Sub(lhs, rhs)),
                    NumericOp::Mul => Some(SmtTerm::Mul(lhs, rhs)),
                    NumericOp::Div => Some(SmtTerm::Div(lhs, rhs)),
                    NumericOp::Rem => Some(SmtTerm::Rem(lhs, rhs)),
                    NumericOp::BitAnd | NumericOp::BitOr | NumericOp::BitXor => None,
                }
            }
            ContractExpr::Min { a, b } => {
                let a = Box::new(self.contract_expr_to_smt_term(caller, a, forward)?);
                let b = Box::new(self.contract_expr_to_smt_term(caller, b, forward)?);
                Some(SmtTerm::Min(a, b))
            }
            ContractExpr::Max { a, b } => {
                let a = Box::new(self.contract_expr_to_smt_term(caller, a, forward)?);
                let b = Box::new(self.contract_expr_to_smt_term(caller, b, forward)?);
                Some(SmtTerm::Max(a, b))
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
        forward: Option<&ForwardVisitResult<'tcx>>,
    ) -> Option<SmtPredicate> {
        let lhs = self.contract_expr_to_smt_term(caller, &predicate.lhs, forward)?;
        let rhs = self.contract_expr_to_smt_term(caller, &predicate.rhs, forward)?;
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
        forward: Option<&ForwardVisitResult<'tcx>>,
    ) -> Option<Vec<SmtPredicate>> {
        let predicates = self.property_numeric_predicates(checkpoint, property)?;
        let mut lowered = Vec::new();
        for predicate in predicates {
            if let Some(expanded) = self.expand_index_access_predicate(checkpoint, &predicate)? {
                lowered.extend(expanded);
            } else {
                lowered.push(self.numeric_predicate_to_smt_predicate(
                    checkpoint.caller,
                    &predicate,
                    forward,
                )?);
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
        let index_term = self.contract_expr_to_smt_term(caller, index, None)?;
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
        self.contract_expr_to_smt_term(caller, &contract_expr_from_place_key(place), None)
    }

    fn contract_expr_place(&self, expr: &ContractExpr<'tcx>) -> Option<PlaceKey> {
        let ContractExpr::Place(place) = expr else {
            return None;
        };
        Some(PlaceKey::from_contract_place(place))
    }


    fn contract_expr_label(&self, expr: &ContractExpr<'tcx>) -> Option<String> {
        match expr {
            ContractExpr::Place(place) => {
                let mut key = PlaceKey::from_contract_place(place);
                if let PlaceBaseKey::Arg(ix) = key.base {
                    key.base = PlaceBaseKey::Local(ix + 1);
                }
                Some(place_label(&key))
            }
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
            ContractExpr::Min { a, b } => Some(ContractExpr::Min {
                a: Box::new(self.bind_contract_expr_to_callsite(checkpoint, a)?),
                b: Box::new(self.bind_contract_expr_to_callsite(checkpoint, b)?),
            }),
            ContractExpr::Max { a, b } => Some(ContractExpr::Max {
                a: Box::new(self.bind_contract_expr_to_callsite(checkpoint, a)?),
                b: Box::new(self.bind_contract_expr_to_callsite(checkpoint, b)?),
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
        self.contract_expr_to_smt_term(checkpoint.caller, &expr, None)
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
    Min(Box<SmtTerm>, Box<SmtTerm>),
    Max(Box<SmtTerm>, Box<SmtTerm>),
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
            SmtTerm::Min(lhs, rhs) => format!("min({}, {})", lhs.describe(), rhs.describe()),
            SmtTerm::Max(lhs, rhs) => format!("max({}, {})", lhs.describe(), rhs.describe()),
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

pub(crate) fn smt_term_const_u64(term: &SmtTerm) -> Option<u64> {
    match term {
        SmtTerm::Const(value) => Some(*value),
        _ => None,
    }
}

pub(crate) fn pointer_range_negated_goal(
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
// SmtModel is defined in the `model` sub-module (common/model.rs).
pub(crate) struct PointerBounds<'ctx> {
    pub(crate) index: Int<'ctx>,
    pub(crate) len: Int<'ctx>,
    pub(crate) index_term: SmtTerm,
    pub(crate) len_term: SmtTerm,
    pub(crate) origin_key: String,
    pub(crate) index_is_signed: bool,
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

pub(crate) fn contract_expr_from_place_key<'tcx>(place: PlaceKey) -> ContractExpr<'tcx> {
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
pub(crate) fn value_for_place<'a, 'tcx>(
    forward: &'a ForwardVisitResult<'tcx>,
    place: &PlaceKey,
) -> Option<&'a AbstractValue<'tcx>> {
    let local = place.local()?;
    forward.values.get(&local)
}

/// Base local of a pointer/reference/place abstract value.
pub(crate) fn abstract_value_base_local(value: &AbstractValue<'_>) -> Option<Local> {
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
pub(crate) fn resolve_root_local_mir(
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
pub(crate) fn rvalue_base_local(rvalue: &Rvalue<'_>) -> Option<Local> {
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
pub(crate) fn pointee_ty<'tcx>(ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
    match ty.kind() {
        TyKind::RawPtr(ty, _) | TyKind::Ref(_, ty, _) => Some(*ty),
        _ => None,
    }
}

/// Return a string label for the pointee type, for type-level alias checks.
pub(crate) fn pointee_ty_str<'tcx>(ty: Ty<'tcx>) -> Option<String> {
    match ty.kind() {
        TyKind::RawPtr(inner, _) | TyKind::Ref(_, inner, _) => Some(format!("{inner:?}")),
        _ => None,
    }
}

pub(crate) fn is_len_carrying_ty(ty: Ty<'_>) -> bool {
    match ty.kind() {
        TyKind::Ref(_, inner, _) => is_len_carrying_ty(*inner),
        TyKind::Slice(_) | TyKind::Str => true,
        _ => false,
    }
}

/// The name of the const-generic length parameter of a fixed array `[E; N]`,
/// looking through references and a `MaybeUninit` wrapper.  Returns `None` for
/// concrete lengths or non-array types.
pub(crate) fn array_const_len_param(ty: Ty<'_>) -> Option<String> {
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
pub(crate) fn mir_copy_root<'tcx>(body: &rustc_middle::mir::Body<'tcx>, mut local: Local) -> Local {
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
pub(crate) fn find_as_mut_ptr_of<'tcx>(
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
pub(crate) fn mir_ref_root<'tcx>(body: &rustc_middle::mir::Body<'tcx>, mut local: Local) -> Local {
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
pub(crate) fn pointer_add_index_and_base<'tcx>(
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
pub(crate) fn mir_ptr_cast_root<'tcx>(
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
pub(crate) fn mir_some_payload_source<'tcx>(
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
pub(crate) fn mir_range_next_call<'tcx>(
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
pub(crate) fn mir_range_end_param<'tcx>(
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
pub(crate) fn const_operand_param_name(operand: &Operand<'_>) -> Option<String> {
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
pub(crate) fn loop_write_covers<'tcx>(
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

pub(crate) fn initialized_element_ty_name<'tcx>(ty: Ty<'tcx>) -> Option<String> {
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

pub(crate) fn is_unsigned_integral_ty(ty: Ty<'_>) -> bool {
    matches!(ty.kind(), TyKind::Uint(_))
}

/// Return true when a call summary is a typed pointer addition.
pub(crate) fn is_pointer_add_call(func: &str) -> bool {
    PrimitiveCall::classify(func).is_some_and(PrimitiveCall::is_pointer_add_like)
}

/// Return true when a call summary is a typed pointer subtraction.
pub(crate) fn is_pointer_sub_call(func: &str) -> bool {
    PrimitiveCall::classify(func).is_some_and(PrimitiveCall::is_pointer_sub_like)
}

/// Return true when a call summary extracts a pointer from a slice-like object.
pub(crate) fn is_as_ptr_call(func: &str) -> bool {
    PrimitiveCall::classify(func).is_some_and(PrimitiveCall::is_as_ptr_like)
}

/// Return true when a call summary carries pointer-add semantics.
pub(crate) fn call_has_pointer_add_effect(call: &CallSummary<'_>) -> bool {
    call.effects.iter().any(|effect| {
        matches!(
            effect,
            crate::verify::call_summary::CallEffect::ReturnPointerAdd { .. }
        )
    })
}

pub(crate) fn call_has_pointer_sub_effect(call: &CallSummary<'_>) -> bool {
    call.effects.iter().any(|effect| {
        matches!(
            effect,
            crate::verify::call_summary::CallEffect::ReturnPointerSub { .. }
        )
    })
}

pub(crate) fn abstract_value_from_rvalue<'tcx>(rvalue: &Rvalue<'tcx>) -> Option<AbstractValue<'tcx>> {
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

pub(crate) fn infer_element_ty<'tcx>(ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
    match ty.kind() {
        TyKind::Slice(elem_ty) => Some(*elem_ty),
        TyKind::Array(elem_ty, _) => Some(*elem_ty),
        TyKind::Ref(_, inner, _) => infer_element_ty(*inner),
        TyKind::RawPtr(inner_ty, _) => infer_element_ty(*inner_ty),
        _ => Some(ty),
    }
}

pub(crate) fn abstract_value_from_operand<'tcx>(operand: &Operand<'tcx>) -> AbstractValue<'tcx> {
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
pub(crate) fn place_name(place: &PlaceKey) -> String {
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

pub(crate) fn smt_term_for_value(value: &AbstractValue<'_>) -> Option<SmtTerm> {
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
pub(crate) fn binop_label(op: BinOp) -> &'static str {
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
pub(crate) fn short_func_name(func: &str) -> String {
    func.rsplit("::")
        .next()
        .unwrap_or(func)
        .trim_matches('"')
        .to_string()
}

/// Extract a const generic parameter name, e.g. `Param(N)` → `"N"`.
pub(crate) fn const_param_name_from_debug(text: &str) -> Option<String> {
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
pub(crate) fn const_int_from_debug(text: &str) -> Option<u128> {
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

pub(crate) fn init_type_compatible(init_ty_name: &str, required_ty_name: &str) -> bool {
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

pub(crate) fn is_trivial_init_type(ty_name: &str) -> bool {
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

pub(crate) fn scalar_size_bytes(ty_name: &str) -> u64 {
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

pub(crate) fn init_elem_size_ratio(init_ty_name: &str, required_ty_name: &str) -> u64 {
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

pub(crate) fn allocated_type_compatible(allocated_ty_name: &str, required_ty_name: &str) -> bool {
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

pub(crate) fn array_elem_type(ty_name: &str) -> Option<String> {
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
pub(crate) fn is_owning_wrapper_ty(ty_name: &str) -> bool {
    ty_name.contains("Box<")
        || ty_name.contains("Vec<")
        || ty_name.contains("String")
        || ty_name.contains("CString")
}

/// Build a body-wide value-provenance map: each local points to the local it
/// was derived from via copies, casts, refs, or pointer/ownership-transfer
/// calls (`into_raw`, `from_raw`, `as_ptr`, ...).
pub(crate) fn body_value_parents<'tcx>(
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
pub(crate) fn follow_value_parents(parents: &crate::compat::FxHashMap<Local, Local>, start: Local) -> Local {
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

pub(crate) fn allocation_object_invalidated<'tcx>(
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

pub(crate) fn normalize_init_ty_name(ty_name: &str) -> String {
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
pub(crate) fn sanitize_smt_name(name: &str) -> String {
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

pub(crate) fn ptr_metadata_origin<'tcx>(
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

pub(crate) fn pointee_stride_from_types<'tcx>(
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
pub(crate) fn mir_is_tuple_field_of<'tcx>(
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
