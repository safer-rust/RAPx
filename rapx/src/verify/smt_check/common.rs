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
    mir::{BinOp, Local, Operand, Rvalue, TerminatorKind, UnOp},
    ty::{GenericArgKind, PseudoCanonicalInput, Ty, TyCtxt, TyKind},
};
use z3::{
    Config, Context, SatResult, Solver,
    ast::{Ast, Bool, Int},
};

use super::{
    alias, align, allocated, deref, in_bound, init, non_null, non_overlap, valid_num, valid_ptr,
};

use crate::verify::{
    contract::{
        ContractExpr, ContractPlace, ContractProjection, NumericOp, NumericPredicate, PlaceBase,
        Property, PropertyArg, PropertyKind, RelOp,
    },
    def_use::{PlaceBaseKey, PlaceKey},
    verifier::{AbstractValue, CallSummary, ForwardVisitResult, StateFact},
    generic::GenericTypeCandidates,
    helpers::{Checkpoint, callee_param_index_for_local},
    path_extractor::PathStep,
    primitive::PrimitiveCall,
    report::CheckResult,
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
            PropertyKind::Allocated => allocated::check(self, checkpoint, property, forward),
            PropertyKind::Deref => deref::check(self, checkpoint, property, forward),
            PropertyKind::NonNull => non_null::check(self, checkpoint, property, forward),
            PropertyKind::InBound => in_bound::check(self, checkpoint, property, forward),
            PropertyKind::Init => init::check(self, checkpoint, property, forward),
            PropertyKind::NonOverlap => non_overlap::check(self, checkpoint, property, forward),
            PropertyKind::ValidNum => valid_num::check(self, checkpoint, property, forward),
            PropertyKind::ValidPtr => valid_ptr::check(self, checkpoint, property, forward),
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
                SmtCheckResult::unknown("Allocated struct invariant not implemented yet")
            }
            PropertyKind::NonNull => {
                SmtCheckResult::unknown("NonNull struct invariant not implemented yet")
            }
            PropertyKind::InBound => {
                in_bound::check_for_checkpoint(self, caller, property, forward)
            }
            PropertyKind::Init => init::check_for_checkpoint(self, caller, property, forward),
            PropertyKind::ValidPtr => {
                SmtCheckResult::unknown("ValidPtr struct invariant not implemented yet")
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
    ) -> SmtCheckResult {
        if !forward.forgets.is_empty() {
            let reasons = forward
                .forgets
                .iter()
                .map(|reason| format!("{reason:?}"))
                .collect::<Vec<_>>()
                .join(", ");
            return SmtCheckResult::unknown(
                "path has precision loss; SMT proof is not trusted without a summary",
            )
            .with_query(SmtQuery::new(
                obligation,
                Vec::new(),
                SmtPredicate::Custom(String::from(
                    "proof skipped because relevant state was forgotten",
                )),
            ))
            .with_note(format!("precision loss: {reasons}"));
        }

        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let solver = Solver::new(&ctx);
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
                let covered_end = Int::add(&ctx, &[bounds.index.clone(), access]);
                let within_len = covered_end.le(&bounds.len);
                solver.assert(&index_non_negative);
                solver.assert(&access_non_negative);
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
                        SmtCheckResult::unknown(
                            "current path facts do not prove the required bounds",
                        )
                        .with_query(query)
                        .with_note(
                            "hint: add an index < len guard or provide a richer object-size summary",
                        )
                    }
                    SatResult::Unknown => {
                        SmtCheckResult::unknown("solver returned unknown").with_query(query)
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
            } => {
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
                    let covered_end = Int::add(&ctx, &[bounds.index.clone(), access]);
                    let within_len = covered_end.le(&bounds.len);
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
                                matched_elements = matched_elements.saturating_add(*init_elements);
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
                    let covered_end = Int::add(&ctx, &[bounds.index.clone(), access]);
                    let within_len = covered_end.le(&bounds.len);
                    solver.assert(&index_non_negative);
                    solver.assert(&access_non_negative);
                    model.assumptions.push(SmtPredicate::Ge(
                        bounds.index_term.clone(),
                        SmtTerm::Const(0),
                    ));
                    model
                        .assumptions
                        .push(SmtPredicate::Ge(elements.clone(), SmtTerm::Const(0)));
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
                        SatResult::Sat => SmtCheckResult::unknown(
                            "current path facts do not prove the requested range stays inside one allocation",
                        )
                        .with_query(query)
                        .with_note(
                            "hint: add an object-length guard or provide a richer allocation summary",
                        ),
                        SatResult::Unknown => {
                            SmtCheckResult::unknown("solver returned unknown").with_query(query)
                        }
                    };
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
                    if allocation_object_invalidated(forward, &object) {
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
        };
        self.prove_obligation(&dummy_checkpoint, forward, obligation)
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
            ContractExpr::SizeOf(ty) => {
                let size = self.required_size(caller, *ty)?;
                Some(SmtTerm::Const(size))
            }
            ContractExpr::AlignOf(ty) => {
                let align = self.required_alignment(caller, *ty)?;
                Some(SmtTerm::Const(align))
            }
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

    fn bind_contract_expr_to_callsite(
        &self,
        checkpoint: &Checkpoint<'tcx>,
        expr: &ContractExpr<'tcx>,
    ) -> Option<ContractExpr<'tcx>> {
        match expr {
            ContractExpr::Place(place) => self.contract_place_to_callsite_expr(checkpoint, place),
            ContractExpr::Const(value) => Some(ContractExpr::Const(*value)),
            ContractExpr::SizeOf(ty) => Some(ContractExpr::SizeOf(
                self.instantiate_callsite_ty(checkpoint, *ty),
            )),
            ContractExpr::AlignOf(ty) => Some(ContractExpr::AlignOf(
                self.instantiate_callsite_ty(checkpoint, *ty),
            )),
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
        let operand = checkpoint.args.get(index)?;
        if fields.is_empty()
            && let Operand::Constant(constant) = operand
            && let Some(value) = const_int_from_debug(&format!("{:?}", constant.const_))
        {
            return Some(ContractExpr::Const(value));
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

    /// Return the `index`-th call argument as a common SMT term.
    pub(crate) fn callsite_arg_smt_term(
        &self,
        checkpoint: &Checkpoint<'tcx>,
        index: usize,
    ) -> Option<SmtTerm> {
        let expr = self.callsite_arg_expr(checkpoint, index, &[])?;
        self.contract_expr_to_smt_term(checkpoint.caller, &expr)
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
        let Some(arg) = args.get(param.index as usize) else {
            return ty;
        };
        match arg.kind() {
            GenericArgKind::Type(actual_ty) => actual_ty,
            _ => ty,
        }
    }

    /// Return ABI alignment and size for a type.
    pub(crate) fn type_layout(
        &self,
        caller: rustc_hir::def_id::DefId,
        ty: Ty<'tcx>,
    ) -> Option<(u64, u64)> {
        let typing_env = rustc_middle::ty::TypingEnv::post_analysis(self.tcx, caller);
        let input = PseudoCanonicalInput {
            typing_env,
            value: ty,
        };
        match self.tcx.layout_of(input) {
            Ok(layout) => Some((layout.align.abi.bytes(), layout.size.bytes())),
            Err(_) if matches!(ty.kind(), TyKind::Param(_)) => Some((0, 0)),
            Err(_) => None,
        }
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
        self.generic_candidate_alignments(caller, ty)?
            .into_iter()
            .max()
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
        if !matches!(ty.kind(), TyKind::Param(_)) {
            return self.type_layout(caller, ty).map(|(_, size)| size);
        }
        self.generic_candidate_sizes(caller, ty)?.into_iter().max()
    }

    /// Classify whether a type is definitely zero-sized, definitely non-zero,
    /// or still layout-ambiguous under the current generic bounds.
    pub(crate) fn type_size_class(
        &self,
        caller: rustc_hir::def_id::DefId,
        ty: Ty<'tcx>,
    ) -> TypeSizeClass {
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
}

/// Trivalent size classification for type-dependent composite SPs.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum TypeSizeClass {
    Zero,
    NonZero,
    Unknown,
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

fn failed_smt(note: impl Into<String>) -> SmtCheckResult {
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
    symbolic_align_terms: HashMap<String, Int<'ctx>>,
    assumptions: Vec<SmtPredicate>,
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
            symbolic_align_terms: HashMap::new(),
            assumptions: Vec::new(),
        }
    }

    /// Create or return a cached symbolic alignment constant for a type name.
    pub(crate) fn symbolic_align_term(&mut self, ty_name: &str) -> Int<'ctx> {
        if let Some(term) = self.symbolic_align_terms.get(ty_name) {
            return term.clone();
        }
        let term = Int::new_const(self.ctx, format!("align_{ty_name}"));
        self.symbolic_align_terms
            .insert(ty_name.to_string(), term.clone());
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
            let is_target_kind =
                matches!(property.kind, PropertyKind::InBound | PropertyKind::Init);
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

    /// Assert facts collected by the forward visitor.
    pub(crate) fn assert_forward_facts(&mut self, solver: &Solver<'ctx>) {
        for fact in &self.forward.facts {
            match fact {
                StateFact::PointsTo { pointer, source } => {
                    self.assert_place_non_zero(
                        solver,
                        pointer,
                        "created from a reference/raw pointer",
                    );
                    // Only assert alignment on the pointer when the pointee types
                    // match – pointer-arithmetic wrappers produce pointers of a
                    // different pointee type whose alignment must be proved from
                    // guard facts, not from the raw type alone.
                    let ptr_pointee = self.place_ty(pointer).and_then(|ty| pointee_ty_str(ty));
                    let src_pointee = self.place_ty(source).and_then(|ty| pointee_ty_str(ty));
                    if ptr_pointee == src_pointee {
                        self.assert_place_alignment(solver, pointer);
                    }
                    self.assert_place_alignment(solver, source);
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
                StateFact::BranchEq { value, equals } => {
                    if let Some(term) = self.term_for_value(value, &mut HashSet::new()) {
                        let expected = Int::from_u64(self.ctx, *equals as u64);
                        solver.assert(&term._eq(&expected));
                        self.assumptions.push(SmtPredicate::Eq(
                            SmtTerm::Value(value_label(value)),
                            SmtTerm::Const(*equals as u64),
                        ));
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
                    _ => {}
                },
                StateFact::PathCondition(_)
                | StateFact::Drop(_)
                | StateFact::LocalDead(_)
                | StateFact::CallEffect(_) => {}
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
            let (base_arg, offset_arg) = call.effects.iter().find_map(|effect| {
                let crate::verify::call_summary::CallEffect::ReturnPointerAdd {
                    base_arg,
                    offset_arg,
                    ..
                } = effect
                else {
                    return None;
                };
                Some((*base_arg, *offset_arg))
            })?;
            let base = call.args.get(base_arg)?;
            let index = call.args.get(offset_arg)?;
            let call_cursor = self.call_definition_cursor(&call);
            let base_origin =
                self.origin_key_for_value_before(base, call_cursor, &mut TraceSeen::new())?;

            let index_term = self.term_for_value_at(index, call_cursor, &mut TraceSeen::new())?;
            let (len_term_int, len_term) = self.bounds_len_for_origin(&base_origin, Some(index))?;
            return Some(PointerBounds {
                index: index_term,
                len: len_term_int,
                index_term: SmtTerm::Value(value_label(index)),
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
        let (len_term_int, len_term) = self.bounds_len_for_origin(&base_origin, Some(&zero))?;

        Some(PointerBounds {
            index: Int::from_u64(self.ctx, 0),
            len: len_term_int,
            index_term: SmtTerm::Const(0),
            len_term,
            origin_key: base_origin,
        })
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
        self.forward.facts.iter().find_map(|fact| match fact {
            StateFact::KnownAllocated {
                place: allocated_place,
                object,
                ..
            } if allocated_place == place => Some(object.clone()),
            _ => None,
        })
    }

    /// Assert that a place is known to denote a non-zero address.
    pub(crate) fn assert_place_non_zero(
        &mut self,
        solver: &Solver<'ctx>,
        place: &PlaceKey,
        reason: &str,
    ) {
        if let Some(term) = self.term_for_place(place) {
            let zero = Int::from_u64(self.ctx, 0);
            solver.assert(&term._eq(&zero).not());
            self.assumptions.push(SmtPredicate::Custom(format!(
                "{} != 0 ({reason})",
                place_label(place)
            )));
        }
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
        if align <= 1 {
            return;
        }
        if let Some(term) = self.term_for_place(place) {
            let zero = Int::from_u64(self.ctx, 0);
            let align_term = Int::from_u64(self.ctx, align);
            solver.assert(&term.modulo(&align_term)._eq(&zero));
            self.assumptions.push(SmtPredicate::Custom(format!(
                "{} aligned for {align_ty:?} ({align} bytes)",
                place_label(place)
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
                    let source = call
                        .args
                        .get(*arg)
                        .and_then(|value| {
                            self.origin_key_for_value_before(value, cursor, &mut TraceSeen::new())
                        })
                        .or_else(|| call.args.get(*arg).map(value_label))
                        .unwrap_or_else(|| format!("arg{arg}"));
                    let len_term =
                        Int::new_const(self.ctx, sanitize_smt_name(&format!("len({source})")));
                    self.place_terms.insert(destination.clone(), len_term);
                    self.assumptions.push(SmtPredicate::Eq(
                        SmtTerm::Place(destination.clone()),
                        SmtTerm::Value(format!("len({source})")),
                    ));
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
                crate::verify::call_summary::CallEffect::ReturnNonZero
                | crate::verify::call_summary::CallEffect::ReturnAligned { .. }
                | crate::verify::call_summary::CallEffect::ReadMemory { .. }
                | crate::verify::call_summary::CallEffect::WriteMemory { .. }
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
        if place.fields.as_slice() != [0] {
            return None;
        }
        let mut base = place.clone();
        base.fields.clear();
        let local = base.local()?;
        let definition = self.forward.latest_value_definition_before(local, cursor)?;
        let value = &definition.value;
        let AbstractValue::Binary(op, lhs, rhs) = value else {
            return None;
        };
        if !matches!(
            op,
            BinOp::AddWithOverflow | BinOp::SubWithOverflow | BinOp::MulWithOverflow
        ) {
            return None;
        }
        let lhs = self.term_for_value_at(lhs, definition.ordinal, seen)?;
        let rhs = self.term_for_value_at(rhs, definition.ordinal, seen)?;
        self.term_for_binary(*op, &lhs, &rhs)
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
        Some(Int::new_const(
            self.ctx,
            sanitize_smt_name(&format!("len({source})")),
        ))
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
            AbstractValue::Const(text) => {
                const_int_from_debug(text).map(|value| Int::from_u64(self.ctx, value as u64))
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
                let place = PlaceKey {
                    base: PlaceBaseKey::Local(call.destination.as_usize()),
                    fields: Vec::new(),
                };
                Some(Int::new_const(self.ctx, place_name(&place)))
            }
            AbstractValue::Unknown(_)
            | AbstractValue::ThreadLocal(_)
            | AbstractValue::Repeat(_)
            | AbstractValue::Unary(_, _)
            | AbstractValue::Nullary(_)
            | AbstractValue::Discriminant(_)
            | AbstractValue::Aggregate(_, _) => None,
            #[cfg(not(rapx_rustc_ge_196))]
            AbstractValue::ShallowInitBox(_, _) => None,
        }
    }

    /// Build an SMT integer term from a property-independent diagnostic term.
    fn term_for_smt_term(&mut self, term: &SmtTerm) -> Option<Int<'ctx>> {
        match term {
            SmtTerm::Place(place) => self.term_for_place(place),
            SmtTerm::Value(name) => Some(Int::new_const(self.ctx, sanitize_smt_name(name))),
            SmtTerm::Const(value) => Some(Int::from_u64(self.ctx, *value)),
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
            SmtTerm::Value(_) | SmtTerm::Const(_) => {}
        }
    }

    /// Lower a binary MIR operation to an integer term.
    fn term_for_binary(&self, op: BinOp, lhs: &Int<'ctx>, rhs: &Int<'ctx>) -> Option<Int<'ctx>> {
        let one = Int::from_u64(self.ctx, 1);
        let zero = Int::from_u64(self.ctx, 0);
        Some(match op {
            BinOp::Add | BinOp::AddWithOverflow => Int::add(self.ctx, &[lhs.clone(), rhs.clone()]),
            BinOp::Sub | BinOp::SubWithOverflow => Int::sub(self.ctx, &[lhs.clone(), rhs.clone()]),
            BinOp::Mul | BinOp::MulWithOverflow => Int::mul(self.ctx, &[lhs.clone(), rhs.clone()]),
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
            return None;
        }
        let local = match place.base {
            PlaceBaseKey::Return => Local::from_usize(0),
            PlaceBaseKey::Local(local) => Local::from_usize(local),
            PlaceBaseKey::Arg(_) => return None,
        };
        Some(self.tcx.optimized_mir(self.checkpoint.caller).local_decls[local].ty)
    }

    /// Return ABI alignment and size for a type.
    fn type_layout(&self, ty: Ty<'tcx>) -> Option<(u64, u64)> {
        let typing_env = rustc_middle::ty::TypingEnv::post_analysis(self.tcx, self.checkpoint.caller);
        let input = PseudoCanonicalInput {
            typing_env,
            value: ty,
        };
        match self.tcx.layout_of(input) {
            Ok(layout) => Some((layout.align.abi.bytes(), layout.size.bytes())),
            Err(_) if matches!(ty.kind(), TyKind::Param(_)) => Some((0, 0)),
            Err(_) => None,
        }
    }

    /// Return the alignment guaranteed by a concrete or generic type.
    fn guaranteed_alignment(&self, ty: Ty<'tcx>) -> Option<u64> {
        if let Some((align, _)) = self.type_layout(ty).filter(|(align, _)| *align > 0) {
            return Some(align);
        }
        self.generic_candidate_alignments(ty)?.into_iter().min()
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
            AbstractValue::CallResult(call) if call_has_pointer_add_effect(&call) => Some(call),
            _ => None,
        }
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
        let body = self.tcx.optimized_mir(self.forward.callsite.caller);
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
            block: self.forward.callsite.block,
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
                .or_else(|| Some(place_label(&place))),
            AbstractValue::Cast(inner, _) => self.origin_key_for_value_before(&inner, cursor, seen),
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
                let source_arg = call.effects.iter().find_map(|effect| match effect {
                    crate::verify::call_summary::CallEffect::ReturnPointerFromArg { arg }
                    | crate::verify::call_summary::CallEffect::ReturnAliasArg { arg } => Some(*arg),
                    _ => None,
                })?;
                let call_cursor = self.call_definition_cursor(&call);
                self.origin_key_for_value_before(call.args.get(source_arg)?, call_cursor, seen)
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
            let StateFact::BranchEq { value, equals: 1 } = fact else {
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
        self.forward.facts.iter().find_map(|fact| match fact {
            StateFact::PointsTo {
                pointer: fact_pointer,
                source,
            } if fact_pointer == pointer => Some(source.clone()),
            _ => None,
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
        if let Some(AbstractValue::Place(inner)) = value_for_place(self.forward, place) {
            return self.storage_addr_for_place(inner, seen);
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
        self.allocated_len_for_origin(origin_key)
            .map(|len| (Int::from_u64(self.ctx, len), SmtTerm::Const(len)))
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
                ..
            } if place_label(object) == origin_key || place_label(place) == origin_key => {
                Some(*elements)
            }
            _ => None,
        })
    }

    fn origin_is_initialized_for_ty(&self, origin_key: &str, required_ty_name: &str) -> bool {
        self.forward.facts.iter().any(|fact| {
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
        })
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
fn operand_place(operand: &Operand<'_>) -> Option<PlaceKey> {
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
fn is_as_ptr_call(func: &str) -> bool {
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
            .map(SmtTerm::Const),
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
    normalize_init_ty_name(init_ty_name) == normalize_init_ty_name(required_ty_name)
}

fn allocated_type_compatible(allocated_ty_name: &str, required_ty_name: &str) -> bool {
    normalize_init_ty_name(allocated_ty_name) == normalize_init_ty_name(required_ty_name)
}

fn allocation_object_invalidated<'tcx>(
    forward: &ForwardVisitResult<'tcx>,
    object: &PlaceKey,
) -> bool {
    forward.facts.iter().any(|fact| match fact {
        StateFact::LocalDead(local) => object.local() == Some(*local),
        StateFact::Drop(place) => place.overlaps(object) || object.overlaps(place),
        _ => false,
    })
}

fn normalize_init_ty_name(ty_name: &str) -> String {
    let ty_name = ty_name.trim();
    for prefix in [
        "std::mem::MaybeUninit<",
        "core::mem::MaybeUninit<",
        "MaybeUninit<",
    ] {
        if let Some(inner) = ty_name
            .strip_prefix(prefix)
            .and_then(|s| s.strip_suffix('>'))
        {
            return normalize_init_ty_name(inner);
        }
    }
    ty_name.to_string()
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
