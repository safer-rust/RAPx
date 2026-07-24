//! Per-query SMT term builder over a forward visit result.
//!
//! This is a sub-module of [`super`] (common).  As a child module it inherits
//! access to all items — types, utilities, and helpers — defined in the parent
//! `common` module without explicit imports.

use std::collections::{HashMap, HashSet};

use rustc_middle::{
    mir::{BinOp, Local, Operand, UnOp},
    ty::{Ty, TyCtxt, TyKind},
};
use z3::{
    ast::{Ast, Bool, Int},
    Context, Solver,
};

use crate::verify::{
    contract::{
        ContractExpr, NumericOp, NumericPredicate, PropertyArg, PropertyKind, RelOp,
    },
    def_use::{PlaceBaseKey, PlaceKey},
    generic::GenericTypeCandidates,
    helpers::Checkpoint,
    path_extractor::PathStep,
    primitive::PrimitiveCall,
    verifier::{AbstractValue, CallSummary, ForwardVisitResult, StateFact},
};

use super::common::*;

/// Per-query SMT term builder over a forward visit result.
pub(crate) struct SmtModel<'a, 'ctx, 'tcx> {
    pub(crate) tcx: TyCtxt<'tcx>,
    pub(crate) checkpoint: &'a Checkpoint<'tcx>,
    pub(crate) forward: &'a ForwardVisitResult<'tcx>,
    pub(crate) ctx: &'ctx Context,
    pub(crate) place_terms: HashMap<PlaceKey, Int<'ctx>>,
    /// Shared Z3 constants per MIR local — ensures every reference to the
    /// same local produces the exact same SMT term (e.g. `mid` used in both
    /// `ptr.add` and `unchecked_sub`).
    pub(crate) local_terms: HashMap<usize, Int<'ctx>>,
    pub(crate) symbolic_align_terms: HashMap<String, Int<'ctx>>,
    pub(crate) symbolic_len_terms: HashMap<String, Int<'ctx>>,
    pub(crate) const_terms: HashMap<String, Int<'ctx>>,
    pub(crate) assumptions: Vec<SmtPredicate>,
    /// Set to true when IndexAccess InBound assumptions were added from caller contract
    pub(crate) has_index_access_assumptions: bool,
    /// Lenses recovered from `InBound(ptr, T, len_expr)` contract facts, keyed by
    /// the origin label of the pointer, so `bounds_len_for_origin` can discover
    /// allocation sizes for sub‑range proofs (e.g. `.add(idx)`) without needing
    /// `as_ptr` call‑site tracking.
    pub(crate) contract_inbound_lens: HashMap<String, (Int<'ctx>, SmtTerm)>,
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
            contract_inbound_lens: HashMap::new(),
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

    pub(crate) fn symbolic_len_term(&mut self, len_key: &str) -> Int<'ctx> {
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
    pub(crate) fn has_equivalent_contract_fact(&mut self, place: &PlaceKey, _kind: PropertyKind) -> bool {
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

    pub(crate) fn contract_predicate_to_smt(
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

    pub(crate) fn smt_term_from_contract_expr(&mut self, expr: &ContractExpr<'tcx>) -> Option<SmtTerm> {
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

    pub(crate) fn value_to_int(&mut self, value: &AbstractValue<'tcx>) -> Option<Int<'ctx>> {
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
                    self.record_call_effect_assumptions(solver, call);
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
                    // cmp::min(a, b) => result <= a && result <= b
                    if call.func.contains("::cmp::min") {
                        let dest = PlaceKey {
                            base: PlaceBaseKey::Local(call.destination.as_usize()),
                            fields: Vec::new(),
                        };
                        let cursor = self.call_definition_cursor(call);
                        if let Some(dest_term) = self.term_for_place(&dest) {
                            if let Some(arg0) = call.args.get(0)
                                && let Some(arg0_term) =
                                    self.term_for_value_at(arg0, cursor, &mut TraceSeen::new())
                            {
                                solver.assert(&dest_term.le(&arg0_term));
                                self.place_terms.insert(dest.clone(), dest_term.clone());
                                self.assumptions.push(SmtPredicate::Le(
                                    SmtTerm::Place(dest.clone()),
                                    SmtTerm::Value(value_label(arg0)),
                                ));
                            }
                            if let Some(arg1) = call.args.get(1)
                                && let Some(arg1_term) =
                                    self.term_for_value_at(arg1, cursor, &mut TraceSeen::new())
                            {
                                solver.assert(&dest_term.le(&arg1_term));
                                self.assumptions.push(SmtPredicate::Le(
                                    SmtTerm::Place(dest),
                                    SmtTerm::Value(value_label(arg1)),
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
                        // Handle 3-arg InBound(ptr, Ty, count) form
                        // args = [Place(slice_ptr), Ty(T), Expr(count)]
                        // count is either a single-element index (Place/Const)
                        // or a total-element len expression (Len(slice)).
                        if property.args.len() == 3 {
                            let slice_place = match property.args.get(0) {
                                Some(PropertyArg::Place(place)) => place,
                                _ => {
                                    continue;
                                }
                            };
                            let count_expr = match property.args.get(2) {
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
                            // Try to extract a concrete index or recognise a total-length form.
                            let is_total_len = matches!(
                                count_expr,
                                ContractExpr::Len(_) | ContractExpr::Binary { .. }
                            );
                            let index_term = match count_expr {
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
                                _ if is_total_len => {
                                    // The contract gives the full element count, not a
                                    // single-element index.  The symbolic `len(…)` term
                                    // was already created above; just assert non‑negativity
                                    // and record it so pointer‑bounds recovery can discover
                                    // it later.
                                    let len_int = self.symbolic_len_term(&format!("len({slice_label})"));
                                    let zero = Int::from_u64(self.ctx, 0);
                                    solver.assert(&len_int.ge(&zero));
                                    self.assumptions.push(SmtPredicate::Le(
                                        SmtTerm::Const(0),
                                        SmtTerm::Value(format!("len({slice_label})")),
                                    ));
                                    // Record this bound so that `pointer_bounds_for_place`
                                    // can find the allocation length for sub‑range queries.
                                self.contract_inbound_lens
                                    .insert(slice_label.to_string(), (len_int, len.clone()));
                                // Also assert the full InBounds fact so that
                                // `allocated_len_for_origin` / KnownAllocated
                                // paths see the length.
                                self.assumptions.push(SmtPredicate::InBounds {
                                    index: SmtTerm::Const(0),
                                    access_count: SmtTerm::Const(1),
                                    len: len.clone(),
                                });
                                self.has_index_access_assumptions = true;
                                    continue;
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
                                    // Assert len >= 0 for len terms so that
                                    // len != 0 implies len >= 1 downstream.
                                    self.assert_numeric_term_non_negativity(solver, &smt_pred);
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
    pub(crate) fn assert_round_down_products(&mut self, solver: &Solver<'ctx>) {
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

    pub(crate) fn latest_cursor(&self) -> ValueCursor {
        self.forward.value_definitions.len()
    }

    pub(crate) fn call_definition_cursor(&self, call: &CallSummary<'tcx>) -> ValueCursor {
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
    pub(crate) fn defining_cast(&self, place: &PlaceKey) -> Option<(AbstractValue<'tcx>, Ty<'tcx>)> {
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
    pub(crate) fn cast_source_pointee(&self, value: &AbstractValue<'tcx>, depth: usize) -> Option<Ty<'tcx>> {
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

            let is_signed = PrimitiveCall::classify(&call.func)
                .is_some_and(|p| p.is_signed_pointer_arithmetic());

            return Some(PointerBounds {
                index: result_index_val,
                len: len_term_int,
                index_term: result_index_smt,
                len_term,
                origin_key: base_origin,
                index_is_signed: is_signed,
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
        let (mut index_term, mut index_val) =
            self.field_projection_index(place, &base_origin);

        // When the place traces to a pointer-arithmetic call result
        // (e.g. `.add(idx)`), use the call's offset argument as the index
        // so the SMT goal reflects the actual pointer offset rather than 0.
        let pointer_add_call: Option<CallSummary<'tcx>> = match &value {
            AbstractValue::CallResult(call) if call_has_pointer_add_effect(call) => {
                Some((*call).clone())
            }
            _ => None,
        };
        if let Some(call) = pointer_add_call {
            for effect in &call.effects {
                if let crate::verify::call_summary::CallEffect::ReturnPointerAdd {
                    offset_arg, ..
                } = effect
                {
                    if let Some(offset) = call.args.get(*offset_arg) {
                        let call_cursor = self.call_definition_cursor(&call);
                        if let Some(off_val) = self.term_for_value_at(
                            offset,
                            call_cursor,
                            &mut TraceSeen::new(),
                        ) {
                            index_term = SmtTerm::Value(value_label(offset));
                            index_val = off_val;
                        }
                    }
                }
            }
        }

        Some(PointerBounds {
            index: index_val,
            len: len_term_int,
            index_term,
            len_term,
            origin_key: base_origin,
            index_is_signed: false,
        })
    }

    /// Walk the value chain for `place` to determine if it is a field projection
    /// from an `as_ptr_range`/`as_mut_ptr_range` result (or an inlined equivalent).
    /// Returns (index_term, index_val).  Field [0] (start) → offset 0;
    /// field [1] (end) → offset len.
    pub(crate) fn field_projection_index(
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
    pub(crate) fn pointer_object_offset_for_place(&self, place: &PlaceKey) -> Option<(PlaceKey, SmtTerm)> {
        self.pointer_object_offset_for_place_before(
            place,
            self.latest_cursor(),
            &mut TraceSeen::new(),
        )
    }

    pub(crate) fn pointer_object_offset_for_place_before(
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

    pub(crate) fn pointer_object_offset_for_value(
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

    pub(crate) fn allocated_object_for_place(&self, place: &PlaceKey) -> Option<PlaceKey> {
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
    pub(crate) fn assert_bounded_range(
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
    pub(crate) fn assert_lcm_split_bounds(
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
    pub(crate) fn assert_place_alignment(&mut self, solver: &Solver<'ctx>, place: &PlaceKey) {
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
    pub(crate) fn assert_known_alignment(
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
    pub(crate) fn assert_known_const(
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
    pub(crate) fn assert_length_alias(&mut self, solver: &Solver<'ctx>, left: &PlaceKey, right: &PlaceKey) {
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

    pub(crate) fn is_len_carrying_place(&self, place: &PlaceKey) -> bool {
        self.place_ty(place).is_some_and(is_len_carrying_ty)
    }

    /// True when `place` (or its resolved root) is a reference or slice.
    pub(crate) fn place_is_len_carrying_slice(&self, place: &PlaceKey) -> bool {
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
    pub(crate) fn bridge_tuple_field_lengths(&mut self, solver: &Solver<'ctx>, call: &CallSummary<'tcx>) {
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
    pub(crate) fn bridge_field_length(
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
    pub(crate) fn multiple_divisor(&self, value: &AbstractValue<'tcx>) -> Option<AbstractValue<'tcx>> {
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
    pub(crate) fn resolve_arith(
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
    pub(crate) fn record_call_effect_assumptions(&mut self, solver: &Solver<'ctx>, call: &CallSummary<'tcx>) {
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
                    solver.assert(&len_term.ge(&Int::from_u64(self.ctx, 0)));
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
                    solver.assert(&len_term.ge(&zero));
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
                crate::verify::call_summary::CallEffect::ReturnMin { lhs_arg, rhs_arg } => {
                    let dest_term = SmtTerm::Place(destination.clone());
                    let lhs_val = call.args.get(*lhs_arg);
                    let rhs_val = call.args.get(*rhs_arg);
                    let lhs_term = lhs_val.and_then(smt_term_for_value);
                    let rhs_term = rhs_val.and_then(smt_term_for_value);
                    if let (Some(lhs), Some(rhs)) = (lhs_term, rhs_term) {
                        let dest_int = self
                            .place_terms
                            .entry(destination.clone())
                            .or_insert_with(|| Int::new_const(self.ctx, place_name(&destination)))
                            .clone();
                        let lhs_int = self.term_for_smt_term(&lhs);
                        let rhs_int = self.term_for_smt_term(&rhs);
                        if let Some(lhs_z3) = lhs_int {
                            solver.assert(&dest_int.le(&lhs_z3));
                        }
                        if let Some(rhs_z3) = rhs_int {
                            solver.assert(&dest_int.le(&rhs_z3));
                        }
                        self.assumptions
                            .push(SmtPredicate::Le(dest_term.clone(), lhs));
                        self.assumptions
                            .push(SmtPredicate::Le(dest_term.clone(), rhs));
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
    pub(crate) fn term_for_place_before(
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
    pub(crate) fn projected_term_for_place(
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
    pub(crate) fn resolve_field_through_casts(
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
    pub(crate) fn term_for_value(
        &mut self,
        value: &AbstractValue<'tcx>,
        seen: &mut TraceSeen,
    ) -> Option<Int<'ctx>> {
        self.term_for_value_at(value, self.latest_cursor(), seen)
    }

    /// Build an address expression for a call summarized as pointer arithmetic.
    pub(crate) fn term_for_pointer_arith_call(
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
    pub(crate) fn term_for_length_call(
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
    pub(crate) fn const_param_symbol(&mut self, name_or_debug: &str) -> Int<'ctx> {
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
    pub(crate) fn term_for_value_at(
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
    pub(crate) fn term_for_smt_term(&mut self, term: &SmtTerm) -> Option<Int<'ctx>> {
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
            SmtTerm::Min(lhs, rhs) => {
                let lhs_z3 = self.term_for_smt_term(lhs)?;
                let rhs_z3 = self.term_for_smt_term(rhs)?;
                Some(lhs_z3.le(&rhs_z3).ite(&lhs_z3, &rhs_z3))
            }
            SmtTerm::Max(lhs, rhs) => {
                let lhs_z3 = self.term_for_smt_term(lhs)?;
                let rhs_z3 = self.term_for_smt_term(rhs)?;
                Some(lhs_z3.ge(&rhs_z3).ite(&lhs_z3, &rhs_z3))
            }
        }
    }

    /// Build a boolean term for a conjunction of shared predicates.
    pub(crate) fn bool_for_predicates(&mut self, predicates: &[SmtPredicate]) -> Option<Bool<'ctx>> {
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
    pub(crate) fn bool_for_predicate(&mut self, predicate: &SmtPredicate) -> Option<Bool<'ctx>> {
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

    /// For every `len(...)` value in a predicate, assert `len >= 0` so that
    /// `len != 0` can imply `len >= 1`.
    pub(crate) fn assert_numeric_term_non_negativity(
        &mut self,
        solver: &Solver<'ctx>,
        predicate: &SmtPredicate,
    ) {
        let mut collect = |term: &SmtTerm| {
            self.assert_len_term_non_negativity(solver, term);
        };
        match predicate {
            SmtPredicate::Eq(lhs, rhs)
            | SmtPredicate::Ne(lhs, rhs)
            | SmtPredicate::Lt(lhs, rhs)
            | SmtPredicate::Le(lhs, rhs)
            | SmtPredicate::Gt(lhs, rhs)
            | SmtPredicate::Ge(lhs, rhs) => {
                collect(lhs);
                collect(rhs);
            }
            SmtPredicate::And(preds) => {
                for p in preds {
                    self.assert_numeric_term_non_negativity(solver, p);
                }
            }
            SmtPredicate::Not(pred) => {
                self.assert_numeric_term_non_negativity(solver, pred);
            }
            _ => {}
        }
    }

    pub(crate) fn assert_len_term_non_negativity(&mut self, solver: &Solver<'ctx>, term: &SmtTerm) {
        match term {
            SmtTerm::Value(name) if name.starts_with("len(") => {
                let len_term = self.symbolic_len_term(name);
                let zero = Int::from_u64(self.ctx, 0);
                solver.assert(&len_term.ge(&zero));
            }
            SmtTerm::Add(lhs, rhs)
            | SmtTerm::Sub(lhs, rhs)
            | SmtTerm::Mul(lhs, rhs)
            | SmtTerm::Div(lhs, rhs)
            | SmtTerm::Rem(lhs, rhs) => {
                self.assert_len_term_non_negativity(solver, lhs);
                self.assert_len_term_non_negativity(solver, rhs);
            }
            _ => {}
        }
    }

    /// Assert Rust unsigned integer lower bounds for terms that appear in a
    /// numeric obligation.
    pub(crate) fn assert_unsigned_bounds_for_predicates(
        &mut self,
        solver: &Solver<'ctx>,
        predicates: &[SmtPredicate],
    ) {
        let mut seen = HashSet::new();
        for predicate in predicates {
            self.assert_unsigned_bounds_for_predicate(solver, predicate, &mut seen);
        }
    }

    pub(crate) fn assert_unsigned_bounds_for_predicate(
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

    pub(crate) fn assert_unsigned_bounds_for_term(
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
            SmtTerm::Value(_) | SmtTerm::Const(_) | SmtTerm::ConstParam(_) | SmtTerm::Min(..) | SmtTerm::Max(..) => {}
        }
    }

    /// Build an SMT term for a pure numeric-arithmetic intrinsic result
    /// (`unchecked_mul`/`unchecked_add`/...), reconstructing the exact value
    /// from its operands so downstream range checks can relate it back to the
    /// source quantities (e.g. `self.len() * N` in `[[T; N]]::as_flattened`).
    pub(crate) fn term_for_numeric_arith_call(
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
        } else if func.contains("::cmp::min") {
            lhs.le(&rhs).ite(&lhs, &rhs)
        } else {
            return None;
        };
        Some(term)
    }

    /// Lower a binary MIR operation to an integer term.
    pub(crate) fn term_for_binary(&self, op: BinOp, lhs: &Int<'ctx>, rhs: &Int<'ctx>) -> Option<Int<'ctx>> {
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
    pub(crate) fn call_destination_stride(&self, call: &CallSummary<'tcx>) -> Option<u64> {
        let place = PlaceKey {
            base: PlaceBaseKey::Local(call.destination.as_usize()),
            fields: Vec::new(),
        };
        let destination_ty = self.place_ty(&place)?;
        let pointee = pointee_ty(destination_ty)?;
        self.type_layout(pointee).map(|(_, size)| size)
    }

    /// Return the MIR type for a simple place key.
    pub(crate) fn place_ty(&self, place: &PlaceKey) -> Option<Ty<'tcx>> {
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

    pub(crate) fn type_layout(&self, ty: Ty<'tcx>) -> Option<(u64, u64)> {
        safe_type_layout(self.tcx, self.checkpoint.caller, ty)
    }

    /// Return the alignment guaranteed by a concrete or generic type.
    pub(crate) fn guaranteed_alignment(&self, ty: Ty<'tcx>) -> Option<u64> {
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

    pub(crate) fn generic_candidate_alignments(&self, ty: Ty<'tcx>) -> Option<Vec<u64>> {
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
    pub(crate) fn pointer_add_call_for_place(&self, place: &PlaceKey) -> Option<CallSummary<'tcx>> {
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
    pub(crate) fn place_is_reference_aligned(&self, place: &PlaceKey, ty_name: &str) -> bool {
        let Some(value) = self.resolved_value_for_place(place, &mut TraceSeen::new()) else {
            return false;
        };
        self.value_is_reference_aligned(&value, ty_name, 0)
    }

    /// See [`place_is_reference_aligned`]; follows element-stride pointer
    /// arithmetic back to an `as_ptr`/`as_mut_ptr` base, since `p.add(k)` keeps
    /// the alignment of `p` for element strides.
    pub(crate) fn value_is_reference_aligned(
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
    pub(crate) fn resolved_value_for_place(
        &self,
        place: &PlaceKey,
        seen: &mut TraceSeen,
    ) -> Option<AbstractValue<'tcx>> {
        self.resolved_value_for_place_before(place, self.latest_cursor(), seen)
    }

    pub(crate) fn resolved_value_for_place_before(
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
    pub(crate) fn resolved_value(
        &self,
        value: &AbstractValue<'tcx>,
        seen: &mut TraceSeen,
    ) -> Option<AbstractValue<'tcx>> {
        self.resolved_value_before(value, self.latest_cursor(), seen)
    }

    pub(crate) fn resolved_value_before(
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
    pub(crate) fn path_value_definition_before(
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

    pub(crate) fn path_cursor_cutoff(&self, cursor: ValueCursor) -> PathCursorCutoff {
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
    pub(crate) fn origin_key_for_value(
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
    pub(crate) fn allocated_by_align_to_offsets(
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

    pub(crate) fn origin_key_for_value_before(
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
    pub(crate) fn guarded_len_for_index(
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
    pub(crate) fn value_mentions(&self, haystack: &AbstractValue<'tcx>, needle: &AbstractValue<'tcx>) -> bool {
        self.value_mentions_inner(haystack, needle, &mut HashSet::new())
    }

    pub(crate) fn value_mentions_inner(
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
    pub(crate) fn len_matches_origin(&self, len: &AbstractValue<'tcx>, base_origin: &str) -> bool {
        self.len_matches_origin_inner(len, base_origin, &mut HashSet::new())
    }

    pub(crate) fn len_matches_origin_inner(
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
    pub(crate) fn source_from_points_to(&self, pointer: &PlaceKey) -> Option<PlaceKey> {
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
    pub(crate) fn init_target_terms(&mut self, place: &PlaceKey) -> Vec<Int<'ctx>> {
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
    pub(crate) fn init_source_terms(&mut self, place: &PlaceKey) -> Vec<Int<'ctx>> {
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
    pub(crate) fn storage_addr_for_place(
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
    pub(crate) fn bounds_len_for_origin(
        &mut self,
        origin_key: &str,
        index: Option<&AbstractValue<'tcx>>,
    ) -> Option<(Int<'ctx>, SmtTerm)> {
        if let Some((term, smt)) = self.contract_inbound_lens_find(origin_key) {
            return Some((term, smt));
        }
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
        result.or_else(|| self.bounds_len_from_contract_fact(origin_key))
    }

    /// The const-generic length parameter of a fixed-array allocation object
    /// (optionally under references / `MaybeUninit`), if any.
    pub(crate) fn array_len_param_for_origin(&self, origin_key: &str) -> Option<String> {
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
    pub(crate) fn is_slice_pointer_origin(&self, origin_key: &str) -> bool {
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
    pub(crate) fn is_maybe_uninit_origin(&self, origin_key: &str) -> bool {
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

    /// Look up a symbolic length in `contract_inbound_lens` for `origin_key`,
    /// trying exact match, single-entry fallback, and substring heuristics.
    pub(crate) fn contract_inbound_lens_find(&self, origin_key: &str) -> Option<(Int<'ctx>, SmtTerm)> {
        if let Some((term, smt)) = self.contract_inbound_lens.get(origin_key) {
            return Some((term.clone(), smt.clone()));
        }
        if self.contract_inbound_lens.len() == 1 {
            let (term, smt) = self.contract_inbound_lens.values().next().unwrap();
            return Some((term.clone(), smt.clone()));
        }
        let candidates: Vec<_> = self
            .contract_inbound_lens
            .iter()
            .filter(|(k, _)| origin_key.contains(k.as_str()) || k.contains(origin_key))
            .collect();
        if candidates.len() == 1 {
            let (term, smt) = candidates[0].1.clone();
            return Some((term, smt));
        }
        None
    }

    /// Fallback: when a struct field has an `InBound(place, T, len)` invariant
    /// from `#[rapx::invariant(…)]`, use the symbolic `len(origin)` term so
    /// that `pointer_bounds_for_place` can discover the allocation length and
    /// combine it with path conditions (e.g. `ValidNum(idx < self.len())`)
    /// to prove sub-range bounds for `.add(idx)` and similar pointer arithmetic.
    pub(crate) fn bounds_len_from_contract_fact(&mut self, origin_key: &str) -> Option<(Int<'ctx>, SmtTerm)> {
        for fact in &self.forward.facts {
            let StateFact::Contract(property) = fact else {
                continue;
            };
            if property.kind != PropertyKind::InBound {
                continue;
            }
            if let Some(target_place) = property
                .args
                .get(0)
                .and_then(|arg| {
                    if let PropertyArg::Place(place) = arg {
                        Some(place)
                    } else {
                        None
                    }
                })
            {
                let mut key = PlaceKey::from_contract_place(target_place);
                if let PlaceBaseKey::Arg(ix) = key.base {
                    key.base = PlaceBaseKey::Local(ix + 1);
                }
                let target_label = place_label(&key);
                if target_label == origin_key {
                    let len_key = format!("len({})", target_label);
                    let len_term = self.symbolic_len_term(&len_key);
                    let len_smt = SmtTerm::Value(len_key);
                    return Some((len_term, len_smt));
                }
            }
        }
        None
    }

    pub(crate) fn len_place_for_origin(&self, origin_key: &str) -> Option<PlaceKey> {
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

    pub(crate) fn allocated_len_for_origin(&self, origin_key: &str) -> Option<u64> {
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
    pub(crate) fn allocated_ty_via_known_fact(
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
    pub(crate) fn allocation_dropped_on_path(&self, object: &PlaceKey, alloc_place: &PlaceKey) -> bool {
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
    pub(crate) fn place_defined_by_pointer_arith(&self, place: &PlaceKey) -> bool {
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
    pub(crate) fn allocation_freed_by_owner_drop(&self, object: &PlaceKey) -> bool {
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
    pub(crate) fn allocated_bounds_via_points_to(
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

    pub(crate) fn origin_is_initialized_for_ty(&self, origin_key: &str, required_ty_name: &str) -> bool {
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

    pub(crate) fn initialized_element_ty_for_place(&self, place: &PlaceKey) -> Option<String> {
        let ty = self.place_ty(place)?;
        initialized_element_ty_name(ty)
    }
}
