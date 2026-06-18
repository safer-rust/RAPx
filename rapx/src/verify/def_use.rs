//! Def-use computation for the backward path visitor.
//!
//! These types and helpers track which MIR places are relevant to a safety
//! property and compute definitions/uses from MIR terminators.
//! This is the data layer that `path_refine` drives block-by-block along a
//! finite verification path; keeping it separate lets the core visit logic stay
//! focused on path-level decisions (calls, SCC exits, path conditions).

use crate::compat::FxHashSet;
use crate::compat::Spanned;
use rustc_middle::mir::{
    Local, Operand, Place, ProjectionElem, Rvalue, Terminator, TerminatorKind,
};
use rustc_middle::ty::TyCtxt;

use super::{
    contract::{
        ContractExpr, ContractPlace, ContractProjection, NumericPredicate, PlaceBase, Property,
        PropertyArg, PropertyKind,
    },
    helpers::{Callsite, callee_param_index_for_local},
};

/// Definitions and uses collected from one MIR item.
#[derive(Clone, Debug, Default)]
pub struct DefUse {
    /// Places defined or invalidated by the MIR item.
    pub defs: RelevantPlaces,
    /// Places read by the MIR item.
    pub uses: RelevantPlaces,
}

impl DefUse {
    /// Create an empty use-def summary.
    pub fn new() -> Self {
        Self::default()
    }
}

/// Base of a contract/MIR place tracked by relevance.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum PlaceBaseKey {
    /// MIR return local `_0`.
    Return,
    /// MIR local by numeric index.
    Local(usize),
    /// Callee argument by index before callsite binding.
    Arg(usize),
}

/// Projection-insensitive enough place key for relevance tracking.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct PlaceKey {
    /// Base local/argument of the place.
    pub base: PlaceBaseKey,
    /// Field projections kept from the contract place.
    pub fields: Vec<usize>,
}

impl PlaceKey {
    /// Build a relevance place key from a parsed contract place.
    pub fn from_contract_place(place: &ContractPlace<'_>) -> Self {
        Self {
            base: match place.base {
                PlaceBase::Return => PlaceBaseKey::Return,
                PlaceBase::Arg(index) => PlaceBaseKey::Arg(index),
                PlaceBase::Local(local) => PlaceBaseKey::Local(local),
            },
            fields: place
                .projections
                .iter()
                .map(|projection| match projection {
                    ContractProjection::Field { index, .. } => *index,
                })
                .collect(),
        }
    }

    /// Build a relevance place key from a MIR place.
    pub fn from_mir_place(place: &Place<'_>) -> Self {
        Self {
            base: if place.local.as_usize() == 0 {
                PlaceBaseKey::Return
            } else {
                PlaceBaseKey::Local(place.local.as_usize())
            },
            fields: place
                .projection
                .iter()
                .filter_map(|projection| match projection {
                    ProjectionElem::Field(index, _) => Some(index.as_usize()),
                    _ => None,
                })
                .collect(),
        }
    }

    /// Return the MIR local represented by this key when it is already known.
    pub fn local(&self) -> Option<Local> {
        match self.base {
            PlaceBaseKey::Return => Some(Local::from_usize(0)),
            PlaceBaseKey::Local(local) => Some(Local::from_usize(local)),
            PlaceBaseKey::Arg(_) => None,
        }
    }

    /// Return true when this place shares a base-and-projection prefix with
    /// `other`.  Two places overlap when one of them is a shorter projection
    /// of the other (e.g. `[]` overlaps `[0]`, but `[0]` does not overlap
    /// `[1]`).
    pub fn overlaps(&self, other: &PlaceKey) -> bool {
        self.base == other.base && {
            let min_len = self.fields.len().min(other.fields.len());
            self.fields[..min_len] == other.fields[..min_len]
        }
    }
}

/// Set of places that make MIR items relevant to a property.
#[derive(Clone, Debug, Default)]
pub struct RelevantPlaces {
    /// Contract-level places, including callee arguments before binding.
    pub places: FxHashSet<PlaceKey>,
    /// MIR locals that are already known from local contract places.
    pub locals: FxHashSet<Local>,
}

impl RelevantPlaces {
    /// Create an empty relevance set.
    pub fn new() -> Self {
        Self::default()
    }

    /// Extract initial relevance roots from a required property.
    pub fn from_property(property: &Property<'_>) -> Self {
        let mut set = Self::new();
        set.collect_property(property);
        set
    }

    /// Return true when no roots have been collected.
    pub fn is_empty(&self) -> bool {
        self.places.is_empty() && self.locals.is_empty()
    }

    /// Return the number of contract-level places in this set.
    pub fn place_count(&self) -> usize {
        self.places.len()
    }

    /// Return the number of MIR locals in this set.
    pub fn local_count(&self) -> usize {
        self.locals.len()
    }

    /// Insert a MIR local as a relevance root.
    pub fn insert_local(&mut self, local: Local) {
        self.locals.insert(local);
        self.places.insert(PlaceKey {
            base: if local.as_usize() == 0 {
                PlaceBaseKey::Return
            } else {
                PlaceBaseKey::Local(local.as_usize())
            },
            fields: Vec::new(),
        });
    }

    /// Insert a MIR place as a relevance root.
    pub fn insert_mir_place(&mut self, place: &Place<'_>) {
        self.insert_place_key(PlaceKey::from_mir_place(place));
    }

    /// Insert a contract place as a relevance root.
    pub fn insert_contract_place(&mut self, place: &ContractPlace<'_>) {
        self.insert_place_key(PlaceKey::from_contract_place(place));
    }

    /// Insert a prebuilt place key as a relevance root.
    pub fn insert_place_key(&mut self, place: PlaceKey) {
        if let Some(local) = place.local() {
            self.locals.insert(local);
        }
        self.places.insert(place);
    }

    /// Merge another relevance set into this one.
    pub fn extend(&mut self, other: RelevantPlaces) {
        self.places.extend(other.places);
        self.locals.extend(other.locals);
    }

    /// Remove a list of place keys and rebuild the derived local set.
    pub fn remove_place_keys(&mut self, places: &[PlaceKey]) {
        for place in places {
            self.places.remove(place);
        }
        self.rebuild_locals();
    }

    /// Return true if this set shares any known root with `other`.
    pub fn intersects(&self, other: &RelevantPlaces) -> bool {
        self.places
            .iter()
            .any(|sp| other.places.iter().any(|op| sp.overlaps(op)))
    }

    /// Remove all roots contained in `other` from this set.
    pub fn remove_all(&mut self, other: &RelevantPlaces) {
        for local in &other.locals {
            self.locals.remove(local);
            self.places.retain(|place| place.local() != Some(*local));
        }
        for place in &other.places {
            self.places.remove(place);
            if let Some(local) = place.local() {
                self.locals.remove(&local);
            }
        }
    }

    fn rebuild_locals(&mut self) {
        self.locals = self.places.iter().filter_map(PlaceKey::local).collect();
    }

    /// Collect all roots mentioned by a property.
    fn collect_property(&mut self, property: &Property<'_>) {
        for (arg_index, arg) in property.args.iter().enumerate() {
            if self.collect_target_argument_root(&property.kind, arg_index, arg) {
                continue;
            }
            self.collect_property_arg(arg);
        }
    }

    /// Collect a numeric std-contract target argument as a callee argument root.
    fn collect_target_argument_root(
        &mut self,
        kind: &PropertyKind,
        arg_index: usize,
        arg: &PropertyArg<'_>,
    ) -> bool {
        if !is_target_argument_index(kind, arg_index) {
            return false;
        }
        let PropertyArg::Expr(ContractExpr::Const(value)) = arg else {
            return false;
        };
        let Ok(index) = usize::try_from(*value) else {
            return false;
        };
        self.insert_place_key(PlaceKey {
            base: PlaceBaseKey::Arg(index),
            fields: Vec::new(),
        });
        true
    }

    /// Collect all roots mentioned by a property argument.
    fn collect_property_arg(&mut self, arg: &PropertyArg<'_>) {
        match arg {
            PropertyArg::Place(place) => self.insert_contract_place(place),
            PropertyArg::Expr(expr) => self.collect_contract_expr(expr),
            PropertyArg::Predicates(predicates) => {
                for predicate in predicates {
                    self.collect_numeric_predicate(predicate);
                }
            }
            PropertyArg::Ty(_) | PropertyArg::Ident(_) => {}
        }
    }

    /// Collect all roots mentioned by a numeric predicate.
    fn collect_numeric_predicate(&mut self, predicate: &NumericPredicate<'_>) {
        self.collect_contract_expr(&predicate.lhs);
        self.collect_contract_expr(&predicate.rhs);
    }

    /// Collect all roots mentioned by a contract expression.
    fn collect_contract_expr(&mut self, expr: &ContractExpr<'_>) {
        match expr {
            ContractExpr::Place(place) => self.insert_contract_place(place),
            ContractExpr::Binary { lhs, rhs, .. } => {
                self.collect_contract_expr(lhs);
                self.collect_contract_expr(rhs);
            }
            ContractExpr::Unary { expr, .. } => self.collect_contract_expr(expr),
            ContractExpr::Const(_)
            | ContractExpr::SizeOf(_)
            | ContractExpr::AlignOf(_)
            | ContractExpr::Unknown => {}
        }
    }
}

/// Return whether an argument index is a target-place position for a property.
fn is_target_argument_index(kind: &PropertyKind, arg_index: usize) -> bool {
    match kind {
        PropertyKind::NonOverlap | PropertyKind::Alias => arg_index <= 1,
        PropertyKind::ValidNum | PropertyKind::Unknown => false,
        _ => arg_index == 0,
    }
}

/// Bind callee parameter roots to concrete MIR call operands.
pub fn bind_callsite_roots(
    tcx: TyCtxt<'_>,
    relevance: &mut RelevantPlaces,
    callsite: &Callsite<'_>,
) {
    let argument_roots: Vec<(PlaceKey, usize)> = relevance
        .places
        .iter()
        .filter_map(|place| match place.base {
            PlaceBaseKey::Arg(index) => Some((place.clone(), index)),
            PlaceBaseKey::Local(local) => callee_param_index_for_local(tcx, callsite.callee, local)
                .map(|index| (place.clone(), index)),
            _ => None,
        })
        .collect();

    let mut bound_roots = RelevantPlaces::new();
    let mut rebound_roots = Vec::new();
    for (root, index) in argument_roots {
        if let Some(operand) = callsite.args.get(index) {
            if let Some(place) = bind_operand_place(operand, &root.fields) {
                bound_roots.insert_place_key(place);
            } else {
                bound_roots.extend(operand_uses(operand));
            }
            rebound_roots.push(root);
        }
    }

    relevance.remove_place_keys(&rebound_roots);
    relevance.extend(bound_roots);
}

fn bind_operand_place(operand: &Operand<'_>, fields: &[usize]) -> Option<PlaceKey> {
    let mut place = match operand {
        Operand::Copy(place) | Operand::Move(place) => PlaceKey::from_mir_place(place),
        Operand::Constant(_) => return None,
        #[cfg(rapx_rustc_ge_196)]
        Operand::RuntimeChecks(_) => return None,
    };
    place.fields.extend(fields.iter().copied());
    Some(place)
}

// ── def-use extraction from MIR ────────────────────────────────────────

/// Collect definitions and uses for one MIR terminator.
pub fn terminator_use_def<'tcx>(terminator: &Terminator<'tcx>) -> DefUse {
    let mut use_def = DefUse::new();
    match &terminator.kind {
        TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } => {
            use_def.defs.insert_mir_place(destination);
            use_def.uses.extend(operand_uses(func));
            for arg in args {
                use_def.uses.extend(operand_uses(&arg.node));
            }
        }
        TerminatorKind::SwitchInt { discr, .. } => {
            use_def.uses.extend(operand_uses(discr));
        }
        TerminatorKind::Assert { cond, .. } => {
            use_def.uses.extend(operand_uses(cond));
        }
        TerminatorKind::Drop { place, .. } => {
            use_def.uses.extend(place_uses(place));
        }
        _ => {}
    }
    use_def
}

/// Collect MIR roots used by selected call argument indices.
pub fn call_args_uses_at<'tcx>(
    args: &[Spanned<Operand<'tcx>>],
    indices: &[usize],
) -> RelevantPlaces {
    let mut uses = RelevantPlaces::new();
    for index in indices {
        if let Some(arg) = args.get(*index) {
            uses.extend(operand_uses(&arg.node));
        }
    }
    uses
}

/// Collect all MIR roots used by an operand.
pub fn operand_uses<'tcx>(operand: &Operand<'tcx>) -> RelevantPlaces {
    let mut uses = RelevantPlaces::new();
    match operand {
        Operand::Copy(place) | Operand::Move(place) => {
            uses.extend(place_uses(place));
        }
        Operand::Constant(_) => {}
        #[cfg(rapx_rustc_ge_196)]
        Operand::RuntimeChecks(_) => {}
    }
    uses
}

/// Collect the base and projection-index roots used by a MIR place.
pub fn place_uses(place: &Place<'_>) -> RelevantPlaces {
    let mut uses = RelevantPlaces::new();
    uses.insert_mir_place(place);
    uses.extend(place_projection_uses(place));
    uses
}

/// Collect only the index roots used by a place projection.
pub fn place_projection_uses(place: &Place<'_>) -> RelevantPlaces {
    let mut uses = RelevantPlaces::new();
    for projection in place.projection {
        if let ProjectionElem::Index(local) = projection {
            uses.insert_local(local);
        }
    }
    uses
}

/// Collect all MIR operands referenced by an rvalue.
pub fn rvalue_operands<'tcx>(rvalue: &'tcx Rvalue<'tcx>) -> Vec<&'tcx Operand<'tcx>> {
    let mut operands = Vec::new();
    match rvalue {
        Rvalue::Use(op, ..)
        | Rvalue::Repeat(op, _)
        | Rvalue::Cast(_, op, _)
        | Rvalue::UnaryOp(_, op) => {
            operands.push(op);
        }
        Rvalue::BinaryOp(_, pair) => {
            let (lhs, rhs) = &**pair;
            operands.push(lhs);
            operands.push(rhs);
        }
        Rvalue::Ref(_, _, _) | Rvalue::RawPtr(_, _) => {}
        #[cfg(not(rapx_rustc_ge_196))]
        Rvalue::ShallowInitBox(_, _) => {}
        Rvalue::Discriminant(_)
        | Rvalue::CopyForDeref(_)
        | Rvalue::ThreadLocalRef(_)
        | Rvalue::Aggregate(_, _)
        | _ => {}
    }
    operands
}
