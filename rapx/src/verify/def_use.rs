//! Def-use computation for the backward path visitor.
//!
//! These types and helpers track which MIR places are relevant to a safety
//! property and compute definitions/uses from MIR statements and terminators.
//! This is the data layer that `path_refine` drives block-by-block along a
//! finite verification path; keeping it separate lets the core visit logic stay
//! focused on path-level decisions (calls, SCC exits, path conditions).

use rustc_data_structures::fx::FxHashSet;
use rustc_middle::mir::{
    Local, Operand, Place, ProjectionElem, Rvalue, Statement, StatementKind, Terminator,
    TerminatorKind,
};
use rustc_span::source_map::Spanned;

use super::{
    contract::{
        ContractExpr, ContractPlace, ContractProjection, NumericPredicate, PlaceBase, Property,
        PropertyArg, PropertyKind,
    },
    helpers::Callsite,
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

    /// Return true if this set shares any known root with `other`.
    pub fn intersects(&self, other: &RelevantPlaces) -> bool {
        self.locals.iter().any(|local| other.locals.contains(local))
            || self.places.iter().any(|place| other.places.contains(place))
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

/// Bind callee-argument roots in std contracts to concrete MIR call operands.
pub fn bind_callsite_roots(relevance: &mut RelevantPlaces, callsite: &Callsite<'_>) {
    let argument_roots: Vec<usize> = relevance
        .places
        .iter()
        .filter_map(|place| match place.base {
            PlaceBaseKey::Arg(index) => Some(index),
            _ => None,
        })
        .collect();

    for index in argument_roots {
        if let Some(operand) = callsite.args.get(index) {
            relevance.extend(operand_uses(operand));
        }
    }
}

// ── def-use extraction from MIR ────────────────────────────────────────

/// Collect definitions and uses for one MIR statement.
pub fn statement_use_def<'tcx>(statement: &Statement<'tcx>) -> DefUse {
    let mut use_def = DefUse::new();
    match &statement.kind {
        StatementKind::Assign(box (place, rvalue)) => {
            use_def.defs.insert_mir_place(place);
            use_def.uses.extend(place_projection_uses(place));
            use_def.uses.extend(rvalue_uses(rvalue));
        }
        StatementKind::StorageDead(local) => {
            use_def.defs.insert_local(*local);
        }
        StatementKind::StorageLive(_) => {}
        _ => {}
    }
    use_def
}

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

/// Collect all MIR roots used by call arguments.
pub fn call_args_uses<'tcx>(args: &[Spanned<Operand<'tcx>>]) -> RelevantPlaces {
    let mut uses = RelevantPlaces::new();
    for arg in args {
        uses.extend(operand_uses(&arg.node));
    }
    uses
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

/// Collect all MIR roots used by an rvalue.
pub fn rvalue_uses<'tcx>(rvalue: &Rvalue<'tcx>) -> RelevantPlaces {
    let mut uses = RelevantPlaces::new();
    match rvalue {
        Rvalue::Use(operand)
        | Rvalue::Repeat(operand, _)
        | Rvalue::UnaryOp(_, operand)
        | Rvalue::Cast(_, operand, _)
        | Rvalue::ShallowInitBox(operand, _) => {
            uses.extend(operand_uses(operand));
        }
        Rvalue::BinaryOp(_, box (lhs, rhs)) => {
            uses.extend(operand_uses(lhs));
            uses.extend(operand_uses(rhs));
        }
        Rvalue::Ref(_, _, place)
        | Rvalue::RawPtr(_, place)
        | Rvalue::CopyForDeref(place)
        | Rvalue::Discriminant(place) => {
            uses.extend(place_uses(place));
        }
        Rvalue::Aggregate(_, operands) => {
            for operand in operands {
                uses.extend(operand_uses(operand));
            }
        }
        Rvalue::NullaryOp(_) | Rvalue::ThreadLocalRef(_) => {}
        _ => {}
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
