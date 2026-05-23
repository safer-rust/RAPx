//! Backward evidence data model for the staged verifier.
//!
//! This module defines the structures used by the future backward evidence
//! reducer.  It also provides property-root extraction without making the
//! contract layer depend on the evidence layer.

use rustc_data_structures::fx::FxHashSet;
use rustc_middle::mir::{
    BasicBlock, Local, Operand, Place, ProjectionElem, Rvalue, Statement, StatementKind,
    Terminator, TerminatorKind,
};
use rustc_middle::ty::TyCtxt;

use super::{
    contract::{
        ContractExpr, ContractPlace, ContractProjection, NumericPredicate, PlaceBase, Property,
        PropertyArg, PropertyKind,
    },
    helpers::{Callsite, CallsiteLocation},
    path::{Path, PathStep},
};

/// Entry point for future backward evidence reduction.
pub struct EvidenceReducer<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> EvidenceReducer<'tcx> {
    /// Create an evidence reducer over the current compiler type context.
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self { tcx }
    }

    /// Return the compiler type context owned by this reducer.
    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    /// Build the initial reduced-evidence object for a path and property.
    pub fn seed(
        &self,
        callsite: CallsiteLocation,
        path: &Path,
        property: &Property<'tcx>,
    ) -> ReducedEvidence<'tcx> {
        ReducedEvidence {
            callsite,
            property: property.clone(),
            path: path.clone(),
            items: Vec::new(),
            roots: RelevanceSet::from_property(property),
        }
    }

    /// Reduce one `(callsite, path, property)` item to path-specific evidence.
    ///
    /// The reducer walks the path backward from the unsafe callsite, starting
    /// from the roots mentioned by the required property.  Statements defining
    /// relevant locals are retained and their uses become the next relevance
    /// frontier.  Relevant branch conditions, calls, drops, and loop exits are
    /// retained as conservative evidence for later replay.
    pub fn reduce(
        &self,
        callsite: &Callsite<'tcx>,
        path: &Path,
        property: &Property<'tcx>,
    ) -> ReducedEvidence<'tcx> {
        let mut evidence = self.seed(callsite.location(), path, property);
        bind_callsite_roots(&mut evidence.roots, callsite);

        let mut relevant = evidence.roots.clone();
        let mut items = Vec::new();
        let body = self.tcx.optimized_mir(callsite.caller);

        for step in path.steps.iter().rev() {
            match step {
                PathStep::Callsite(location) => {
                    if *location != callsite.location() {
                        continue;
                    }
                    items.push(EvidenceItem::Terminator {
                        block: location.block,
                        kind: EvidenceKind::Callsite,
                    });
                }
                PathStep::Block(block) => {
                    let block_data = &body.basic_blocks[*block];
                    if *block != callsite.block {
                        self.reduce_terminator(
                            *block,
                            block_data.terminator(),
                            &mut relevant,
                            &mut items,
                        );
                    }
                    for (statement_index, statement) in
                        block_data.statements.iter().enumerate().rev()
                    {
                        self.reduce_statement(
                            *block,
                            statement_index,
                            statement,
                            &mut relevant,
                            &mut items,
                        );
                    }
                }
                PathStep::LoopExit { .. } => {
                    items.push(EvidenceItem::Havoc {
                        reason: HavocReason::LoopWithoutSummary,
                    });
                    items.push(EvidenceItem::PathStep {
                        step: step.clone(),
                        kind: EvidenceKind::LoopSummary,
                    });
                }
            }
        }

        items.reverse();
        evidence.items = items;
        evidence
    }

    /// Reduce one MIR statement against the current relevance frontier.
    fn reduce_statement(
        &self,
        block: BasicBlock,
        statement_index: usize,
        statement: &Statement<'tcx>,
        relevant: &mut RelevanceSet,
        items: &mut Vec<EvidenceItem<'tcx>>,
    ) {
        let use_def = statement_use_def(statement);
        if use_def.defs.intersects(relevant) {
            items.push(EvidenceItem::Statement {
                block,
                statement_index,
                kind: statement_evidence_kind(statement),
            });
            relevant.remove_all(&use_def.defs);
            relevant.extend(use_def.uses);
            return;
        }

        if statement_invalidates_relevant(statement, relevant) {
            items.push(EvidenceItem::Statement {
                block,
                statement_index,
                kind: EvidenceKind::Invalidation,
            });
        } else if use_def.uses.intersects(relevant) && statement_can_refine(statement) {
            items.push(EvidenceItem::Statement {
                block,
                statement_index,
                kind: EvidenceKind::RuntimeCheck,
            });
        }
    }

    /// Reduce one MIR terminator against the current relevance frontier.
    fn reduce_terminator(
        &self,
        block: BasicBlock,
        terminator: &Terminator<'tcx>,
        relevant: &mut RelevanceSet,
        items: &mut Vec<EvidenceItem<'tcx>>,
    ) {
        let use_def = terminator_use_def(terminator);
        if use_def.defs.intersects(relevant) {
            if terminator_may_havoc(terminator) {
                items.push(EvidenceItem::Havoc {
                    reason: HavocReason::UnknownCall,
                });
            }
            items.push(EvidenceItem::Terminator {
                block,
                kind: terminator_definition_kind(terminator),
            });
            relevant.remove_all(&use_def.defs);
            relevant.extend(use_def.uses);
            return;
        }

        if use_def.uses.intersects(relevant) {
            if terminator_may_havoc(terminator) {
                items.push(EvidenceItem::Havoc {
                    reason: HavocReason::UnknownCall,
                });
            }
            items.push(EvidenceItem::Terminator {
                block,
                kind: terminator_use_kind(terminator),
            });
        }
    }
}

/// Definitions and uses collected from one MIR item.
#[derive(Clone, Debug, Default)]
pub struct UseDef {
    /// Places defined or invalidated by the MIR item.
    pub defs: RelevanceSet,
    /// Places read by the MIR item.
    pub uses: RelevanceSet,
}

impl UseDef {
    /// Create an empty use-def summary.
    pub fn new() -> Self {
        Self::default()
    }
}

/// Reduced evidence retained for one `(callsite, path, property)` item.
#[derive(Clone, Debug)]
pub struct ReducedEvidence<'tcx> {
    /// Unsafe callsite whose obligation is being checked.
    pub callsite: CallsiteLocation,
    /// Required property that determines the relevance roots.
    pub property: Property<'tcx>,
    /// Path being reduced.
    pub path: Path,
    /// Evidence retained from the path.
    pub items: Vec<EvidenceItem<'tcx>>,
    /// Initial roots extracted from the property.
    pub roots: RelevanceSet,
}

impl<'tcx> ReducedEvidence<'tcx> {
    /// Append one evidence item to the reduced path.
    pub fn push(&mut self, item: EvidenceItem<'tcx>) {
        self.items.push(item);
    }

    /// Return true when no MIR/path evidence has been retained yet.
    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }
}

/// One retained evidence item from a path.
#[derive(Clone, Debug)]
pub enum EvidenceItem<'tcx> {
    /// A MIR statement retained from a basic block.
    Statement {
        block: BasicBlock,
        statement_index: usize,
        kind: EvidenceKind,
    },
    /// A MIR terminator retained from a basic block.
    Terminator {
        block: BasicBlock,
        kind: EvidenceKind,
    },
    /// A path-level step retained as structural evidence.
    PathStep { step: PathStep, kind: EvidenceKind },
    /// A contract fact retained as evidence.
    ContractFact { property: Property<'tcx> },
    /// A conservative loss of precision for relevant state.
    Havoc { reason: HavocReason },
}

/// Why a retained item is relevant.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum EvidenceKind {
    /// The item defines a relevant place.
    Definition,
    /// The item contributes a branch/path condition.
    PathCondition,
    /// The item contributes pointer provenance or pointer arithmetic.
    PointerProvenance,
    /// The item refines state through a runtime check.
    RuntimeCheck,
    /// The item is the unsafe callsite being checked.
    Callsite,
    /// The item represents a loop summary or loop exit.
    LoopSummary,
    /// The item may invalidate a relevant fact.
    Invalidation,
    /// The item may affect relevant state but is not modeled precisely yet.
    UnknownRelevantEffect,
}

/// Reason for conservatively forgetting relevant state.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum HavocReason {
    /// A call may modify relevant state but has no summary yet.
    UnknownCall,
    /// A loop may modify relevant state but has no summary yet.
    LoopWithoutSummary,
    /// A write may alias relevant state.
    MayAliasWrite,
    /// A relevant statement or terminator is not supported yet.
    UnsupportedEffect,
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

/// Set of roots that can make MIR evidence relevant.
#[derive(Clone, Debug, Default)]
pub struct RelevanceSet {
    /// Contract-level places, including callee arguments before binding.
    pub places: FxHashSet<PlaceKey>,
    /// MIR locals that are already known from local contract places.
    pub locals: FxHashSet<Local>,
}

impl RelevanceSet {
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
    pub fn extend(&mut self, other: RelevanceSet) {
        self.places.extend(other.places);
        self.locals.extend(other.locals);
    }

    /// Return true if this set shares any known root with `other`.
    pub fn intersects(&self, other: &RelevanceSet) -> bool {
        self.locals.iter().any(|local| other.locals.contains(local))
            || self.places.iter().any(|place| other.places.contains(place))
    }

    /// Remove all roots contained in `other` from this set.
    pub fn remove_all(&mut self, other: &RelevanceSet) {
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
    ///
    /// The bundled std contract database currently uses strings such as `"0"`
    /// for "callee argument 0".  The generic contract parser treats that as a
    /// numeric constant.  For properties whose first argument is a target place,
    /// this helper recovers the intended argument root without changing the
    /// contract layer.
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
fn bind_callsite_roots(relevance: &mut RelevanceSet, callsite: &Callsite<'_>) {
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

/// Collect definitions and uses for one MIR statement.
fn statement_use_def<'tcx>(statement: &Statement<'tcx>) -> UseDef {
    let mut use_def = UseDef::new();
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
fn terminator_use_def<'tcx>(terminator: &Terminator<'tcx>) -> UseDef {
    let mut use_def = UseDef::new();
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

/// Collect all MIR roots used by an rvalue.
fn rvalue_uses<'tcx>(rvalue: &Rvalue<'tcx>) -> RelevanceSet {
    let mut uses = RelevanceSet::new();
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
fn operand_uses<'tcx>(operand: &Operand<'tcx>) -> RelevanceSet {
    let mut uses = RelevanceSet::new();
    match operand {
        Operand::Copy(place) | Operand::Move(place) => {
            uses.extend(place_uses(place));
        }
        Operand::Constant(_) => {}
    }
    uses
}

/// Collect the base and projection-index roots used by a MIR place.
fn place_uses(place: &Place<'_>) -> RelevanceSet {
    let mut uses = RelevanceSet::new();
    uses.insert_mir_place(place);
    uses.extend(place_projection_uses(place));
    uses
}

/// Collect only the index roots used by a place projection.
fn place_projection_uses(place: &Place<'_>) -> RelevanceSet {
    let mut uses = RelevanceSet::new();
    for projection in place.projection {
        if let ProjectionElem::Index(local) = projection {
            uses.insert_local(local);
        }
    }
    uses
}

/// Classify a retained statement by the kind of evidence it contributes.
fn statement_evidence_kind(statement: &Statement<'_>) -> EvidenceKind {
    match &statement.kind {
        StatementKind::Assign(box (_, rvalue)) => match rvalue {
            Rvalue::Ref(_, _, _)
            | Rvalue::RawPtr(_, _)
            | Rvalue::Cast(_, _, _)
            | Rvalue::CopyForDeref(_)
            | Rvalue::BinaryOp(_, _) => EvidenceKind::PointerProvenance,
            _ => EvidenceKind::Definition,
        },
        StatementKind::StorageDead(_) => EvidenceKind::Invalidation,
        _ => EvidenceKind::Definition,
    }
}

/// Return true if a statement may refine facts about a relevant root.
fn statement_can_refine(statement: &Statement<'_>) -> bool {
    matches!(
        &statement.kind,
        StatementKind::Assign(box (
            _,
            Rvalue::BinaryOp(_, _) | Rvalue::UnaryOp(_, _) | Rvalue::Cast(_, _, _),
        ))
    )
}

/// Return true if a statement invalidates currently relevant state.
fn statement_invalidates_relevant(statement: &Statement<'_>, relevant: &RelevanceSet) -> bool {
    match &statement.kind {
        StatementKind::StorageDead(local) => relevant.locals.contains(local),
        _ => false,
    }
}

/// Classify a retained terminator that defines a relevant place.
fn terminator_definition_kind(terminator: &Terminator<'_>) -> EvidenceKind {
    match terminator.kind {
        TerminatorKind::Call { .. } => EvidenceKind::UnknownRelevantEffect,
        _ => EvidenceKind::Definition,
    }
}

/// Classify a retained terminator that uses a relevant place.
fn terminator_use_kind(terminator: &Terminator<'_>) -> EvidenceKind {
    match terminator.kind {
        TerminatorKind::SwitchInt { .. } | TerminatorKind::Assert { .. } => {
            EvidenceKind::PathCondition
        }
        TerminatorKind::Drop { .. } => EvidenceKind::Invalidation,
        TerminatorKind::Call { .. } => EvidenceKind::UnknownRelevantEffect,
        _ => EvidenceKind::UnknownRelevantEffect,
    }
}

/// Return true if a terminator has an unsupported relevant side effect.
fn terminator_may_havoc(terminator: &Terminator<'_>) -> bool {
    matches!(terminator.kind, TerminatorKind::Call { .. })
}
