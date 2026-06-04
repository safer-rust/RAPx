//! Backward path visitor for the staged verifier.
//!
//! This module walks a finite path backward from an unsafe callsite and keeps
//! only MIR statements, terminators, and path steps that can affect the required
//! property. It also extracts property roots without making the contract layer
//! depend on the backward visitor.

use std::fmt::Write;

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

/// Entry point for backward path visiting.
pub struct BackwardVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> BackwardVisitor<'tcx> {
    /// Create a backward visitor over the current compiler type context.
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self { tcx }
    }

    /// Return the compiler type context owned by this visitor.
    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    /// Build the initial relevant-MIR item set for a path and property.
    pub fn start_visit(
        &self,
        callsite: CallsiteLocation,
        path: &Path,
        property: &Property<'tcx>,
    ) -> RelevantMirItems<'tcx> {
        RelevantMirItems {
            callsite,
            property: property.clone(),
            path: path.clone(),
            items: Vec::new(),
            roots: RelevantPlaces::from_property(property),
        }
    }

    /// Visit one `(callsite, path, property)` item backward.
    ///
    /// The visitor walks the path backward from the unsafe callsite, starting
    /// from the roots mentioned by the required property.  Statements defining
    /// relevant locals are retained and their uses become the next relevance
    /// frontier.  Relevant branch conditions, calls, drops, and loop exits are
    /// retained as conservative inputs for later forward visits.
    pub fn visit(
        &self,
        callsite: &Callsite<'tcx>,
        path: &Path,
        property: &Property<'tcx>,
    ) -> RelevantMirItems<'tcx> {
        let mut visit = self.start_visit(callsite.location(), path, property);
        bind_callsite_roots(&mut visit.roots, callsite);

        let mut relevant = visit.roots.clone();
        let mut items = Vec::new();
        let body = self.tcx.optimized_mir(callsite.caller);

        for step in path.steps.iter().rev() {
            self.visit_path_step(step, callsite, &body, &mut relevant, &mut items);
        }

        for step in path.entry_prefix.iter().rev() {
            self.visit_path_step(step, callsite, &body, &mut relevant, &mut items);
        }

        items.reverse();
        visit.items = items;
        visit
    }

    /// Visit one path step against the current relevance frontier.
    fn visit_path_step(
        &self,
        step: &PathStep,
        callsite: &Callsite<'tcx>,
        body: &rustc_middle::mir::Body<'tcx>,
        relevant: &mut RelevantPlaces,
        items: &mut Vec<BackwardItem<'tcx>>,
    ) {
        match step {
            PathStep::Callsite(location) => {
                if *location != callsite.location() {
                    return;
                }
                items.push(BackwardItem::Terminator {
                    block: location.block,
                    kind: KeepReason::Callsite,
                });
            }
            PathStep::Block(block) => {
                let block_data = &body.basic_blocks[*block];
                if *block != callsite.block {
                    self.visit_terminator(*block, block_data.terminator(), relevant, items);
                }
                for (statement_index, statement) in block_data.statements.iter().enumerate().rev() {
                    self.visit_statement(*block, statement_index, statement, relevant, items);
                }
            }
            PathStep::SccExit { .. } => {
                items.push(BackwardItem::Forget {
                    reason: ForgetReason::SccWithoutSummary,
                });
                items.push(BackwardItem::PathStep {
                    step: step.clone(),
                    kind: KeepReason::LoopExit,
                });
            }
        }
    }

    /// Visit one MIR statement against the current relevance frontier.
    fn visit_statement(
        &self,
        block: BasicBlock,
        statement_index: usize,
        statement: &Statement<'tcx>,
        relevant: &mut RelevantPlaces,
        items: &mut Vec<BackwardItem<'tcx>>,
    ) {
        let use_def = statement_use_def(statement);
        if use_def.defs.intersects(relevant) {
            items.push(BackwardItem::Statement {
                block,
                statement_index,
                kind: statement_keep_reason(statement),
            });
            relevant.remove_all(&use_def.defs);
            relevant.extend(use_def.uses);
            return;
        }

        if statement_invalidates_relevant(statement, relevant) {
            items.push(BackwardItem::Statement {
                block,
                statement_index,
                kind: KeepReason::Invalidation,
            });
        } else if use_def.uses.intersects(relevant) && statement_can_refine(statement) {
            items.push(BackwardItem::Statement {
                block,
                statement_index,
                kind: KeepReason::RuntimeCheck,
            });
        }
    }

    /// Visit one MIR terminator against the current relevance frontier.
    fn visit_terminator(
        &self,
        block: BasicBlock,
        terminator: &Terminator<'tcx>,
        relevant: &mut RelevantPlaces,
        items: &mut Vec<BackwardItem<'tcx>>,
    ) {
        let use_def = terminator_use_def(terminator);
        if use_def.defs.intersects(relevant) {
            if terminator_may_havoc(terminator) {
                items.push(BackwardItem::Forget {
                    reason: ForgetReason::UnknownCall,
                });
            }
            items.push(BackwardItem::Terminator {
                block,
                kind: terminator_definition_reason(terminator),
            });
            relevant.remove_all(&use_def.defs);
            relevant.extend(use_def.uses);
            return;
        }

        if use_def.uses.intersects(relevant) {
            if terminator_may_havoc(terminator) {
                items.push(BackwardItem::Forget {
                    reason: ForgetReason::UnknownCall,
                });
            }
            items.push(BackwardItem::Terminator {
                block,
                kind: terminator_use_reason(terminator),
            });
        }
    }
}

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

/// MIR items relevant to one `(callsite, path, property)` item.
#[derive(Clone, Debug)]
pub struct RelevantMirItems<'tcx> {
    /// Unsafe callsite whose obligation is being checked.
    pub callsite: CallsiteLocation,
    /// Required property that determines the relevance roots.
    pub property: Property<'tcx>,
    /// Path being visited.
    pub path: Path,
    /// Items kept from the path.
    pub items: Vec<BackwardItem<'tcx>>,
    /// Initial roots extracted from the property.
    pub roots: RelevantPlaces,
}

impl<'tcx> RelevantMirItems<'tcx> {
    /// Append one kept item to the visited path.
    pub fn push(&mut self, item: BackwardItem<'tcx>) {
        self.items.push(item);
    }

    /// Return true when no MIR/path item has been kept yet.
    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    /// Render a detailed, path-ordered diagnostic for the relevant MIR items.
    pub fn describe(
        &self,
        tcx: TyCtxt<'tcx>,
        callsite: &Callsite<'tcx>,
        path_index: usize,
    ) -> String {
        let mut out = String::new();
        let body = tcx.optimized_mir(self.callsite.caller);
        let _ = writeln!(
            out,
            "      callsite: {} at bb{}",
            callsite.callee_name(tcx),
            callsite.block.as_usize()
        );
        let _ = writeln!(
            out,
            "      property: kind={:?}, args={:?}",
            self.property.kind, self.property.args
        );
        let _ = writeln!(out, "      path {path_index}:");
        let _ = writeln!(
            out,
            "        |_ kind: {}",
            describe_path_start(&self.path.start)
        );
        if self.path.entry_prefix.is_empty() {
            let _ = writeln!(out, "        |_ steps: {}", self.path.describe_body());
        } else {
            let _ = writeln!(
                out,
                "        |_ entry prefix: {}",
                self.path.describe_entry_prefix()
            );
            let _ = writeln!(out, "        |_ loop body: {}", self.path.describe_body());
        }
        let _ = writeln!(
            out,
            "        |_ roots: {} place(s), {} local(s)",
            self.roots.place_count(),
            self.roots.local_count()
        );
        let _ = writeln!(out, "      relevant MIR items:");

        let mut has_relevant_item = false;
        for step in self.path.entry_prefix.iter().chain(self.path.steps.iter()) {
            let step_items: Vec<_> = self
                .items
                .iter()
                .filter(|item| item_belongs_to_step(item, step))
                .collect();
            if step_items.is_empty() {
                continue;
            }
            has_relevant_item = true;

            let _ = writeln!(out, "        |_ {}", describe_path_step(step));
            for item in step_items {
                let _ = writeln!(out, "        |  |_ {}", describe_backward_item(item, body));
            }
        }
        if !has_relevant_item {
            let _ = writeln!(out, "        |_ <none>");
        }

        let forgets: Vec<_> = self
            .items
            .iter()
            .filter_map(|item| match item {
                BackwardItem::Forget { reason } => Some(reason),
                _ => None,
            })
            .collect();
        if !forgets.is_empty() {
            let _ = writeln!(out, "      precision loss:");
            for reason in forgets {
                let _ = writeln!(out, "        |_ {}", describe_forget_reason(reason));
            }
        }

        out
    }
}

/// One item kept while walking a path backward.
#[derive(Clone, Debug)]
pub enum BackwardItem<'tcx> {
    /// A MIR statement retained from a basic block.
    Statement {
        block: BasicBlock,
        statement_index: usize,
        kind: KeepReason,
    },
    /// A MIR terminator retained from a basic block.
    Terminator { block: BasicBlock, kind: KeepReason },
    /// A path-level step retained as structural context.
    PathStep { step: PathStep, kind: KeepReason },
    /// A contract fact retained as a visit input.
    ContractFact { property: Property<'tcx> },
    /// A conservative loss of precision for relevant state.
    Forget { reason: ForgetReason },
}

/// Why a retained item is relevant.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum KeepReason {
    /// The item defines a relevant place.
    Definition,
    /// The item contributes a branch/path condition.
    PathCondition,
    /// The item contributes pointer provenance or pointer arithmetic.
    PointerFlow,
    /// The item refines state through a runtime check.
    RuntimeCheck,
    /// The item is the unsafe callsite being checked.
    Callsite,
    /// The item represents a loop summary or loop exit.
    LoopExit,
    /// The item may invalidate a relevant fact.
    Invalidation,
    /// The item may affect relevant state but is not modeled precisely yet.
    UnknownEffect,
}

/// Reason for conservatively forgetting relevant state.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ForgetReason {
    /// A call may modify relevant state but has no summary yet.
    UnknownCall,
    /// An SCC region may modify relevant state but has no summary yet.
    SccWithoutSummary,
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
fn bind_callsite_roots(relevance: &mut RelevantPlaces, callsite: &Callsite<'_>) {
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
fn statement_use_def<'tcx>(statement: &Statement<'tcx>) -> DefUse {
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
fn terminator_use_def<'tcx>(terminator: &Terminator<'tcx>) -> DefUse {
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

/// Collect all MIR roots used by an rvalue.
fn rvalue_uses<'tcx>(rvalue: &Rvalue<'tcx>) -> RelevantPlaces {
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
fn operand_uses<'tcx>(operand: &Operand<'tcx>) -> RelevantPlaces {
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
fn place_uses(place: &Place<'_>) -> RelevantPlaces {
    let mut uses = RelevantPlaces::new();
    uses.insert_mir_place(place);
    uses.extend(place_projection_uses(place));
    uses
}

/// Collect only the index roots used by a place projection.
fn place_projection_uses(place: &Place<'_>) -> RelevantPlaces {
    let mut uses = RelevantPlaces::new();
    for projection in place.projection {
        if let ProjectionElem::Index(local) = projection {
            uses.insert_local(local);
        }
    }
    uses
}

/// Classify why a backward visit keeps a statement.
fn statement_keep_reason(statement: &Statement<'_>) -> KeepReason {
    match &statement.kind {
        StatementKind::Assign(box (_, rvalue)) => match rvalue {
            Rvalue::Ref(_, _, _)
            | Rvalue::RawPtr(_, _)
            | Rvalue::Cast(_, _, _)
            | Rvalue::CopyForDeref(_)
            | Rvalue::BinaryOp(_, _) => KeepReason::PointerFlow,
            _ => KeepReason::Definition,
        },
        StatementKind::StorageDead(_) => KeepReason::Invalidation,
        _ => KeepReason::Definition,
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
fn statement_invalidates_relevant(statement: &Statement<'_>, relevant: &RelevantPlaces) -> bool {
    match &statement.kind {
        StatementKind::StorageDead(local) => relevant.locals.contains(local),
        _ => false,
    }
}

/// Classify a retained terminator that defines a relevant place.
fn terminator_definition_reason(terminator: &Terminator<'_>) -> KeepReason {
    match terminator.kind {
        TerminatorKind::Call { .. } => KeepReason::UnknownEffect,
        _ => KeepReason::Definition,
    }
}

/// Classify a retained terminator that uses a relevant place.
fn terminator_use_reason(terminator: &Terminator<'_>) -> KeepReason {
    match terminator.kind {
        TerminatorKind::SwitchInt { .. } | TerminatorKind::Assert { .. } => {
            KeepReason::PathCondition
        }
        TerminatorKind::Drop { .. } => KeepReason::Invalidation,
        TerminatorKind::Call { .. } => KeepReason::UnknownEffect,
        _ => KeepReason::UnknownEffect,
    }
}

/// Return true if a terminator has an unsupported relevant side effect.
fn terminator_may_havoc(terminator: &Terminator<'_>) -> bool {
    matches!(terminator.kind, TerminatorKind::Call { .. })
}

/// Return true when a kept item belongs under a path step in diagnostics.
fn item_belongs_to_step(item: &BackwardItem<'_>, step: &PathStep) -> bool {
    match (item, step) {
        (BackwardItem::Statement { block, .. }, PathStep::Block(step_block)) => block == step_block,
        (BackwardItem::Terminator { block, kind }, PathStep::Block(step_block)) => {
            block == step_block && *kind != KeepReason::Callsite
        }
        (BackwardItem::Terminator { block, kind }, PathStep::Callsite(location)) => {
            *kind == KeepReason::Callsite && *block == location.block
        }
        (
            BackwardItem::PathStep {
                step: item_step, ..
            },
            step,
        ) => same_path_step(item_step, step),
        _ => false,
    }
}

/// Return true when two path steps describe the same path position.
fn same_path_step(lhs: &PathStep, rhs: &PathStep) -> bool {
    match (lhs, rhs) {
        (PathStep::Block(lhs), PathStep::Block(rhs)) => lhs == rhs,
        (
            PathStep::SccExit {
                representative: lhs_representative,
                from: lhs_from,
                to: lhs_to,
            },
            PathStep::SccExit {
                representative: rhs_representative,
                from: rhs_from,
                to: rhs_to,
            },
        ) => lhs_representative == rhs_representative && lhs_from == rhs_from && lhs_to == rhs_to,
        (PathStep::Callsite(lhs), PathStep::Callsite(rhs)) => lhs == rhs,
        _ => false,
    }
}

/// Render a compact path start label.
fn describe_path_start(start: &super::path::PathStart) -> String {
    match start {
        super::path::PathStart::FunctionEntry => "entry".to_string(),
        super::path::PathStart::SccRepresentative { representative } => {
            format!("scc-representative(bb{})", representative.as_usize())
        }
    }
}

/// Render a compact path step label.
fn describe_path_step(step: &PathStep) -> String {
    match step {
        PathStep::Block(block) => format!("bb{}", block.as_usize()),
        PathStep::SccExit {
            representative,
            from,
            to,
        } => format!(
            "SccRegion(bb{}).exit(bb{} -> bb{})",
            representative.as_usize(),
            from.as_usize(),
            to.as_usize()
        ),
        PathStep::Callsite(location) => format!("callsite(bb{})", location.block.as_usize()),
    }
}

/// Render one kept backward item with the original MIR attached.
fn describe_backward_item(item: &BackwardItem<'_>, body: &rustc_middle::mir::Body<'_>) -> String {
    match item {
        BackwardItem::Statement {
            block,
            statement_index,
            kind,
            ..
        } => {
            let statement = &body.basic_blocks[*block].statements[*statement_index];
            format!("stmt#{} [{:?}] {:?}", statement_index, kind, statement.kind)
        }
        BackwardItem::Terminator { block, kind } => {
            let terminator = body.basic_blocks[*block].terminator();
            format!("terminator [{:?}] {:?}", kind, terminator.kind)
        }
        BackwardItem::PathStep { kind, .. } => format!("path-step {:?}", kind),
        BackwardItem::ContractFact { property } => {
            format!(
                "contract kind={:?}, args={:?}",
                property.kind, property.args
            )
        }
        BackwardItem::Forget { reason } => format!("forget {:?}", reason),
    }
}

/// Explain why relevant facts were conservatively forgotten.
fn describe_forget_reason(reason: &ForgetReason) -> &'static str {
    match reason {
        ForgetReason::UnknownCall => {
            "UnknownCall: a retained call may affect relevant state and has no summary yet"
        }
        ForgetReason::SccWithoutSummary => {
            "SccWithoutSummary: a relevant SCC exit has no verified SCC summary yet"
        }
        ForgetReason::MayAliasWrite => {
            "MayAliasWrite: a write may alias relevant state and is not modeled precisely yet"
        }
        ForgetReason::UnsupportedEffect => {
            "UnsupportedEffect: a relevant MIR effect is not modeled precisely yet"
        }
    }
}
