//! Backward evidence data model for the staged verifier.
//!
//! This module defines the structures used by the future backward evidence
//! reducer.  It also provides property-root extraction without making the
//! contract layer depend on the evidence layer.

use rustc_data_structures::fx::FxHashSet;
use rustc_middle::mir::{BasicBlock, Local};
use rustc_middle::ty::TyCtxt;

use super::{
    contract::{
        ContractExpr, ContractPlace, ContractProjection, NumericPredicate, PlaceBase, Property,
        PropertyArg, PropertyKind,
    },
    helpers::CallsiteLocation,
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
    ///
    /// This is intentionally a lightweight stub for the next phase: it records
    /// the property roots but does not yet walk MIR statements.  Step 3 will
    /// replace the empty `items` vector with the actual backward slice.
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
