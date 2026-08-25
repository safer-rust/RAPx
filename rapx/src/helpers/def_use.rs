//! Def-use computation types and pure MIR helpers.
//!
//! These types (`PlaceKey`, `PlaceBaseKey`, `RelevantPlaces`, `DefUse`) track
//! which MIR places are relevant to an analysis and compute definitions/uses
//! from MIR terminators.  Shared between the verify module and other analysis
//! passes (points-to, etc.).

use crate::analysis::dataflow::types::DataflowGraph;
use crate::compat::FxHashSet;
use crate::compat::Spanned;
use rustc_middle::mir::{
    Local, Operand, Place, ProjectionElem, Rvalue, Terminator, TerminatorKind,
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
    /// Callee argument by index before checkpoint binding.
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

    /// Build a PlaceKey from an analysis-level `(origin_local, fields)` tuple.
    pub fn from_origin(local: usize, fields: Vec<usize>) -> Self {
        Self {
            base: PlaceBaseKey::Local(local),
            fields,
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
    pub places: FxHashSet<PlaceKey>,
    pub locals: FxHashSet<Local>,
    pub saturated: FxHashSet<PlaceKey>,
    pub just_added: FxHashSet<PlaceKey>,
    /// Places whose length is needed by a `Len(place)` contract expression.
    /// Carried through the backward slice to trigger inclusion of `slice::len()`
    /// calls whose argument traces to the same origin.
    pub need_len: FxHashSet<PlaceKey>,
}

impl RelevantPlaces {
    /// Create an empty relevance set.
    pub fn new() -> Self {
        Self::default()
    }

    /// Return true when no roots have been collected.
    pub fn is_empty(&self) -> bool {
        self.places.is_empty() && self.locals.is_empty()
    }

    /// Insert a MIR local as a relevance root, tracking the addition.
    pub fn insert_local(&mut self, local: Local) {
        let pk = PlaceKey {
            base: if local.as_usize() == 0 {
                PlaceBaseKey::Return
            } else {
                PlaceBaseKey::Local(local.as_usize())
            },
            fields: Vec::new(),
        };
        if self.places.insert(pk.clone()) {
            self.just_added.insert(pk);
        }
        self.locals.insert(local);
    }

    /// Insert a MIR place as a relevance root.
    pub fn insert_mir_place(&mut self, place: &Place<'_>) {
        self.insert_place_key(PlaceKey::from_mir_place(place));
    }

    /// Insert a prebuilt place key as a relevance root, tracking addition.
    pub fn insert_place_key(&mut self, place: PlaceKey) {
        if let Some(local) = place.local() {
            self.locals.insert(local);
        }
        if self.places.insert(place.clone()) {
            self.just_added.insert(place);
        }
    }

    /// Merge another relevance set into this one, tracking additions.
    pub fn extend(&mut self, other: RelevantPlaces) {
        for place in other.places {
            if self.places.insert(place.clone()) {
                self.just_added.insert(place);
            }
        }
        for local in other.locals {
            self.locals.insert(local);
        }
        for place in other.need_len {
            self.need_len.insert(place);
        }
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

    /// Remove all roots contained in `other` from this set, marking them
    /// as saturated (definition found).
    pub fn remove_all(&mut self, other: &RelevantPlaces) {
        for local in &other.locals {
            self.saturated.insert(PlaceKey {
                base: PlaceBaseKey::Local(local.as_usize()),
                fields: vec![],
            });
            self.locals.remove(local);
            self.places.retain(|place| place.local() != Some(*local));
        }
        for place in &other.places {
            self.saturated.insert(place.clone());
            self.places.remove(place);
            if let Some(local) = place.local() {
                self.locals.remove(&local);
            }
        }
    }

    fn rebuild_locals(&mut self) {
        self.locals = self.places.iter().filter_map(PlaceKey::local).collect();
    }
}

// ── def-use extraction from MIR ────────────────────────────────────────

/// Collect definitions and uses for one MIR terminator.
///
/// Call terminators are handled separately by the slicer's `call_visit` module
/// (which consults interprocedural summaries), so the `Call` arm is
/// deliberately absent here.
pub fn terminator_use_def<'tcx>(terminator: &Terminator<'tcx>) -> DefUse {
    let mut use_def = DefUse::new();
    match &terminator.kind {
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
        #[cfg(rapx_ge_99)]
        Operand::RuntimeChecks(_) => {}
    }
    uses
}

fn place_uses(place: &Place<'_>) -> RelevantPlaces {
    let mut uses = RelevantPlaces::new();
    uses.insert_mir_place(place);
    uses.extend(place_projection_uses(place));
    uses
}

fn place_projection_uses(place: &Place<'_>) -> RelevantPlaces {
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
        #[cfg(not(rapx_ge_99))]
        Rvalue::ShallowInitBox(_, _) => {}
        Rvalue::Aggregate(_, aggregate_operands) => {
            operands.extend(aggregate_operands.iter());
        }
        Rvalue::Discriminant(_) | Rvalue::CopyForDeref(_) | Rvalue::ThreadLocalRef(_) | _ => {}
    }
    operands
}

// ── chain-tracing helpers ────────────────────────────────────────────

/// Trace a [`PlaceKey`] through the dataflow graph to resolve
/// Copy/Move chains back to their origin local.
pub fn trace_place_origin(flow: &DataflowGraph, key: &PlaceKey) -> PlaceKey {
    let Some(local) = key.local() else {
        return key.clone();
    };
    PlaceKey {
        base: PlaceBaseKey::Local(flow.trace_origin(local).as_usize()),
        fields: key.fields.clone(),
    }
}
