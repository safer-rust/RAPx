//! Cached symbolic states for sliced proof goals.

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{BasicBlock, Body},
    ty::TyCtxt,
};
use std::{cell::Cell, rc::Rc};
use z3::Config;

use crate::analysis::path::CallArg;
use crate::compat::FxHashMap;
use crate::contract::Property;
use crate::limit::{VM_CACHE_MAX_ENTRIES, VM_PREFIX_STRIDE, Z3_TIMEOUT_MS};
use crate::vm::{VmExecutor, constructor_policy::ConstructorMirMode};

use super::slicer::RelevantItem;

/// Sliced MIR items and the contract facts assumed before execution.
pub(crate) struct ProofGoal<'tcx> {
    pub(crate) items: Vec<RelevantItem<'tcx>>,
    pub(crate) entry_facts: Vec<Property<'tcx>>,
}

#[derive(Clone, Hash, PartialEq, Eq)]
enum GoalItemKey<'tcx> {
    /// Contract facts assumed before execution; different facts produce different initial states.
    EntryFacts(Vec<Property<'tcx>>),
    /// Owning function, MIR block, and statement index.
    Statement(DefId, BasicBlock, usize),
    /// Owning function, MIR block, and chosen successor, if any.
    Terminator(DefId, BasicBlock, Option<BasicBlock>),
    /// Inlined callee, optional selected MIR body address, and bindings for its arguments.
    CalleeEntry(DefId, Option<usize>, Vec<CallArg>),
    /// Caller local that receives the inlined callee's return value.
    CalleeExit(usize),
}

#[derive(Hash, PartialEq, Eq)]
struct PrefixEdge<'tcx> {
    parent: usize,
    chunk: Vec<GoalItemKey<'tcx>>,
}

/// Symbolic states shared by properties that retain the same MIR and entry facts.
pub(crate) struct VmCache<'z3, 'tcx> {
    context: &'z3 z3::Context,
    constructor_mir_mode: ConstructorMirMode,
    /// Shared prefixes with node IDs and VM states, keyed by parent node and next MIR chunk.
    prefixes: FxHashMap<PrefixEdge<'tcx>, (usize, Rc<Vec<VmExecutor<'z3, 'tcx>>>)>,
    /// Complete proof goals and their final VM states and reachability results.
    states: FxHashMap<Vec<GoalItemKey<'tcx>>, CachedGoal<'z3, 'tcx>>,
}

pub(crate) struct CachedGoal<'z3, 'tcx> {
    pub(crate) states: Rc<Vec<VmExecutor<'z3, 'tcx>>>,
    pub(crate) reachability: Vec<Cell<Option<z3::SatResult>>>,
}

impl<'z3, 'tcx> VmCache<'z3, 'tcx> {
    pub(crate) fn new(context: &'z3 z3::Context, constructor_mir_mode: ConstructorMirMode) -> Self {
        Self {
            context,
            constructor_mir_mode,
            prefixes: FxHashMap::default(),
            states: FxHashMap::default(),
        }
    }

    pub(crate) fn states_for(
        &mut self,
        tcx: TyCtxt<'tcx>,
        caller_def_id: DefId,
        instance_body: Option<&'tcx Body<'tcx>>,
        goal: ProofGoal<'tcx>,
    ) -> &CachedGoal<'z3, 'tcx> {
        // Keep entry facts in the cache key; the remaining keys correspond to MIR items.
        let mut key = vec![GoalItemKey::EntryFacts(goal.entry_facts.clone())];
        key.extend(goal_key(&goal.items));
        if self.states.contains_key(&key) {
            return self.states.get(&key).unwrap();
        }
        if self.states.len() >= VM_CACHE_MAX_ENTRIES {
            self.states.clear();
        }
        if self.prefixes.len() >= VM_CACHE_MAX_ENTRIES.saturating_mul(4).max(1) {
            self.prefixes.clear();
        }
        let mut prefix_len = 0;
        let mut parent = 0;
        let mut prefix_state = None;
        while prefix_len + VM_PREFIX_STRIDE < key.len() {
            let edge = PrefixEdge { parent, chunk: key[prefix_len..prefix_len + VM_PREFIX_STRIDE].to_vec() };
            let Some((next, state)) = self.prefixes.get(&edge) else {
                break;
            };
            parent = *next;
            prefix_state = Some(Rc::clone(state));
            prefix_len += VM_PREFIX_STRIDE;
        }
        let mut states = if let Some(state) = prefix_state {
            state
        } else {
            let mut states = VmExecutor::new(
                self.context,
                tcx,
                caller_def_id,
                instance_body,
                self.constructor_mir_mode,
            ).execute_items(&[]);
            for state in &mut states {
                for property in &goal.entry_facts {
                    if state.diagnostics().is_unsupported() { break; }
                    state.assert_contract_fact(property);
                }
            }
            prefix_len = 1;
            Rc::new(states)
        };
        while prefix_len < key.len() {
            let end = ((prefix_len / VM_PREFIX_STRIDE) + 1).saturating_mul(VM_PREFIX_STRIDE).min(key.len());
            if states.iter().any(|state| !state.diagnostics().is_unsupported()) {
                let owned = Rc::try_unwrap(states).unwrap_or_else(|shared| shared.as_ref().clone());
                states = Rc::new(VmExecutor::execute_items_after(owned, &goal.items[prefix_len - 1..end - 1]));
            }
            if end < key.len() {
                let edge = PrefixEdge { parent, chunk: key[prefix_len..end].to_vec() };
                parent = self.prefixes.len() + 1;
                self.prefixes.insert(edge, (parent, Rc::clone(&states)));
            }
            prefix_len = end;
        }
        let reachability = states.iter().map(|_| Cell::new(None)).collect();
        self.states.insert(key.clone(), CachedGoal { states, reachability });
        self.states.get(&key).unwrap()
    }
}

fn goal_key<'tcx>(items: &[RelevantItem<'tcx>]) -> Vec<GoalItemKey<'tcx>> {
    items
        .iter()
        .map(|item| match item {
            RelevantItem::Statement { def_id, block, stmt_index, .. } =>
                GoalItemKey::Statement(*def_id, *block, *stmt_index),
            RelevantItem::Terminator { def_id, block, switch_succ, .. } =>
                GoalItemKey::Terminator(*def_id, *block, *switch_succ),
            RelevantItem::CalleeEntry { callee, body, args } =>
                GoalItemKey::CalleeEntry(*callee, body.map(|body| body as *const _ as usize), args.clone()),
            RelevantItem::CalleeExit { dest } => GoalItemKey::CalleeExit(*dest),
        })
        .collect()
}

/// Create a fresh Z3 context with a fixed 10s solver timeout.
/// A new context is created per verification phase.
pub(crate) fn new_z3_context() -> z3::Context {
    let mut cfg = Config::new();
    cfg.set_timeout_msec(Z3_TIMEOUT_MS);
    z3::Context::new(&cfg)
}
