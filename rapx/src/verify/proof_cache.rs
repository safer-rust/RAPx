//! Cached symbolic states for sliced proof goals.

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{BasicBlock, Body},
    ty::TyCtxt,
};
use std::{cell::Cell, rc::Rc, sync::Arc};
use z3::Config;

use crate::analysis::path::CallArg;
use crate::compat::FxHashMap;
use crate::contract::Property;
use crate::limit::{VM_CACHE_MAX_ENTRIES, VM_PREFIX_STRIDE};
use crate::vm::VmExecutor;

use super::{
    config::VerifyConfig,
    path::Path,
    slicer::RelevantItem,
};

/// A sliced MIR path and the contract facts assumed before its first item.
#[derive(Clone)]
pub(crate) struct ProofGoal<'tcx> {
    pub(crate) path: Path,
    pub(crate) items: Vec<RelevantItem<'tcx>>,
    pub(crate) entry_facts: Vec<Property<'tcx>>,
}

#[derive(Clone, Hash, PartialEq, Eq)]
enum GoalItemKey<'tcx> {
    EntryFacts(Vec<Property<'tcx>>),
    Statement(DefId, BasicBlock, Option<usize>, usize),
    Terminator(DefId, BasicBlock, Option<usize>, Option<BasicBlock>),
    CalleeEntry(DefId, Option<usize>, Vec<CallArg>),
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
    config: Rc<VerifyConfig>,
    states: FxHashMap<Vec<GoalItemKey<'tcx>>, CachedGoal<'z3, 'tcx>>,
    prefix_edges: FxHashMap<PrefixEdge<'tcx>, usize>,
    prefix_states: Vec<Arc<Vec<VmExecutor<'z3, 'tcx>>>>,
}

pub(crate) struct CachedGoal<'z3, 'tcx> {
    pub(crate) states: Arc<Vec<VmExecutor<'z3, 'tcx>>>,
    pub(crate) reachability: Vec<Cell<Option<z3::SatResult>>>,
}

impl<'z3, 'tcx> VmCache<'z3, 'tcx> {
    pub(crate) fn new(context: &'z3 z3::Context, config: Rc<VerifyConfig>) -> Self {
        Self {
            context,
            config,
            states: FxHashMap::default(),
            prefix_edges: FxHashMap::default(),
            prefix_states: Vec::new(),
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
        if self.prefix_states.len() >= VM_CACHE_MAX_ENTRIES.saturating_mul(4).max(1) {
            self.prefix_edges.clear();
            self.prefix_states.clear();
        }
        let mut prefix_len = 0;
        let mut parent = 0;
        while prefix_len + VM_PREFIX_STRIDE < key.len() {
            let edge = PrefixEdge {
                parent,
                chunk: key[prefix_len..prefix_len + VM_PREFIX_STRIDE].to_vec(),
            };
            let Some(&next) = self.prefix_edges.get(&edge) else {
                break;
            };
            parent = next;
            prefix_len += VM_PREFIX_STRIDE;
        }
        let mut states = if prefix_len > 0 {
            Arc::clone(&self.prefix_states[parent - 1])
        } else {
            let mut states = VmExecutor::new(
                self.context,
                tcx,
                caller_def_id,
                instance_body,
                self.config.constructor_mir_mode(),
            ).execute_items(&[]);
            for state in &mut states {
                for property in &goal.entry_facts {
                    if state.diagnostics().is_unsupported() { break; }
                    state.assert_contract_fact(property);
                }
            }
            prefix_len = 1;
            Arc::new(states)
        };
        while prefix_len < key.len() {
            let end = ((prefix_len / VM_PREFIX_STRIDE) + 1)
                .saturating_mul(VM_PREFIX_STRIDE)
                .min(key.len());
            if states
                .iter()
                .any(|state| !state.diagnostics().is_unsupported())
            {
                let owned =
                    Arc::try_unwrap(states).unwrap_or_else(|shared| shared.as_ref().clone());
                states = Arc::new(VmExecutor::execute_items_after(
                    owned,
                    &goal.items[prefix_len - 1..end - 1],
                ));
            }
            if end < key.len() {
                let edge = PrefixEdge {
                    parent,
                    chunk: key[prefix_len..end].to_vec(),
                };
                parent = self.prefix_states.len() + 1;
                self.prefix_edges.insert(edge, parent);
                self.prefix_states.push(Arc::clone(&states));
            }
            prefix_len = end;
        }
        let reachability = states.iter().map(|_| Cell::new(None)).collect();
        self.states.insert(
            key.clone(),
            CachedGoal {
                states,
                reachability,
            },
        );
        self.states.get(&key).unwrap()
    }
}

fn goal_key<'tcx>(items: &[RelevantItem<'tcx>]) -> Vec<GoalItemKey<'tcx>> {
    items
        .iter()
        .map(|item| match item {
            RelevantItem::Statement {
                def_id,
                block,
                global_block,
                stmt_index,
            } => GoalItemKey::Statement(*def_id, *block, *global_block, *stmt_index),
            RelevantItem::Terminator {
                def_id,
                block,
                global_block,
                switch_succ,
            } => GoalItemKey::Terminator(*def_id, *block, *global_block, *switch_succ),
            RelevantItem::CalleeEntry { callee, body, args } => GoalItemKey::CalleeEntry(
                *callee,
                body.map(|body| body as *const _ as usize),
                args.clone(),
            ),
            RelevantItem::CalleeExit { dest } => GoalItemKey::CalleeExit(*dest),
        })
        .collect()
}

/// Create a fresh Z3 context with a fixed 10s solver timeout.
/// A new context is created per verification phase.
pub(crate) fn new_z3_context() -> z3::Context {
    let mut cfg = Config::new();
    cfg.set_timeout_msec(10000);
    z3::Context::new(&cfg)
}
