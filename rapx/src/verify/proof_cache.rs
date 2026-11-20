//! Cached symbolic states for sliced proof goals.

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{BasicBlock, Body},
    ty::TyCtxt,
};
use std::{cell::Cell, sync::Arc};
use z3::Config;

use crate::analysis::path::CallArg;
use crate::compat::FxHashMap;

use super::{
    config::VerifyConfig,
    contract::Property,
    slicer::{ProofGoal, RelevantItem},
    vm::VmExecutor,
};

#[derive(Clone, Hash, PartialEq, Eq)]
enum GoalItemKey<'tcx> {
    Statement(DefId, BasicBlock, Option<usize>, usize),
    Terminator(DefId, BasicBlock, Option<usize>, Option<BasicBlock>),
    CalleeEntry(DefId, Option<usize>, Vec<CallArg>),
    CalleeExit(usize),
    ContractFact(Property<'tcx>),
}

#[derive(Hash, PartialEq, Eq)]
struct PrefixEdge<'tcx> {
    parent: usize,
    chunk: Vec<GoalItemKey<'tcx>>,
}

/// Symbolic states shared by properties that retain the same MIR and entry facts.
pub(crate) struct VmCache<'z3, 'tcx> {
    context: &'z3 z3::Context,
    config: Arc<VerifyConfig>,
    states: FxHashMap<Vec<GoalItemKey<'tcx>>, CachedGoal<'z3, 'tcx>>,
    prefix_edges: FxHashMap<PrefixEdge<'tcx>, usize>,
    prefix_states: Vec<Arc<Vec<VmExecutor<'z3, 'tcx>>>>,
    max_entries: usize,
}

pub(crate) struct CachedGoal<'z3, 'tcx> {
    pub(crate) states: Arc<Vec<VmExecutor<'z3, 'tcx>>>,
    pub(crate) reachability: Vec<Cell<Option<z3::SatResult>>>,
}

const VM_CACHE_MAX_ENTRIES: usize = 128;
const VM_PREFIX_STRIDE: usize = 16;

impl<'z3, 'tcx> VmCache<'z3, 'tcx> {
    pub(crate) fn new(context: &'z3 z3::Context, config: Arc<VerifyConfig>) -> Self {
        Self::new_with_capacity(context, VM_CACHE_MAX_ENTRIES, config)
    }

    pub(crate) fn new_with_capacity(context: &'z3 z3::Context, max_entries: usize, config: Arc<VerifyConfig>) -> Self {
        Self {
            context,
            config,
            states: FxHashMap::default(),
            prefix_edges: FxHashMap::default(),
            prefix_states: Vec::new(),
            max_entries,
        }
    }

    pub(crate) fn states_for(
        &mut self,
        tcx: TyCtxt<'tcx>,
        caller_def_id: DefId,
        instance_body: Option<&'tcx Body<'tcx>>,
        goal: ProofGoal<'tcx>,
    ) -> &CachedGoal<'z3, 'tcx> {
        let key = goal_key(&goal.items);
        if self.states.contains_key(&key) {
            return self.states.get(&key).unwrap();
        }
        if self.states.len() >= self.max_entries {
            self.states.clear();
        }
        if self.prefix_states.len() >= self.max_entries.saturating_mul(4).max(1) {
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
            Arc::new(
                VmExecutor::new(
                    self.context,
                    tcx,
                    caller_def_id,
                    instance_body,
                    self.config.constructor_mir_mode(),
                )
                .execute_items(&[]),
            )
        };
        while prefix_len < key.len() {
            let end = ((prefix_len / VM_PREFIX_STRIDE) + 1)
                .saturating_mul(VM_PREFIX_STRIDE)
                .min(key.len());
            if states
                .iter()
                .any(|state| !state.path_state.diagnostics.is_unsupported())
            {
                let owned =
                    Arc::try_unwrap(states).unwrap_or_else(|shared| shared.as_ref().clone());
                states = Arc::new(VmExecutor::execute_items_after(
                    owned,
                    &goal.items[prefix_len..end],
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
            RelevantItem::ContractFact { property } => GoalItemKey::ContractFact(property.clone()),
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
