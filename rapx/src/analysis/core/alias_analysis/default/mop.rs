use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{
        Operand::{Constant, Copy, Move},
        TerminatorKind,
    },
    ty::{TyKind, TypingEnv},
};

use std::{cell::Cell, collections::HashSet};

use rustc_data_structures::fx::{FxHashMap, FxHashSet};

use crate::graphs::{
    scc::SccInfo,
    scc_paths::{
        SccEnumeratedPath, SccPathAction, SccPathSemantics, SccPathTraversalConfig,
        SccPathTraversalState, enumerate_scc_paths_cached,
    },
};

use super::value::Value;
use super::{graph::*, *};

/// rustc analysis threads can have a relatively small stack.
///
/// We cap recursive `check` depth so deeply nested CFG/SCC exploration degrades gracefully
/// instead of overflowing the compiler thread stack.
const CHECK_STACK_LIMIT: usize = 96;
thread_local! {
    static CHECK_DEPTH: Cell<usize> = Cell::new(0);
}

#[derive(Clone)]
struct MopStateSnapshot {
    values: Vec<Value>,
    constants: FxHashMap<usize, usize>,
    alias_sets: Vec<FxHashSet<usize>>,
}

enum SwitchSuccessorPlan {
    NotSwitch,
    SingleTarget {
        target: usize,
    },
    SplitTargets {
        constraint_id: usize,
        targets: rustc_middle::mir::SwitchTargets,
        otherwise_value: Option<usize>,
    },
}

struct DepthLimitGuard {
    key: &'static std::thread::LocalKey<Cell<usize>>,
}

fn enter_depth_limit(
    key: &'static std::thread::LocalKey<Cell<usize>>,
    limit: usize,
) -> Option<DepthLimitGuard> {
    key.with(|d| {
        let cur = d.get() + 1;
        d.set(cur);
        if cur > limit {
            d.set(cur - 1);
            None
        } else {
            Some(DepthLimitGuard { key })
        }
    })
}

impl Drop for DepthLimitGuard {
    fn drop(&mut self) {
        self.key.with(|d| {
            let cur = d.get();
            if cur > 0 {
                d.set(cur - 1);
            }
        });
    }
}

struct MopSccPathSemantics<'a, 'tcx> {
    graph: &'a mut AliasGraph<'tcx>,
}

impl<'a, 'tcx> SccPathSemantics for MopSccPathSemantics<'a, 'tcx> {
    fn on_node_enter(&mut self, node: usize, constraints: &mut FxHashMap<usize, usize>) {
        // Path constraints are facts about the current value of a discriminant/local.
        // Once a local is reassigned along this path, prior facts about that local are stale
        // and must be dropped to avoid using invalid path-sensitive assumptions downstream.
        if let Some(assigned_locals) = self.graph.assigned_locals(node) {
            for local in assigned_locals {
                rap_debug!(
                    "Remove path_constraints {:?}, because it has been reassigned.",
                    local
                );
                constraints.remove(local);
            }
        }
    }

    fn enumerate_child_paths(
        &mut self,
        child_enter: usize,
        constraints: &FxHashMap<usize, usize>,
    ) -> Vec<SccEnumeratedPath> {
        let child_scc = self.graph.cfg_block(child_enter).scc.clone();
        self.graph
            .find_scc_paths(child_enter, &child_scc, constraints)
    }

    fn enumerate_actions(
        &mut self,
        _scc: &SccInfo,
        state: &SccPathTraversalState,
        path_constraints: &FxHashMap<usize, usize>,
    ) -> Vec<SccPathAction> {
        let Some(term) = self.graph.terminator(state.cur).cloned() else {
            return Vec::new();
        };

        rap_debug!("term: {:?}", term);

        let mut path_constraints = path_constraints.clone();
        if let TerminatorKind::Call { destination, .. } = &term.kind {
            // A call can overwrite `destination`; any branch constraints on that value become
            // invalid immediately after the call and must not be propagated.
            let dest_idx = self.graph.projection(*destination);
            let dest_local = self
                .graph
                .path_graph
                .discriminants
                .get(&self.graph.values[dest_idx].local)
                .cloned()
                .unwrap_or(dest_idx);
            path_constraints.remove(&dest_local);
        }

        match term.kind {
            TerminatorKind::SwitchInt { discr, targets } => {
                let otherwise_val = self.graph.unique_otherwise_switch_value(&discr, &targets);
                let place = match discr {
                    Copy(p) | Move(p) => Some(self.graph.projection(p)),
                    _ => None,
                };

                let Some(place) = place else {
                    return Vec::new();
                };

                let discr_local = self
                    .graph
                    .path_graph
                    .discriminants
                    .get(&self.graph.values[place].local)
                    .cloned()
                    .unwrap_or(place);

                let possible_values = self
                    .graph
                    .possible_switch_values_for_constraint_id(discr_local);
                let mut actions = Vec::new();

                if let Some(&constant) = path_constraints.get(&discr_local) {
                    // `usize::MAX` is our sentinel for "take otherwise/default branch".
                    // It is used when we cannot represent otherwise as a unique concrete value.
                    if constant == usize::MAX {
                        actions.push(SccPathAction::Traverse {
                            next: targets.otherwise().as_usize(),
                            constraints: path_constraints,
                        });
                        return actions;
                    }

                    let mut found = false;
                    for branch in targets.iter() {
                        if branch.0 as usize != constant {
                            continue;
                        }
                        found = true;
                        actions.push(SccPathAction::Traverse {
                            next: branch.1.as_usize(),
                            constraints: path_constraints.clone(),
                        });
                    }
                    if !found {
                        actions.push(SccPathAction::Traverse {
                            next: targets.otherwise().as_usize(),
                            constraints: path_constraints,
                        });
                    }
                    return actions;
                }

                if let Some(values) = possible_values {
                    for constant in values {
                        let mut new_constraints = path_constraints.clone();
                        new_constraints.insert(discr_local, constant);
                        actions.push(SccPathAction::Traverse {
                            next: self.graph.switch_target_for_value(&targets, constant),
                            constraints: new_constraints,
                        });
                    }
                    return actions;
                }

                for branch in targets.iter() {
                    let mut new_constraints = path_constraints.clone();
                    new_constraints.insert(discr_local, branch.0 as usize);
                    actions.push(SccPathAction::Traverse {
                        next: branch.1.as_usize(),
                        constraints: new_constraints,
                    });
                }

                let mut otherwise_constraints = path_constraints;
                // Prefer a concrete value for `otherwise` if there is exactly one remaining
                // enum/bool variant; otherwise use the sentinel to represent default flow.
                otherwise_constraints.insert(discr_local, otherwise_val.unwrap_or(usize::MAX));
                actions.push(SccPathAction::Traverse {
                    next: targets.otherwise().as_usize(),
                    constraints: otherwise_constraints,
                });

                actions
            }
            _ => {
                let mut actions = Vec::new();
                actions.push(SccPathAction::RecordExit {
                    constraints: path_constraints.clone(),
                });
                for next in self.graph.cfg_block(state.cur).next.clone() {
                    actions.push(SccPathAction::Traverse {
                        next,
                        constraints: path_constraints.clone(),
                    });
                }
                actions
            }
        }
    }
}

impl<'tcx> AliasGraph<'tcx> {
    fn switch_target_for_value(
        &self,
        targets: &rustc_middle::mir::SwitchTargets,
        value: usize,
    ) -> usize {
        for (v, bb) in targets.iter() {
            if v as usize == value {
                return bb.as_usize();
            }
        }
        targets.otherwise().as_usize()
    }

    fn unique_otherwise_switch_value(
        &self,
        discr: &rustc_middle::mir::Operand<'tcx>,
        targets: &rustc_middle::mir::SwitchTargets,
    ) -> Option<usize> {
        let tcx = self.tcx();
        let local_decls = &tcx.optimized_mir(self.def_id()).local_decls;

        let place = match discr {
            Copy(p) | Move(p) => Some(*p),
            _ => None,
        }?;

        let place_ty = place.ty(local_decls, tcx).ty;
        let possible_values: Vec<usize> = match place_ty.kind() {
            TyKind::Bool => vec![0, 1],
            TyKind::Adt(adt_def, _) if adt_def.is_enum() => (0..adt_def.variants().len()).collect(),
            _ => return None,
        };

        let mut seen = FxHashSet::default();
        for (val, _) in targets.iter() {
            seen.insert(val as usize);
        }

        let remaining: Vec<usize> = possible_values
            .into_iter()
            .filter(|v| !seen.contains(v))
            .collect();

        if remaining.len() == 1 {
            Some(remaining[0])
        } else {
            None
        }
    }

    fn possible_switch_values_for_constraint_id(&self, discr_local: usize) -> Option<Vec<usize>> {
        let tcx = self.tcx();
        let local_decls = &tcx.optimized_mir(self.def_id()).local_decls;
        if discr_local >= local_decls.len() {
            return None;
        }

        let ty = local_decls[rustc_middle::mir::Local::from_usize(discr_local)].ty;
        match ty.kind() {
            TyKind::Bool => Some(vec![0, 1]),
            TyKind::Adt(adt_def, _) if adt_def.is_enum() => {
                Some((0..adt_def.variants().len()).collect())
            }
            _ => None,
        }
    }

    fn snapshot_state(&self) -> MopStateSnapshot {
        MopStateSnapshot {
            values: self.values.clone(),
            constants: self.constants.clone(),
            alias_sets: self.alias_sets.clone(),
        }
    }

    fn restore_state(&mut self, snapshot: &MopStateSnapshot) {
        self.values = snapshot.values.clone();
        self.constants = snapshot.constants.clone();
        self.alias_sets = snapshot.alias_sets.clone();
    }

    fn apply_path_constraints(&mut self, constraints: Option<&FxHashMap<usize, usize>>) {
        if let Some(constraints) = constraints {
            self.constants.extend(constraints);
        }
    }

    fn known_switch_value(&mut self, discr: &rustc_middle::mir::Operand<'tcx>) -> Option<usize> {
        match discr {
            Copy(p) | Move(p) => {
                let value_idx = self.projection(*p);
                let tcx = self.tcx();
                let local_decls = &tcx.optimized_mir(self.def_id()).local_decls;
                let place_ty = (*p).ty(local_decls, tcx);

                match place_ty.ty.kind() {
                    TyKind::Bool => self
                        .constants
                        .get(&value_idx)
                        .copied()
                        .filter(|c| *c != usize::MAX),
                    _ => {
                        let father = self
                            .path_graph
                            .discriminants
                            .get(&self.values[value_idx].local)?;
                        self.constants
                            .get(father)
                            .copied()
                            .filter(|c| *c != usize::MAX)
                    }
                }
            }
            Constant(c) => {
                // Preserve existing behavior: if evaluation fails, we still treat this as
                // a deterministic switch and default to `0`.
                let tcx = self.tcx();
                let ty_env = TypingEnv::post_analysis(tcx, self.def_id());
                Some(
                    c.const_
                        .try_eval_target_usize(tcx, ty_env)
                        .map_or(0, |v| v as usize),
                )
            }
        }
    }

    fn switch_constraint_id_for_split(
        &mut self,
        discr: &rustc_middle::mir::Operand<'tcx>,
    ) -> Option<usize> {
        match discr {
            Copy(p) | Move(p) => {
                let value_idx = self.projection(*p);
                let tcx = self.tcx();
                let local_decls = &tcx.optimized_mir(self.def_id()).local_decls;
                let place_ty = (*p).ty(local_decls, tcx);
                match place_ty.ty.kind() {
                    TyKind::Bool => Some(value_idx),
                    _ => {
                        let father = self
                            .path_graph
                            .discriminants
                            .get(&self.values[value_idx].local)?;
                        (self.values[value_idx].local == value_idx).then_some(*father)
                    }
                }
            }
            Constant(_) => None,
        }
    }

    fn analyze_switch_successors(&mut self, bb_idx: usize) -> SwitchSuccessorPlan {
        let Some(terminator) = self.terminator(bb_idx).cloned() else {
            return SwitchSuccessorPlan::NotSwitch;
        };
        let TerminatorKind::SwitchInt { discr, targets } = terminator.kind else {
            return SwitchSuccessorPlan::NotSwitch;
        };

        if let Some(discriminant_value) = self.known_switch_value(&discr) {
            return SwitchSuccessorPlan::SingleTarget {
                target: self.switch_target_for_value(&targets, discriminant_value),
            };
        }

        let Some(constraint_id) = self.switch_constraint_id_for_split(&discr) else {
            return SwitchSuccessorPlan::NotSwitch;
        };

        let otherwise_value = self.unique_otherwise_switch_value(&discr, &targets);
        SwitchSuccessorPlan::SplitTargets {
            constraint_id,
            targets,
            otherwise_value,
        }
    }

    fn dispatch_split_switch_targets(
        &mut self,
        constraint_id: usize,
        targets: &rustc_middle::mir::SwitchTargets,
        otherwise_value: Option<usize>,
        fn_map: &mut MopFnAliasMap,
        recursion_set: &mut HashSet<DefId>,
    ) {
        if let Some(values) = self.possible_switch_values_for_constraint_id(constraint_id) {
            // Enumerate each possible value explicitly (bool: 0/1, enum: 0..N).
            for constraint_value in values {
                if self.visit_times() > VISIT_LIMIT {
                    continue;
                }
                let next = self.switch_target_for_value(targets, constraint_value);
                self.split_check_with_cond(
                    next,
                    constraint_id,
                    constraint_value,
                    fn_map,
                    recursion_set,
                );
            }
            return;
        }

        // Fallback: explore explicit branches + otherwise.
        for (constraint_value, branch) in targets.iter() {
            if self.visit_times() > VISIT_LIMIT {
                continue;
            }
            self.split_check_with_cond(
                branch.as_usize(),
                constraint_id,
                constraint_value as usize,
                fn_map,
                recursion_set,
            );
        }

        // `usize::MAX` is the sentinel for "otherwise/default branch" when no unique concrete
        // value can represent that arm.
        self.split_check_with_cond(
            targets.otherwise().as_usize(),
            constraint_id,
            otherwise_value.unwrap_or(usize::MAX),
            fn_map,
            recursion_set,
        );
    }

    fn dispatch_normal_successors(
        &mut self,
        successors: impl IntoIterator<Item = usize>,
        fn_map: &mut MopFnAliasMap,
        recursion_set: &mut HashSet<DefId>,
    ) {
        for next in successors {
            if self.visit_times() > VISIT_LIMIT {
                continue;
            }
            self.split_check(next, fn_map, recursion_set);
        }
    }

    fn allowed_switch_targets_for_exit(&mut self, exit_node: usize) -> Option<FxHashSet<usize>> {
        let Some(terminator) = self.terminator(exit_node).cloned() else {
            return None;
        };
        let TerminatorKind::SwitchInt { discr, targets } = terminator.kind else {
            return None;
        };

        let place = match discr {
            Copy(p) | Move(p) => Some(self.projection(p)),
            _ => None,
        }?;

        let discr_local = self
            .path_graph
            .discriminants
            .get(&self.values[place].local)
            .cloned()
            .unwrap_or(place);

        let mut allowed = FxHashSet::default();
        if let Some(&constant) = self.constants.get(&discr_local) {
            allowed.insert(self.switch_target_for_value(&targets, constant));
        } else {
            // No path constraint: all explicit targets and default remain reachable.
            for (_, bb) in targets.iter() {
                allowed.insert(bb.as_usize());
            }
            allowed.insert(targets.otherwise().as_usize());
        }
        Some(allowed)
    }

    fn follow_recorded_scc_exits(
        &mut self,
        scc: &SccInfo,
        exit_node: usize,
        allowed_targets: Option<&FxHashSet<usize>>,
        fn_map: &mut MopFnAliasMap,
        recursion_set: &mut HashSet<DefId>,
    ) -> bool {
        let mut followed = false;
        for edge in &scc.exits {
            if edge.exit != exit_node {
                continue;
            }
            if let Some(allowed_targets) = allowed_targets {
                if !allowed_targets.contains(&edge.to) {
                    continue;
                }
            }
            followed = true;
            self.split_check(edge.to, fn_map, recursion_set);
        }
        followed
    }

    pub fn split_check(
        &mut self,
        bb_idx: usize,
        fn_map: &mut MopFnAliasMap,
        recursion_set: &mut HashSet<DefId>,
    ) {
        let snapshot = self.snapshot_state();
        self.check(bb_idx, fn_map, recursion_set);
        self.restore_state(&snapshot);
    }
    pub fn split_check_with_cond(
        &mut self,
        bb_idx: usize,
        path_discr_id: usize,
        path_discr_val: usize,
        fn_map: &mut MopFnAliasMap,
        recursion_set: &mut HashSet<DefId>,
    ) {
        let snapshot = self.snapshot_state();
        // Add control-sensitive indicator to the path status.
        self.constants.insert(path_discr_id, path_discr_val);
        self.check(bb_idx, fn_map, recursion_set);
        self.restore_state(&snapshot);
    }

    // the core function of the alias analysis algorithm.
    pub fn check(
        &mut self,
        bb_idx: usize,
        fn_map: &mut MopFnAliasMap,
        recursion_set: &mut HashSet<DefId>,
    ) {
        let Some(_guard) = enter_depth_limit(&CHECK_DEPTH, CHECK_STACK_LIMIT) else {
            // Prevent rustc stack overflow on extremely deep CFG / SCC exploration.
            return;
        };
        self.increment_visit_times();
        if self.visit_times() > VISIT_LIMIT {
            return;
        }
        let scc_idx = self.cfg_block(bb_idx).scc.enter;
        rap_debug!("check {:?}", bb_idx);
        if bb_idx == scc_idx && !self.cfg_block(bb_idx).scc.nodes.is_empty() {
            rap_debug!("check {:?} as a scc", bb_idx);
            self.check_scc(bb_idx, fn_map, recursion_set);
        } else {
            self.check_single_node(bb_idx, fn_map, recursion_set);
            self.handle_nexts(bb_idx, fn_map, None, recursion_set);
        }
    }

    pub fn check_scc(
        &mut self,
        bb_idx: usize,
        fn_map: &mut MopFnAliasMap,
        recursion_set: &mut HashSet<DefId>,
    ) {
        let cur_scc = self.cfg_block(bb_idx).scc.clone();

        /* Handle cases if the current block is a merged scc block with sub block */
        rap_debug!("Searchng paths in scc: {:?}, {:?}", bb_idx, cur_scc);
        let scc = self.sort_scc_tree(&cur_scc);
        rap_debug!("scc: {:?}", scc);
        // Propagate constraints collected so far (top-down)
        let inherited_constraints = self.constants.clone();
        let paths_in_scc = self.find_scc_paths(bb_idx, &scc, &inherited_constraints);
        rap_debug!("Paths found in scc: {:?}", paths_in_scc);

        // Every SCC path is evaluated from the same pre-SCC state.
        let snapshot = self.snapshot_state();
        let backup_recursion_set = recursion_set.clone();

        // SCC exits are recorded on the SCC entry metadata.
        for raw_path in paths_in_scc {
            self.restore_state(&snapshot);
            *recursion_set = backup_recursion_set.clone();

            let path = raw_path.blocks;
            let path_constraints = &raw_path.constraints;
            rap_debug!("checking path: {:?}", path);

            // Apply alias transfer for every node in the path (including the exit node).
            for idx in &path {
                self.alias_bb(*idx);
                self.alias_bbcall(*idx, fn_map, recursion_set);
            }

            // The path ends at an SCC-exit node (inside the SCC). We now leave the SCC only via
            // recorded SCC exit edges from that node, carrying the collected path constraints.
            if let Some(&exit_node) = path.last() {
                self.apply_path_constraints(Some(path_constraints));
                let allowed_targets = self.allowed_switch_targets_for_exit(exit_node);
                let followed = self.follow_recorded_scc_exits(
                    &cur_scc,
                    exit_node,
                    allowed_targets.as_ref(),
                    fn_map,
                    recursion_set,
                );

                // If this SCC path ends at a node that is not recorded as an exit (should be rare),
                // fall back to exploring its successors normally.
                if !followed {
                    self.handle_nexts(exit_node, fn_map, Some(path_constraints), recursion_set);
                }
            }
        }
    }

    pub fn check_single_node(
        &mut self,
        bb_idx: usize,
        fn_map: &mut MopFnAliasMap,
        recursion_set: &mut HashSet<DefId>,
    ) {
        rap_debug!("check {:?} as a node", bb_idx);
        let cur_next = self.cfg_block(bb_idx).next.clone();
        self.alias_bb(self.cfg_block(bb_idx).scc.enter);
        self.alias_bbcall(self.cfg_block(bb_idx).scc.enter, fn_map, recursion_set);
        if cur_next.is_empty() {
            self.merge_results();
            return;
        }
    }

    pub fn handle_nexts(
        &mut self,
        bb_idx: usize,
        fn_map: &mut MopFnAliasMap,
        path_constraints: Option<&FxHashMap<usize, usize>>,
        recursion_set: &mut HashSet<DefId>,
    ) {
        let successors = self.cfg_block(bb_idx).next.clone();

        rap_debug!(
            "handle nexts {:?} of node {:?}",
            self.cfg_block(bb_idx).next,
            bb_idx
        );
        // Extra constraints are introduced during SCC path expansion and reused here when
        // dispatching CFG successors after exiting an SCC path.
        self.apply_path_constraints(path_constraints);

        match self.analyze_switch_successors(bb_idx) {
            SwitchSuccessorPlan::SingleTarget { target } => {
                rap_debug!("visit a single switch target: {:?}", target);
                self.check(target, fn_map, recursion_set);
            }
            SwitchSuccessorPlan::SplitTargets {
                constraint_id,
                targets,
                otherwise_value,
            } => {
                self.dispatch_split_switch_targets(
                    constraint_id,
                    &targets,
                    otherwise_value,
                    fn_map,
                    recursion_set,
                );
            }
            SwitchSuccessorPlan::NotSwitch => {
                self.dispatch_normal_successors(successors, fn_map, recursion_set);
            }
        }
    }

    pub fn find_scc_paths(
        &mut self,
        start: usize,
        scc: &SccInfo,
        initial_constraints: &FxHashMap<usize, usize>,
    ) -> Vec<SccEnumeratedPath> {
        let def_id = self.def_id();
        let mut semantics = MopSccPathSemantics { graph: self };
        enumerate_scc_paths_cached(
            def_id,
            start,
            scc,
            initial_constraints.clone(),
            &mut semantics,
            SccPathTraversalConfig::default(),
        )
    }
}
