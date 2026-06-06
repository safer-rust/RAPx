use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{
        Operand::{Constant, Copy, Move},
        TerminatorKind,
    },
    ty::{TyKind, TypingEnv},
};

use std::{
    cell::{Cell, RefCell},
    collections::HashSet,
};

use rustc_data_structures::fx::{FxHashMap, FxHashSet};

use crate::graphs::{
    scc::SccInfo,
    scc_paths::{
        SccEnumeratedPath, SccPathAction, SccPathSemantics, SccPathTraversalConfig,
        SccPathTraversalState, constraints_key, enumerate_scc_paths,
    },
};

use super::{graph::*, *};

// rustc analysis threads may have a relatively small stack; keep recursion limits conservative.
const CHECK_STACK_LIMIT: usize = 96;
const SCC_PATH_CACHE_LIMIT: usize = 2048;

thread_local! {
    static CHECK_DEPTH: Cell<usize> = Cell::new(0);
    static SCC_PATH_CACHE: RefCell<
        FxHashMap<SccPathCacheKey, Vec<(Vec<usize>, FxHashMap<usize, usize>)>>
    > = RefCell::new(FxHashMap::default());
}

#[derive(Clone, Hash, PartialEq, Eq)]
struct SccPathCacheKey {
    def_id: DefId,
    scc_enter: usize,
    constraints: Vec<(usize, usize)>,
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
    graph: &'a mut MopGraph<'tcx>,
}

impl<'a, 'tcx> SccPathSemantics for MopSccPathSemantics<'a, 'tcx> {
    fn on_node_enter(&mut self, node: usize, constraints: &mut FxHashMap<usize, usize>) {
        for local in &self.graph.cfg_block(node).assigned_locals {
            rap_debug!(
                "Remove path_constraints {:?}, because it has been reassigned.",
                local
            );
            constraints.remove(local);
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
        let Some(term) = self.graph.cfg_block(state.cur).terminator.clone() else {
            return Vec::new();
        };

        rap_debug!("term: {:?}", term);

        let mut path_constraints = path_constraints.clone();
        if let TerminatorKind::Call { destination, .. } = &term.kind {
            let dest_idx = self.graph.projection(*destination);
            let dest_local = self
                .graph
                .cfg
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
                    .cfg
                    .discriminants
                    .get(&self.graph.values[place].local)
                    .cloned()
                    .unwrap_or(place);

                let possible_values = self
                    .graph
                    .possible_switch_values_for_constraint_id(discr_local);
                let mut actions = Vec::new();

                if let Some(&constant) = path_constraints.get(&discr_local) {
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

impl<'tcx> MopGraph<'tcx> {
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

    pub fn split_check(
        &mut self,
        bb_idx: usize,
        fn_map: &mut MopFnAliasMap,
        recursion_set: &mut HashSet<DefId>,
    ) {
        /* duplicate the status before visiting a path; */
        let backup_values = self.values.clone(); // duplicate the status when visiting different paths;
        let backup_constant = self.cfg.constants.clone();
        let backup_alias_sets = self.alias_sets.clone();
        self.check(bb_idx, fn_map, recursion_set);
        /* restore after visit */
        self.alias_sets = backup_alias_sets;
        self.values = backup_values;
        self.cfg.constants = backup_constant;
    }
    pub fn split_check_with_cond(
        &mut self,
        bb_idx: usize,
        path_discr_id: usize,
        path_discr_val: usize,
        fn_map: &mut MopFnAliasMap,
        recursion_set: &mut HashSet<DefId>,
    ) {
        /* duplicate the status before visiting a path; */
        let backup_values = self.values.clone(); // duplicate the status when visiting different paths;
        let backup_constant = self.cfg.constants.clone();
        let backup_alias_sets = self.alias_sets.clone();
        /* add control-sensitive indicator to the path status */
        self.cfg.constants.insert(path_discr_id, path_discr_val);
        self.check(bb_idx, fn_map, recursion_set);
        /* restore after visit */
        self.alias_sets = backup_alias_sets;
        self.values = backup_values;
        self.cfg.constants = backup_constant;
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
        let inherited_constraints = self.cfg.constants.clone();
        let paths_in_scc = self.find_scc_paths(bb_idx, &scc, &inherited_constraints);
        rap_debug!("Paths found in scc: {:?}", paths_in_scc);

        let backup_values = self.values.clone(); // duplicate the status when visiteding different paths;
        let backup_constant = self.cfg.constants.clone();
        let backup_alias_sets = self.alias_sets.clone();
        let backup_recursion_set = recursion_set.clone();

        // SCC exits are stored on the SCC enter node.
        let scc_exits = cur_scc.exits.clone();
        for raw_path in paths_in_scc {
            self.alias_sets = backup_alias_sets.clone();
            self.values = backup_values.clone();
            self.cfg.constants = backup_constant.clone();
            *recursion_set = backup_recursion_set.clone();

            let path = raw_path.0;
            let path_constraints = &raw_path.1;
            rap_debug!("checking path: {:?}", path);

            // Apply alias transfer for every node in the path (including the exit node).
            for idx in &path {
                self.alias_bb(*idx);
                self.alias_bbcall(*idx, fn_map, recursion_set);
            }

            // The path ends at an SCC-exit node (inside the SCC). We now leave the SCC only via
            // recorded SCC exit edges from that node, carrying the collected path constraints.
            if let Some(&exit_node) = path.last() {
                self.cfg.constants.extend(path_constraints);
                let mut followed = false;

                // If exit_node is a SwitchInt, only follow SCC-exit edges consistent with the
                // current constraint (important for enum parameters).
                let mut allowed_targets: Option<FxHashSet<usize>> = None;
                if let Some(sw) = self.cfg_block(exit_node).terminator.clone() {
                    if let TerminatorKind::SwitchInt { discr, targets } = sw.kind {
                        // Resolve discr local id in the same way as SCC path generation.
                        let place = match discr {
                            Copy(p) | Move(p) => Some(self.projection(p)),
                            _ => None,
                        };
                        if let Some(place) = place {
                            let discr_local = self
                                .cfg
                                .discriminants
                                .get(&self.values[place].local)
                                .cloned()
                                .unwrap_or(place);

                            let mut allowed = FxHashSet::default();
                            if let Some(&c) = self.cfg.constants.get(&discr_local) {
                                allowed.insert(self.switch_target_for_value(&targets, c));
                            } else {
                                // No constraint: allow all explicit targets + default.
                                for (_, bb) in targets.iter() {
                                    allowed.insert(bb.as_usize());
                                }
                                allowed.insert(targets.otherwise().as_usize());
                            }
                            allowed_targets = Some(allowed);
                        }
                    }
                }

                for e in &scc_exits {
                    if e.exit != exit_node {
                        continue;
                    }
                    if let Some(allowed) = &allowed_targets {
                        if !allowed.contains(&e.to) {
                            continue;
                        }
                    }
                    followed = true;
                    self.split_check(e.to, fn_map, recursion_set);
                }

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
        let cur_next = self.cfg_block(bb_idx).next.clone();
        let tcx = self.tcx();

        rap_debug!(
            "handle nexts {:?} of node {:?}",
            self.cfg_block(bb_idx).next,
            bb_idx
        );
        // Extra path contraints are introduced during scc handling.
        if let Some(path_constraints) = path_constraints {
            self.cfg.constants.extend(path_constraints);
        }
        /* Begin: handle the SwitchInt statement. */
        let mut single_target = false;
        let mut sw_val = 0;
        let mut sw_target = 0; // Single target
        let mut path_discr_id = 0; // To avoid analyzing paths that cannot be reached with one enum type.
        let mut sw_targets = None; // Multiple targets of SwitchInt
        let mut sw_otherwise_val: Option<usize> = None;

        if let Some(switch) = self.cfg_block(bb_idx).terminator.clone() {
            if let TerminatorKind::SwitchInt {
                ref discr,
                ref targets,
            } = switch.kind
            {
                sw_otherwise_val = self.unique_otherwise_switch_value(discr, targets);
                match discr {
                    Copy(p) | Move(p) => {
                        let value_idx = self.projection(*p);
                        let local_decls = &tcx.optimized_mir(self.def_id()).local_decls;
                        let place_ty = (*p).ty(local_decls, tcx);
                        rap_debug!("value_idx: {:?}", value_idx);
                        match place_ty.ty.kind() {
                            TyKind::Bool => {
                                if let Some(constant) = self.cfg.constants.get(&value_idx) {
                                    if *constant != usize::MAX {
                                        single_target = true;
                                        sw_val = *constant;
                                    }
                                }
                                path_discr_id = value_idx;
                                sw_targets = Some(targets.clone());
                            }
                            _ => {
                                if let Some(father) =
                                    self.cfg.discriminants.get(&self.values[value_idx].local)
                                {
                                    if let Some(constant) = self.cfg.constants.get(father) {
                                        if *constant != usize::MAX {
                                            single_target = true;
                                            sw_val = *constant;
                                        }
                                    }
                                    if self.values[value_idx].local == value_idx {
                                        path_discr_id = *father;
                                        sw_targets = Some(targets.clone());
                                    }
                                }
                            }
                        }
                    }
                    Constant(c) => {
                        single_target = true;
                        let ty_env = TypingEnv::post_analysis(tcx, self.def_id());
                        if let Some(val) = c.const_.try_eval_target_usize(tcx, ty_env) {
                            sw_val = val as usize;
                        }
                    }
                }
                if single_target {
                    rap_debug!("targets: {:?}; sw_val = {:?}", targets, sw_val);
                    sw_target = self.switch_target_for_value(targets, sw_val);
                }
            }
        }
        /* End: finish handling SwitchInt */
        // fixed path since a constant switchInt value
        if single_target {
            rap_debug!("visit a single target: {:?}", sw_target);
            self.check(sw_target, fn_map, recursion_set);
        } else {
            // Other cases in switchInt terminators
            if let Some(targets) = sw_targets {
                if let Some(values) = self.possible_switch_values_for_constraint_id(path_discr_id) {
                    // Enumerate each possible value explicitly (bool: 0/1, enum: 0..N).
                    for path_discr_val in values {
                        if self.visit_times() > VISIT_LIMIT {
                            continue;
                        }
                        let next = self.switch_target_for_value(&targets, path_discr_val);
                        self.split_check_with_cond(
                            next,
                            path_discr_id,
                            path_discr_val,
                            fn_map,
                            recursion_set,
                        );
                    }
                } else {
                    // Fallback: explore explicit branches + otherwise.
                    for iter in targets.iter() {
                        if self.visit_times() > VISIT_LIMIT {
                            continue;
                        }
                        let next = iter.1.as_usize();
                        let path_discr_val = iter.0 as usize;
                        self.split_check_with_cond(
                            next,
                            path_discr_id,
                            path_discr_val,
                            fn_map,
                            recursion_set,
                        );
                    }
                    let next_index = targets.otherwise().as_usize();
                    // For bool/enum switches, the "otherwise" arm may represent a single concrete
                    // value (e.g., an enum with 2 variants). Prefer a concrete value when unique.
                    let path_discr_val = sw_otherwise_val.unwrap_or(usize::MAX); // default/otherwise path
                    self.split_check_with_cond(
                        next_index,
                        path_discr_id,
                        path_discr_val,
                        fn_map,
                        recursion_set,
                    );
                }
            } else {
                for next in cur_next {
                    if self.visit_times() > VISIT_LIMIT {
                        continue;
                    }
                    self.split_check(next, fn_map, recursion_set);
                }
            }
        }
    }

    pub fn find_scc_paths(
        &mut self,
        start: usize,
        scc: &SccInfo,
        initial_constraints: &FxHashMap<usize, usize>,
    ) -> Vec<(Vec<usize>, FxHashMap<usize, usize>)> {
        let key = SccPathCacheKey {
            def_id: self.def_id(),
            scc_enter: scc.enter,
            constraints: constraints_key(initial_constraints),
        };

        if let Some(cached) = SCC_PATH_CACHE.with(|c| c.borrow().get(&key).cloned()) {
            return cached;
        }

        let mut semantics = MopSccPathSemantics { graph: self };
        let all_paths = enumerate_scc_paths(
            start,
            scc,
            initial_constraints.clone(),
            &mut semantics,
            SccPathTraversalConfig::default(),
        );

        SCC_PATH_CACHE.with(|c| {
            let mut cache = c.borrow_mut();
            if cache.len() >= SCC_PATH_CACHE_LIMIT {
                cache.clear();
            }
            cache.insert(key, all_paths.clone());
        });

        all_paths
    }
}
