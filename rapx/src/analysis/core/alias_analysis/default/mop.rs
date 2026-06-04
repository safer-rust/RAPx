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
        constraints_key, record_unique_path, PathKey, SccPathTraversalState,
    },
};

use super::{block::Term, graph::*, *};

// rustc analysis threads may have a relatively small stack; keep recursion limits conservative.
const CHECK_STACK_LIMIT: usize = 96;
const SCC_DFS_STACK_LIMIT: usize = 128;
const SCC_PATH_CACHE_LIMIT: usize = 2048;

thread_local! {
    static CHECK_DEPTH: Cell<usize> = Cell::new(0);
    static SCC_DFS_DEPTH: Cell<usize> = Cell::new(0);
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
        let tcx = self.tcx;
        let local_decls = &tcx.optimized_mir(self.def_id).local_decls;

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

    fn record_scc_exit_path(
        &self,
        scc: &SccInfo,
        node: usize,
        constraints: &FxHashMap<usize, usize>,
        cur_path: &Vec<usize>,
        out: &mut Vec<(Vec<usize>, FxHashMap<usize, usize>)>,
        seen_paths: &mut FxHashSet<PathKey>,
    ) {
        if !scc.exits.iter().any(|e| e.exit == node) {
            return;
        }
        record_unique_path(cur_path, constraints, out, seen_paths);
    }

    fn possible_switch_values_for_constraint_id(&self, discr_local: usize) -> Option<Vec<usize>> {
        let tcx = self.tcx;
        let local_decls = &tcx.optimized_mir(self.def_id).local_decls;
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
        let backup_constant = self.constants.clone();
        let backup_alias_sets = self.alias_sets.clone();
        self.check(bb_idx, fn_map, recursion_set);
        /* restore after visit */
        self.alias_sets = backup_alias_sets;
        self.values = backup_values;
        self.constants = backup_constant;
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
        let backup_constant = self.constants.clone();
        let backup_alias_sets = self.alias_sets.clone();
        /* add control-sensitive indicator to the path status */
        self.constants.insert(path_discr_id, path_discr_val);
        self.check(bb_idx, fn_map, recursion_set);
        /* restore after visit */
        self.alias_sets = backup_alias_sets;
        self.values = backup_values;
        self.constants = backup_constant;
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
        self.visit_times += 1;
        if self.visit_times > VISIT_LIMIT {
            return;
        }
        let scc_idx = self.blocks[bb_idx].scc.enter;
        let cur_block = self.blocks[bb_idx].clone();

        rap_debug!("check {:?}", bb_idx);
        if bb_idx == scc_idx && !cur_block.scc.nodes.is_empty() {
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
        let cur_block = self.blocks[bb_idx].clone();

        /* Handle cases if the current block is a merged scc block with sub block */
        rap_debug!("Searchng paths in scc: {:?}, {:?}", bb_idx, cur_block.scc);
        let scc = self.sort_scc_tree(&cur_block.scc);
        rap_debug!("scc: {:?}", scc);
        // Propagate constraints collected so far (top-down)
        let inherited_constraints = self.constants.clone();
        let paths_in_scc = self.find_scc_paths(bb_idx, &scc, &inherited_constraints);
        rap_debug!("Paths found in scc: {:?}", paths_in_scc);

        let backup_values = self.values.clone(); // duplicate the status when visiteding different paths;
        let backup_constant = self.constants.clone();
        let backup_alias_sets = self.alias_sets.clone();
        let backup_recursion_set = recursion_set.clone();

        // SCC exits are stored on the SCC enter node.
        let scc_exits = cur_block.scc.exits.clone();
        for raw_path in paths_in_scc {
            self.alias_sets = backup_alias_sets.clone();
            self.values = backup_values.clone();
            self.constants = backup_constant.clone();
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
                self.constants.extend(path_constraints);
                let mut followed = false;

                // If exit_node is a SwitchInt, only follow SCC-exit edges consistent with the
                // current constraint (important for enum parameters).
                let mut allowed_targets: Option<FxHashSet<usize>> = None;
                if let Term::Switch(sw) = self.blocks[exit_node].terminator.clone() {
                    if let TerminatorKind::SwitchInt { discr, targets } = sw.kind {
                        // Resolve discr local id in the same way as SCC path generation.
                        let place = match discr {
                            Copy(p) | Move(p) => Some(self.projection(p)),
                            _ => None,
                        };
                        if let Some(place) = place {
                            let discr_local = self
                                .discriminants
                                .get(&self.values[place].local)
                                .cloned()
                                .unwrap_or(place);

                            let mut allowed = FxHashSet::default();
                            if let Some(&c) = self.constants.get(&discr_local) {
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
        let cur_block = self.blocks[bb_idx].clone();
        self.alias_bb(self.blocks[bb_idx].scc.enter);
        self.alias_bbcall(self.blocks[bb_idx].scc.enter, fn_map, recursion_set);
        if cur_block.next.is_empty() {
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
        let cur_block = self.blocks[bb_idx].clone();
        let tcx = self.tcx;

        rap_debug!(
            "handle nexts {:?} of node {:?}",
            self.blocks[bb_idx].next,
            bb_idx
        );
        // Extra path contraints are introduced during scc handling.
        if let Some(path_constraints) = path_constraints {
            self.constants.extend(path_constraints);
        }
        /* Begin: handle the SwitchInt statement. */
        let mut single_target = false;
        let mut sw_val = 0;
        let mut sw_target = 0; // Single target
        let mut path_discr_id = 0; // To avoid analyzing paths that cannot be reached with one enum type.
        let mut sw_targets = None; // Multiple targets of SwitchInt
        let mut sw_otherwise_val: Option<usize> = None;

        match cur_block.terminator {
            Term::Switch(ref switch) => {
                if let TerminatorKind::SwitchInt {
                    ref discr,
                    ref targets,
                } = switch.kind
                {
                    sw_otherwise_val = self.unique_otherwise_switch_value(discr, targets);
                    match discr {
                        Copy(p) | Move(p) => {
                            let value_idx = self.projection(*p);
                            let local_decls = &tcx.optimized_mir(self.def_id).local_decls;
                            let place_ty = (*p).ty(local_decls, tcx);
                            rap_debug!("value_idx: {:?}", value_idx);
                            match place_ty.ty.kind() {
                                TyKind::Bool => {
                                    if let Some(constant) = self.constants.get(&value_idx) {
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
                                        self.discriminants.get(&self.values[value_idx].local)
                                    {
                                        if let Some(constant) = self.constants.get(father) {
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
                            let ty_env = TypingEnv::post_analysis(tcx, self.def_id);
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
            _ => {
                // Not SwitchInt
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
                        if self.visit_times > VISIT_LIMIT {
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
                        if self.visit_times > VISIT_LIMIT {
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
                for next in cur_block.next {
                    if self.visit_times > VISIT_LIMIT {
                        continue;
                    }
                    self.split_check(next, fn_map, recursion_set);
                }
            }
        }
    }

    pub fn sort_scc_tree(&mut self, scc: &SccInfo) -> SccInfo {
        self.populate_child_sccs(scc.enter);
        self.blocks[scc.enter].scc.clone()
    }

    /// Recursively discover nested child SCCs for the SCC rooted at `enter` and
    /// write the result back into `self.blocks[enter].scc.child_sccs`.
    fn populate_child_sccs(&mut self, enter: usize) {
        // Collect the node list first to avoid holding a borrow on self.blocks.
        let nodes: Vec<usize> = self.blocks[enter].scc.nodes.iter().cloned().collect();
        let mut child_enters: Vec<usize> = Vec::new();
        let mut seen = rustc_data_structures::fx::FxHashSet::default();

        for node in nodes {
            if let Some(block) = self.blocks.get(node) {
                let node_enter = block.scc.enter;
                let non_trivial = !block.scc.nodes.is_empty();
                if node_enter != enter && non_trivial && seen.insert(node_enter) {
                    child_enters.push(node_enter);
                }
            }
        }

        self.blocks[enter].scc.child_sccs = child_enters;

        for &child_enter in &self.blocks[enter].scc.child_sccs.clone() {
            self.populate_child_sccs(child_enter);
        }
    }

    pub fn find_scc_paths(
        &mut self,
        start: usize,
        scc: &SccInfo,
        initial_constraints: &FxHashMap<usize, usize>,
    ) -> Vec<(Vec<usize>, FxHashMap<usize, usize>)> {
        let key = SccPathCacheKey {
            def_id: self.def_id,
            scc_enter: scc.enter,
            constraints: constraints_key(initial_constraints),
        };

        if let Some(cached) = SCC_PATH_CACHE.with(|c| c.borrow().get(&key).cloned()) {
            return cached;
        }

        let mut all_paths = Vec::new();
        let mut seen_paths: FxHashSet<PathKey> = FxHashSet::default();

        self.find_scc_paths_inner(
            scc,
            SccPathTraversalState::new(start),
            initial_constraints.clone(),
            &mut all_paths,
            &mut seen_paths,
        );

        // Paths are deduplicated incrementally via `seen_paths`.

        SCC_PATH_CACHE.with(|c| {
            let mut cache = c.borrow_mut();
            if cache.len() >= SCC_PATH_CACHE_LIMIT {
                cache.clear();
            }
            cache.insert(key, all_paths.clone());
        });

        all_paths
    }

    fn find_scc_paths_inner(
        &mut self,
        scc: &SccInfo,
        state: SccPathTraversalState,
        mut path_constraints: FxHashMap<usize, usize>,
        paths_in_scc: &mut Vec<(Vec<usize>, FxHashMap<usize, usize>)>,
        seen_paths: &mut FxHashSet<PathKey>,
    ) {
        let Some(_guard) = enter_depth_limit(&SCC_DFS_DEPTH, SCC_DFS_STACK_LIMIT) else {
            return;
        };
        if scc.nodes.is_empty() {
            record_unique_path(&state.path, &path_constraints, paths_in_scc, seen_paths);
            return;
        }

        // Temporary complexity control to avoid path explosion.
        // Use unique-path count to avoid biased truncation from duplicates.
        if state.exceeds_complexity_limits(200, 4000, seen_paths.len()) {
            return;
        }

        // We do not traverse outside the SCC when generating SCC internal paths.
        // Instead, we record paths that end at SCC-exit nodes (nodes with an outgoing edge leaving
        // the SCC), and the caller is responsible for resuming traversal outside the SCC.
        if !state.is_cur_in_scc(scc) {
            return;
        }

        let mut state = state;
        if !state.prepare_for_current_node() {
            return;
        }

        // Clear the constraints if the local is reassigned in the current block;
        // Otherwise, it cannot reach other branches.
        for local in &self.blocks[state.cur].assigned_locals {
            rap_debug!(
                "Remove path_constraints {:?}, because it has been reassigned.",
                local
            );
            path_constraints.remove(&local);
        }

        // Find the paths of inner scc recursively;
        for &child_enter in &scc.child_sccs {
            if state.cur == child_enter {
                // When a spliced child-SCC path ends back at the child-enter, we must continue
                // exploring the *parent* SCC without immediately re-expanding the same child SCC
                // again (otherwise we can loop until the depth guard triggers and drop paths).
                if state.skip_child_enter == Some(child_enter) {
                    break;
                }

                let child_scc = self.blocks[child_enter].scc.clone();
                let sub_paths = self.find_scc_paths(child_enter, &child_scc, &path_constraints);
                rap_debug!("paths in sub scc: {}, {:?}", child_enter, sub_paths);

                // Always allow the parent SCC to proceed from `child_enter` without traversing
                // into the child SCC (conceptually, an empty child path). This is necessary when
                // the child enumeration is truncated/empty and also to allow parent exits at
                // `child_enter` (e.g., an edge to a sink `Unreachable` block) to be recorded.
                {
                    self.find_scc_paths_inner(
                        scc,
                        state.with_skip_child_enter(child_enter),
                        path_constraints.clone(),
                        paths_in_scc,
                        seen_paths,
                    );
                }

                for (subp, subconst) in sub_paths {
                    // A single-node sub-path ([child_enter]) makes no progress and would only
                    // re-trigger child expansion; the no-op continuation above already covers it.
                    if subp.len() <= 1 {
                        continue;
                    }

                    let mut new_path = state.path.clone();
                    new_path.extend(&subp[1..]);
                    // `subconst` already starts from `path_constraints` and accumulates changes.
                    // Use it as the current constraints after splicing.
                    let new_const = subconst;

                    let new_cur = *new_path.last().unwrap();
                    let next_skip_child_enter = if new_cur == child_enter {
                        Some(child_enter)
                    } else {
                        None
                    };

                    self.find_scc_paths_inner(
                        scc,
                        state.with_spliced_path(new_path, next_skip_child_enter),
                        new_const,
                        paths_in_scc,
                        seen_paths,
                    );
                }
                return;
            }
        }

        let term = self.terminators[state.cur].clone();
        rap_debug!("term: {:?}", term);

        // Clear constraints when their discriminant locals are redefined by terminators.
        // NOTE: `assigned_locals` is populated only from `StatementKind::Assign`, and does not
        // include locals assigned by terminators (e.g., `_11 = random()` in MIR is a `Call`).
        // If we don't clear these, stale constraints can incorrectly prune SwitchInt branches and
        // also amplify path explosion via inconsistent constraint propagation across iterations.
        if let TerminatorKind::Call { destination, .. } = &term {
            let dest_idx = self.projection(*destination);
            let dest_local = self
                .discriminants
                .get(&self.values[dest_idx].local)
                .cloned()
                .unwrap_or(dest_idx);
            path_constraints.remove(&dest_local);
        }

        match term {
            TerminatorKind::SwitchInt { discr, targets } => {
                let otherwise_val = self.unique_otherwise_switch_value(&discr, &targets);
                // Resolve discr local id for constraint propagation
                let place = match discr {
                    Copy(p) | Move(p) => Some(self.projection(p)),
                    _ => None,
                };

                let Some(place) = place else {
                    return;
                };

                let discr_local = self
                    .discriminants
                    .get(&self.values[place].local)
                    .cloned()
                    .unwrap_or(place);

                let possible_values = self.possible_switch_values_for_constraint_id(discr_local);

                if let Some(&constant) = path_constraints.get(&discr_local) {
                    // Existing constraint: only explore the feasible branch.
                    if constant == usize::MAX {
                        let next = targets.otherwise().as_usize();
                        let next_in_scc = state.is_node_in_scc(scc, next);
                        if !next_in_scc {
                            // Exits the SCC via the default branch.
                            self.record_scc_exit_path(
                                scc,
                                state.cur,
                                &path_constraints,
                                &state.path,
                                paths_in_scc,
                                seen_paths,
                            );
                            return;
                        }
                        if state.can_descend_to(next) {
                            self.find_scc_paths_inner(
                                scc,
                                state.descend_to(next),
                                path_constraints,
                                paths_in_scc,
                                seen_paths,
                            );
                        }
                    } else {
                        let mut found = false;
                        for branch in targets.iter() {
                            if branch.0 as usize != constant {
                                continue;
                            }
                            found = true;
                            let next = branch.1.as_usize();
                            let next_in_scc = state.is_node_in_scc(scc, next);
                            if !next_in_scc {
                                // Exits the SCC via this constrained branch.
                                self.record_scc_exit_path(
                                    scc,
                                    state.cur,
                                    &path_constraints,
                                    &state.path,
                                    paths_in_scc,
                                    seen_paths,
                                );
                                continue;
                            }
                            if !state.can_descend_to(next) {
                                continue;
                            }
                            self.find_scc_paths_inner(
                                scc,
                                state.descend_to(next),
                                path_constraints.clone(),
                                paths_in_scc,
                                seen_paths,
                            );
                        }
                        if !found {
                            let next = targets.otherwise().as_usize();
                            let next_in_scc = state.is_node_in_scc(scc, next);
                            if !next_in_scc {
                                // Exits the SCC via the default branch.
                                self.record_scc_exit_path(
                                    scc,
                                    state.cur,
                                    &path_constraints,
                                    &state.path,
                                    paths_in_scc,
                                    seen_paths,
                                );
                                return;
                            }
                            if state.can_descend_to(next) {
                                self.find_scc_paths_inner(
                                    scc,
                                    state.descend_to(next),
                                    path_constraints,
                                    paths_in_scc,
                                    seen_paths,
                                );
                            }
                        }
                    }
                } else {
                    // No constraint yet: if this is a bool/enum discriminant, enumerate every
                    // possible value explicitly (not just "iter + otherwise").
                    if let Some(values) = possible_values {
                        for constant in values {
                            let next = self.switch_target_for_value(&targets, constant);

                            let next_in_scc = state.is_node_in_scc(scc, next);
                            let mut new_constraints = path_constraints.clone();
                            new_constraints.insert(discr_local, constant);

                            if !next_in_scc {
                                self.record_scc_exit_path(
                                    scc,
                                    state.cur,
                                    &new_constraints,
                                    &state.path,
                                    paths_in_scc,
                                    seen_paths,
                                );
                                continue;
                            }
                            if !state.can_descend_to(next) {
                                continue;
                            }

                            self.find_scc_paths_inner(
                                scc,
                                state.descend_to(next),
                                new_constraints,
                                paths_in_scc,
                                seen_paths,
                            );
                        }
                    } else {
                        // Fallback: explore explicit branches + otherwise.
                        for branch in targets.iter() {
                            let constant = branch.0 as usize;
                            let next = branch.1.as_usize();
                            let next_in_scc = state.is_node_in_scc(scc, next);
                            let mut new_constraints = path_constraints.clone();
                            new_constraints.insert(discr_local, constant);

                            if !next_in_scc {
                                self.record_scc_exit_path(
                                    scc,
                                    state.cur,
                                    &new_constraints,
                                    &state.path,
                                    paths_in_scc,
                                    seen_paths,
                                );
                                continue;
                            }
                            if !state.can_descend_to(next) {
                                continue;
                            }
                            self.find_scc_paths_inner(
                                scc,
                                state.descend_to(next),
                                new_constraints,
                                paths_in_scc,
                                seen_paths,
                            );
                        }

                        let next = targets.otherwise().as_usize();
                        let next_in_scc = state.is_node_in_scc(scc, next);
                        let mut new_constraints = path_constraints;
                        new_constraints.insert(discr_local, otherwise_val.unwrap_or(usize::MAX));

                        if !next_in_scc {
                            self.record_scc_exit_path(
                                scc,
                                state.cur,
                                &new_constraints,
                                &state.path,
                                paths_in_scc,
                                seen_paths,
                            );
                            return;
                        }
                        if state.can_descend_to(next) {
                            self.find_scc_paths_inner(
                                scc,
                                state.descend_to(next),
                                new_constraints,
                                paths_in_scc,
                                seen_paths,
                            );
                        }
                    }
                }
            }
            _ => {
                // For non-SwitchInt terminators, reaching an SCC-exit node is enough to record a
                // usable path segment. Successors leaving the SCC are not traversed here.
                self.record_scc_exit_path(
                    scc,
                    state.cur,
                    &path_constraints,
                    &state.path,
                    paths_in_scc,
                    seen_paths,
                );
                for next in self.blocks[state.cur].next.clone() {
                    let next_in_scc = state.is_node_in_scc(scc, next);
                    if !next_in_scc {
                        continue;
                    }
                    if !state.can_descend_to(next) {
                        continue;
                    }
                    self.find_scc_paths_inner(
                        scc,
                        state.descend_to(next),
                        path_constraints.clone(),
                        paths_in_scc,
                        seen_paths,
                    );
                }
            }
        }
    }
}
