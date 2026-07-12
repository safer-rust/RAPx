use super::{bug_records::*, corner_case::*, drop::*, graph::*};
use crate::{
    analysis::alias_analysis::default::{MopFnAliasMap, types::ValueKind},
    analysis::path_analysis::{PathNode, PathTree},
    def_id::is_drop_fn,
    utils::source::{get_filename, get_name},
};
use rustc_middle::{
    mir::{
        Operand::{self},
        Place, TerminatorKind,
    },
    ty::{self},
};
use rustc_span::{Span, Symbol};

pub const VISIT_LIMIT: usize = 1000;

impl<'tcx> SafeDropGraph<'tcx> {
    // analyze the drop statement and update the liveness for nodes.
    pub fn drop_check(&mut self, bb_idx: usize) {
        let is_cleanup = self.alias_graph.cfg_block(bb_idx).is_cleanup;
        if let Some(terminator) = self.alias_graph.terminator(bb_idx).cloned() {
            rap_debug!("drop check bb: {}, {:?}", bb_idx, terminator);
            match terminator.kind {
                TerminatorKind::Drop {
                    ref place,
                    target: _,
                    unwind: _,
                    replace: _,
                    drop: _,
                    #[cfg(not(rapx_rustc_ge_198))]
                        async_fut: _,
                } => {
                    if !self.drop_heap_item_check(place) {
                        return;
                    }
                    let value_idx = self.alias_graph.projection(place.clone());
                    self.sync_drop_record();
                    self.add_to_drop_record(value_idx, bb_idx, is_cleanup);
                }
                TerminatorKind::Call {
                    ref func, ref args, ..
                } => {
                    let Operand::Constant(c) = func else {
                        return;
                    };
                    let ty::FnDef(id, ..) = c.ty().kind() else {
                        return;
                    };
                    if !is_drop_fn(*id) {
                        return;
                    }
                    if !args.is_empty() {
                        let place = match args[0].node {
                            Operand::Copy(place) => place,
                            Operand::Move(place) => place,
                            _ => {
                                rap_error!("Constant operand exists: {:?}", args[0]);
                                return;
                            }
                        };
                        if !self.drop_heap_item_check(&place) {
                            return;
                        }
                        let local = self.alias_graph.projection(place.clone());
                        self.sync_drop_record();
                        self.add_to_drop_record(local, bb_idx, is_cleanup);
                    }
                }
                _ => {}
            }
        }
    }

    pub fn drop_heap_item_check(&self, place: &Place<'tcx>) -> bool {
        let tcx = self.alias_graph.tcx();
        let place_ty = place.ty(
            &tcx.optimized_mir(self.alias_graph.def_id()).local_decls,
            tcx,
        );
        match place_ty.ty.kind() {
            ty::TyKind::Adt(adtdef, ..) => match self.adt_owner.get(&adtdef.did()) {
                None => true,
                Some(owenr_unit) => {
                    let idx = match place_ty.variant_index {
                        Some(vdx) => vdx.index(),
                        None => 0,
                    };
                    if owenr_unit[idx].0.is_onheap() || owenr_unit[idx].1.contains(&true) {
                        true
                    } else {
                        false
                    }
                }
            },
            _ => true,
        }
    }

    /// Process pre-enumerated whole-function paths for SafeDrop via DFS on
    /// the path tree. All paths have already been filtered by incremental
    /// constraint-based reachability checks during enumeration, so no
    /// per-path filtering is needed. State is saved at branch points and
    /// restored before each sibling subtree.
    pub fn process_function_paths_opt(
        &mut self,
        precomputed_paths: Option<PathTree>,
        fn_map: &MopFnAliasMap,
    ) {
        let paths = precomputed_paths.unwrap_or_else(|| self.alias_graph.enumerate_paths());

        let Some(root) = paths.root() else {
            return;
        };
        let mut path = Vec::new();
        let _ = self.dfs_safedrop(root, &mut path, fn_map);
    }

    fn dfs_safedrop(
        &mut self,
        node: &PathNode,
        path: &mut Vec<usize>,
        fn_map: &MopFnAliasMap,
    ) -> Result<(), ()> {
        path.push(node.block);
        self.alias_bb(node.block);
        self.alias_bbcall(node.block, fn_map);
        self.drop_check(node.block);

        let saved_values = self.alias_graph.values.clone();
        let saved_constants = self.alias_graph.constants.clone();
        let saved_alias_sets = self.alias_graph.alias_sets.clone();
        let saved_drop_record = self.drop_record.clone();

        if node.is_path_end {
            self.alias_graph.increment_visit_times();
            if self.alias_graph.visit_times() > VISIT_LIMIT {
                path.pop();
                return Err(());
            }
            if should_check(self.alias_graph.def_id()) {
                if let Some(&last) = path.last() {
                    let cfg_block = self.alias_graph.cfg_block(last).clone();
                    self.dp_check(cfg_block.is_cleanup);
                }
            }
        }

        for child in &node.children {
            self.alias_graph.values = saved_values.clone();
            self.alias_graph.constants = saved_constants.clone();
            self.alias_graph.alias_sets = saved_alias_sets.clone();
            self.drop_record = saved_drop_record.clone();
            self.dfs_safedrop(child, path, fn_map)?;
        }

        path.pop();
        Ok(())
    }
    pub fn report_bugs(&self) {
        rap_debug!(
            "report bugs, id: {:?}, uaf: {:?}",
            self.alias_graph.def_id(),
            self.bug_records.uaf_bugs
        );
        let filename = get_filename(self.alias_graph.tcx(), self.alias_graph.def_id());
        match filename {
            Some(filename) => {
                if filename.contains(".cargo") {
                    return;
                }
            }
            None => {}
        }
        if self.bug_records.is_bug_free() {
            return;
        }
        let fn_name = match get_name(self.alias_graph.tcx(), self.alias_graph.def_id()) {
            Some(name) => name,
            None => Symbol::intern("no symbol available"),
        };
        let body = self
            .alias_graph
            .tcx()
            .optimized_mir(self.alias_graph.def_id());
        self.bug_records
            .df_bugs_output(body, fn_name, self.alias_graph.span());
        self.bug_records
            .uaf_bugs_output(body, fn_name, self.alias_graph.span());
        self.bug_records
            .dp_bug_output(body, fn_name, self.alias_graph.span());
    }

    fn make_bug(
        &self,
        idx: usize,
        trigger_info: LocalSpot,
        span: Span,
        confidence: usize,
        bug_type: BugType,
    ) -> TyBug {
        TyBug {
            drop_spot: self.drop_record[idx].drop_spot,
            trigger_info,
            span,
            confidence,
            bug_type,
        }
    }

    fn check_drop_status(&mut self, idx: usize) -> Option<usize> {
        self.fetch_drop_info(idx);
        let mut fully_dropped = true;
        if !self.drop_record[idx].is_dropped {
            fully_dropped = false;
            if !self.drop_record[idx].has_dropped_field {
                return None;
            }
        }
        let kind = self.alias_graph.values[idx].kind;
        Some(Self::rate_confidence(kind, fully_dropped))
    }

    pub fn uaf_check(&mut self, value_idx: usize, bb_idx: usize, span: Span, is_fncall: bool) {
        let local = self.alias_graph.values[value_idx].local;
        rap_debug!(
            "uaf_check, idx: {:?}, local: {:?}, drop_record: {:?}",
            value_idx,
            local,
            self.drop_record[value_idx],
        );
        if !self.alias_graph.values[value_idx].may_drop {
            return;
        }
        if self.alias_graph.values[value_idx].is_ptr() && !is_fncall {
            return;
        }
        let Some(confidence) = self.check_drop_status(value_idx) else {
            return;
        };
        if self.bug_records.uaf_bugs.contains_key(&local) {
            return;
        }
        let drop_spot = self.drop_record[value_idx].drop_spot;
        if let Some(t) = self
            .bug_records
            .try_merge_pair(drop_spot, bb_idx, BugType::UseAfterFree)
        {
            let bug = self.make_bug(
                value_idx,
                LocalSpot::new(bb_idx, local),
                span.clone(),
                confidence,
                t,
            );
            rap_warn!("Find a use-after-free bug {:?}; add to records", bug);
            self.bug_records.uaf_bugs.insert(local, bug);
        }
    }

    pub fn rate_confidence(kind: ValueKind, fully_dropped: bool) -> usize {
        match (kind, fully_dropped) {
            (ValueKind::SpecialPtr, _) => 0,
            (_, true) => 99,
            (_, false) => 50,
        }
    }

    pub fn df_check(
        &mut self,
        value_idx: usize,
        bb_idx: usize,
        span: Span,
        flag_cleanup: bool,
    ) -> bool {
        let local = self.alias_graph.values[value_idx].local;
        rap_debug!(
            "df_check: value_idx = {:?}, bb_idx = {:?}, alias_sets: {:?}",
            value_idx,
            bb_idx,
            self.alias_graph.alias_sets,
        );
        let Some(confidence) = self.check_drop_status(value_idx) else {
            return false;
        };

        for item in &self.drop_record {
            rap_debug!("drop_spot: {:?}", item);
        }

        let drop_spot = self.drop_record[value_idx].drop_spot;
        let result_type = self
            .bug_records
            .try_merge_pair(drop_spot, bb_idx, BugType::DoubleFree);
        let Some(t) = result_type else {
            return true;
        };

        let bug = self.make_bug(
            value_idx,
            LocalSpot::new(bb_idx, local),
            span.clone(),
            confidence,
            t,
        );
        let target_map = if flag_cleanup {
            &mut self.bug_records.df_bugs_unwind
        } else {
            &mut self.bug_records.df_bugs
        };
        if !target_map.contains_key(&local) {
            target_map.insert(local, bug);
            if flag_cleanup {
                rap_info!(
                    "Find a double free bug {} during unwinding; add to records.",
                    local
                );
            } else {
                rap_info!("Find a double free bug {}; add to records.", local);
            }
        }
        true
    }

    pub fn dp_check(&mut self, flag_cleanup: bool) {
        rap_debug!("dangling pointer check");
        rap_debug!("current alias sets: {:?}", self.alias_graph.alias_sets);
        if flag_cleanup {
            for arg_idx in 1..self.alias_graph.arg_size() + 1 {
                self.dp_check_arg(arg_idx, flag_cleanup);
            }
        } else if self.alias_graph.values[0].may_drop
            && (self.drop_record[0].is_dropped || self.drop_record[0].has_dropped_field)
        {
            let Some(confidence) = self.check_drop_status(0) else {
                return;
            };
            if !self.bug_records.dp_bugs.contains_key(&0) {
                let bug = self.make_bug(
                    0,
                    LocalSpot::from_local(0),
                    self.alias_graph.span().clone(),
                    confidence,
                    BugType::DanglingPointer,
                );
                self.bug_records.dp_bugs.insert(0, bug);
                rap_info!("Find a dangling pointer 0; add to record.");
            }
        } else {
            for arg_idx in 0..self.alias_graph.arg_size() + 1 {
                self.dp_check_arg(arg_idx, false);
            }
        }
    }

    fn dp_check_arg(&mut self, arg_idx: usize, flag_cleanup: bool) {
        if !self.alias_graph.values[arg_idx].is_ptr() {
            return;
        }
        let Some(confidence) = self.check_drop_status(arg_idx) else {
            return;
        };
        let bug = self.make_bug(
            arg_idx,
            LocalSpot::from_local(arg_idx),
            self.alias_graph.span().clone(),
            confidence,
            BugType::DanglingPointer,
        );
        if flag_cleanup {
            if !self.bug_records.dp_bugs_unwind.contains_key(&arg_idx) {
                let drop_spot = self.drop_record[arg_idx].drop_spot;
                if self
                    .bug_records
                    .dp_bugs_unwind
                    .values()
                    .any(|e| e.drop_spot == drop_spot)
                {
                    return;
                }
                self.bug_records.dp_bugs_unwind.insert(arg_idx, bug);
                rap_info!(
                    "Find a dangling pointer {} during unwinding; add to record.",
                    arg_idx
                );
            }
        } else if !self.bug_records.dp_bugs.contains_key(&arg_idx) {
            let drop_spot = self.drop_record[arg_idx].drop_spot;
            if self
                .bug_records
                .dp_bugs
                .values()
                .any(|e| e.drop_spot == drop_spot)
            {
                return;
            }
            self.bug_records.dp_bugs.insert(arg_idx, bug);
            rap_info!("Find a dangling pointer {}; add to record.", arg_idx);
        }
    }
}
