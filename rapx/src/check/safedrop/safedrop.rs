use super::observer::SafeDropObserver;
use super::{bug_records::*, checks, corner_case::*, drop::*, graph::*};
use crate::{
    analysis::alias::default::MopFnAliasMap,
    analysis::path::{PathNode, PathTree},
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
    fn dfs_safedrop(
        &mut self,
        node: &PathNode,
        path: &mut Vec<usize>,
        fn_map: &MopFnAliasMap,
    ) -> Result<(), ()> {
        path.push(node.block);
        {
            let mut obs = SafeDropObserver {
                drop_record: &mut self.drop_record,
                bug_records: &mut self.bug_records,
                current_bb: node.block,
            };
            self.alias_graph.alias_bb(node.block, &mut obs);
            self.alias_graph.alias_bbcall(node.block, fn_map, &mut obs);
        }
        self.drop_check(node.block);

        let saved_values = self.alias_graph.values.clone();
        let saved_pts_graph = self.alias_graph.pts_graph.clone();
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
            self.alias_graph.pts_graph = saved_pts_graph.clone();
            self.drop_record = saved_drop_record.clone();
            self.dfs_safedrop(child, path, fn_map)?;
        }

        path.pop();
        Ok(())
    }

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
                    #[cfg(not(rapx_ge_99))]
                        async_fut: _,
                } => {
                    if !self.drop_heap_item_check(place) {
                        return;
                    }
                    let value_idx = self.alias_graph.projection(place.clone());
                    checks::sync_drop_record(&self.alias_graph, &mut self.drop_record);
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
                        checks::sync_drop_record(&self.alias_graph, &mut self.drop_record);
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

    pub fn process_function_paths_opt(
        &mut self,
        precomputed_paths: Option<PathTree>,
        fn_map: &MopFnAliasMap,
    ) {
        self.alias_graph.init_pts_graph();
        let paths = precomputed_paths.unwrap_or_else(|| self.alias_graph.enumerate_paths());
        let Some(root) = paths.root() else { return };
        let mut path = Vec::new();
        let _ = self.dfs_safedrop(root, &mut path, fn_map);
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

    pub fn df_check(
        &mut self,
        value_idx: usize,
        bb_idx: usize,
        span: Span,
        flag_cleanup: bool,
    ) -> bool {
        let local = self.alias_graph.values[value_idx].local;
        rap_debug!(
            "df_check: value_idx = {:?}, bb_idx = {:?}",
            value_idx,
            bb_idx,
        );
        let Some(confidence) =
            checks::check_drop_status(&self.alias_graph, &mut self.drop_record, value_idx)
        else {
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

        let bug = checks::make_bug(
            &self.drop_record[value_idx],
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
        if flag_cleanup {
            for arg_idx in 1..self.alias_graph.arg_size() + 1 {
                self.dp_check_arg(arg_idx, flag_cleanup);
            }
        } else if self.alias_graph.value_may_drop(0)
            && (self.drop_record[0].is_dropped || self.drop_record[0].has_dropped_field)
        {
            let Some(confidence) =
                checks::check_drop_status(&self.alias_graph, &mut self.drop_record, 0)
            else {
                return;
            };
            if !self.bug_records.dp_bugs.contains_key(&0) {
                let bug = checks::make_bug(
                    &self.drop_record[0],
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
        if !self.alias_graph.value_is_ptr(arg_idx) {
            return;
        }
        let Some(confidence) =
            checks::check_drop_status(&self.alias_graph, &mut self.drop_record, arg_idx)
        else {
            return;
        };
        let bug = checks::make_bug(
            &self.drop_record[arg_idx],
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
