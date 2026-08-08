use crate::analysis::alias::default::types::ValueKind;
use crate::analysis::alias::observer::AliasObserver;
use crate::analysis::points_to::slot::{AbstractLoc, Slot};
use rustc_abi::FieldIdx;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::{AggregateKind, Operand, Rvalue, StatementKind, TerminatorKind};
use rustc_span::Span;

use super::MopFnAliasMap;
use super::graph::AliasGraph;

impl<'tcx> AliasGraph<'tcx> {
    pub fn init_pts_graph(&mut self) {
        self.pts_graph = crate::analysis::points_to::builder::from_body(self.tcx(), self.def_id());
        for val in self.values.iter_mut() {
            let slot = crate::analysis::points_to::slot::Slot::new(val.local);
            if let Some(si) = self.pts_graph.get_slot_idx(&slot) {
                val.slot_idx = Some(si);
            }
        }
    }

    /// Unified basic-block MIR processing, shared by MoP alias and SafeDrop.
    pub fn alias_bb(&mut self, bb_index: usize, obs: &mut dyn AliasObserver) {
        let body = self.tcx().optimized_mir(self.def_id());
        let bb = &body.basic_blocks[rustc_middle::mir::BasicBlock::from(bb_index)];

        for stmt in &bb.statements {
            let span = stmt.source_info.span;
            match &stmt.kind {
                StatementKind::Assign(assign) => {
                    let (place, rvalue) = &**assign;
                    self.process_assignment(place, rvalue, span, obs);
                }
                _ => {}
            }
        }
    }

    fn process_assignment(
        &mut self,
        place: &rustc_middle::mir::Place<'tcx>,
        rvalue: &rustc_middle::mir::Rvalue<'tcx>,
        span: Span,
        obs: &mut dyn AliasObserver,
    ) {
        let lv_slot = Slot::from_mir_place(place);
        let lv_pts = self.pts_graph.ensure_slot(lv_slot.clone(), false, false);
        if !self.pts_graph.may_drop(lv_pts) {
            return;
        }
        let lv_val = self.projection(*place);

        match rvalue {
            Rvalue::Use(operand, ..) => match operand {
                Operand::Copy(rv_place) => {
                    if let Some((rv_val, rv_pts)) = self.resolve_operand(rv_place) {
                        obs.on_value_use(self, rv_val, span, false);
                        self.pts_graph.assign_value(lv_pts, rv_pts);
                        obs.on_value_assign(self, lv_val);
                    }
                }
                Operand::Move(rv_place) => {
                    if let Some((rv_val, rv_pts)) = self.resolve_operand(rv_place) {
                        self.move_sources.insert(lv_val, rv_val);
                        obs.on_value_use(self, rv_val, span, false);
                        if obs.track_all_moves()
                            || self.pts_graph.slot_kind(rv_pts) == ValueKind::RawPtr
                        {
                            self.pts_graph.assign_value(lv_pts, rv_pts);
                        }
                        obs.on_value_assign(self, lv_val);
                    }
                }
                Operand::Constant(_) => {}
                #[cfg(rapx_rustc_ge_196)]
                Operand::RuntimeChecks(_) => {}
            },
            Rvalue::Ref(_, _, rv_place)
            | Rvalue::RawPtr(_, rv_place)
            | Rvalue::CopyForDeref(rv_place) => {
                let rv_slot = Slot::from_mir_place(rv_place);
                if let Some(rv_val) = self.place_to_value_idx(rv_place) {
                    obs.on_value_use(self, rv_val, span, false);
                }
                let rv_slot_clone = rv_slot.clone();
                self.pts_graph
                    .assign_pointee(lv_pts, AbstractLoc::Slot(rv_slot));
                if let Some(rv_pts) = self.pts_graph.get_slot_idx(&rv_slot_clone) {
                    self.pts_graph.merge_equivalence(lv_pts, rv_pts);
                }
                obs.on_value_assign(self, lv_val);
            }
            Rvalue::Cast(_, operand, _) => match operand {
                Operand::Copy(rv_place) | Operand::Move(rv_place) => {
                    if let Some((rv_val, rv_pts)) = self.resolve_operand(rv_place) {
                        obs.on_value_use(self, rv_val, span, false);
                        self.pts_graph.assign_value(lv_pts, rv_pts);
                        obs.on_value_assign(self, lv_val);
                    }
                }
                _ => {}
            },
            Rvalue::Aggregate(kind, operands) => {
                match kind.as_ref() {
                    AggregateKind::Tuple | AggregateKind::Adt(..) => {
                        for (field_idx, operand) in operands.iter_enumerated() {
                            match operand {
                                Operand::Copy(rv_place) | Operand::Move(rv_place) => {
                                    if let Some((rv_val, rv_pts)) = self.resolve_operand(rv_place) {
                                        let field_slot = lv_slot.project(field_idx.as_usize());
                                        let field_pts =
                                            self.pts_graph.ensure_slot(field_slot, false, false);
                                        // Ensure value entry exists for the field
                                        let field_val = self.projection_field(place, field_idx);
                                        obs.on_value_use(self, rv_val, span, false);
                                        self.pts_graph.assign_value(field_pts, rv_pts);
                                        obs.on_value_assign(self, field_val);
                                    }
                                }
                                _ => {}
                            }
                        }
                    }
                    _ => {
                        for operand in operands {
                            match operand {
                                Operand::Copy(rv_place) | Operand::Move(rv_place) => {
                                    if let Some((rv_val, rv_pts)) = self.resolve_operand(rv_place) {
                                        obs.on_value_use(self, rv_val, span, false);
                                        self.pts_graph.assign_value(lv_pts, rv_pts);
                                        obs.on_value_assign(self, lv_val);
                                    }
                                }
                                _ => {}
                            }
                        }
                    }
                }
            }
            #[cfg(not(rapx_rustc_ge_196))]
            Rvalue::ShallowInitBox(operand, _) => match operand {
                Operand::Copy(rv_place) | Operand::Move(rv_place) => {
                    if let Some((rv_val, rv_pts)) = self.resolve_operand(rv_place) {
                        obs.on_value_use(self, rv_val, span, false);
                        self.pts_graph.assign_value(lv_pts, rv_pts);
                        obs.on_value_assign(self, lv_val);
                    }
                }
                _ => {}
            },
            Rvalue::Discriminant(rv_place) => {
                if let Some((rv_val, rv_pts)) = self.resolve_operand(rv_place) {
                    obs.on_value_use(self, rv_val, span, false);
                    self.pts_graph.assign_value(lv_pts, rv_pts);
                    obs.on_value_assign(self, lv_val);
                }
            }
            _ => {}
        }
    }

    /// Resolve a MIR Place to (value_index, pts_slot_index) if it may drop.
    fn resolve_operand(
        &mut self,
        place: &rustc_middle::mir::Place<'tcx>,
    ) -> Option<(usize, usize)> {
        let slot = Slot::from_mir_place(place);
        let pts_idx = self.pts_graph.ensure_slot(slot, false, false);
        if !self.pts_graph.may_drop(pts_idx) {
            return None;
        }
        let val_idx = self.projection(*place);
        Some((val_idx, pts_idx))
    }

    /// Lookup value index for a place without dynamic creation.
    fn place_to_value_idx(&self, place: &rustc_middle::mir::Place<'tcx>) -> Option<usize> {
        let slot = Slot::from_mir_place(place);
        self.slot_to_value_idx(&slot)
    }

    /// Ensure value entry exists for a field projection.
    fn projection_field(
        &mut self,
        base: &rustc_middle::mir::Place<'tcx>,
        field_idx: FieldIdx,
    ) -> usize {
        let body = self.tcx().optimized_mir(self.def_id());
        let base_ty = base.ty(&body.local_decls, self.tcx()).ty;
        let field_ty = match base_ty.kind() {
            rustc_middle::ty::TyKind::Tuple(fields) => {
                fields.get(field_idx.as_usize()).copied().unwrap_or(base_ty)
            }
            rustc_middle::ty::TyKind::Adt(..) => base_ty,
            _ => base_ty,
        };
        let field_place = self.tcx().mk_place_field(*base, field_idx, field_ty);
        self.projection(field_place)
    }

    /// Reverse lookup: given a Slot, find the corresponding value index.
    pub fn slot_to_value_idx(&self, slot: &Slot) -> Option<usize> {
        if slot.fields.is_empty() {
            let local = slot.local;
            if local < self.values.len() {
                return Some(local);
            }
            return None;
        }
        let mut cur = slot.local;
        if cur >= self.values.len() {
            return None;
        }
        for &field_id in &slot.fields {
            cur = *self.values[cur].fields.get(&field_id)?;
        }
        Some(cur)
    }

    /// Unified call-site processing, shared by MoP alias and SafeDrop.
    pub fn alias_bbcall(
        &mut self,
        bb_index: usize,
        fn_map: &MopFnAliasMap,
        obs: &mut dyn AliasObserver,
    ) {
        let (merge_slots, ret_local, may_drop_count, target_id, span) =
            self.parse_call_slots(bb_index);
        if merge_slots.is_empty() {
            return;
        }

        // UAF check for arguments (skip return-value slot at index 0)
        for &(val_idx, _) in merge_slots.iter().skip(1) {
            if val_idx != 0 {
                obs.on_value_use(self, val_idx, span, true);
            }
        }

        if may_drop_count <= 1 {
            let (ret_val, ret_slot) = merge_slots[0];
            if ret_val != 0 && self.pts_graph.may_drop(ret_slot) {
                self.pts_graph.reset_partition(ret_slot);
                obs.on_value_assign(self, ret_val);
            }
            return;
        }

        match target_id {
            Some(id) => {
                if super::alias::is_no_alias_intrinsic(id) {
                    return;
                }
                if !self.tcx().is_mir_available(id) {
                    let (ret_val, _) = merge_slots[0];
                    if ret_val != 0 && self.value_is_ptr(ret_val) {
                        let slot_args: Vec<usize> = merge_slots.iter().map(|&(_, s)| s).collect();
                        self.pts_graph.conservative_call_merge(&slot_args);
                        obs.on_value_assign(self, ret_val);
                    }
                    return;
                }
                self.apply_fn_alias_results_pts(id, &merge_slots, fn_map, obs);
            }
            None => {
                let (ret_val, _) = merge_slots[0];
                if ret_val != 0
                    && self
                        .pts_graph
                        .get_slot_idx(&Slot::new(ret_local))
                        .map_or(false, |si| self.pts_graph.slot_is_ptr(si))
                {
                    let slot_args: Vec<usize> = merge_slots.iter().map(|&(_, s)| s).collect();
                    self.pts_graph.conservative_call_merge(&slot_args);
                    obs.on_value_assign(self, ret_val);
                }
            }
        }

        let (ret_val, _) = merge_slots[0];
        if ret_val != 0 && self.pts_graph.may_drop(merge_slots[0].1) {
            obs.on_value_assign(self, ret_val);
        }
    }

    /// Parse call terminator, returning slot-based merge info.
    fn parse_call_slots(
        &mut self,
        bb_index: usize,
    ) -> (Vec<(usize, usize)>, usize, usize, Option<DefId>, Span) {
        let terminator = match self.terminator(bb_index) {
            Some(t) => t.clone(),
            None => return (vec![], 0, 0, None, rustc_span::DUMMY_SP),
        };
        let TerminatorKind::Call {
            func: ref func_op,
            ref args,
            ref destination,
            ..
        } = terminator.kind
        else {
            return (vec![], 0, 0, None, rustc_span::DUMMY_SP);
        };
        let span = terminator.source_info.span;

        let target_id = match func_op {
            Operand::Constant(c) => match c.ty().kind() {
                rustc_middle::ty::FnDef(id, _) => Some(*id),
                _ => None,
            },
            _ => None,
        };

        let ret_local = destination.local.as_usize();
        let ret_slot = Slot::new(ret_local);
        let ret_pts = self.pts_graph.ensure_slot(ret_slot, false, false);
        let ret_val = self.projection(*destination);
        let mut result = vec![(ret_val, ret_pts)];
        let mut may_drop_count: usize = if self.pts_graph.may_drop(ret_pts) {
            1
        } else {
            0
        };

        for arg in args {
            match arg.node {
                Operand::Copy(ref p) | Operand::Move(ref p) => {
                    let arg_local = p.local.as_usize();
                    let arg_slot = Slot::new(arg_local);
                    let arg_pts = self.pts_graph.ensure_slot(arg_slot, false, false);
                    let arg_val = self.projection(*p);
                    if self.pts_graph.may_drop(arg_pts) {
                        may_drop_count += 1;
                    }
                    result.push((arg_val, arg_pts));
                }
                Operand::Constant(_) => {
                    result.push((0, 0));
                }
                #[cfg(rapx_rustc_ge_196)]
                Operand::RuntimeChecks(_) => {}
            }
        }

        (result, ret_local, may_drop_count, target_id, span)
    }

    fn apply_fn_alias_results_pts(
        &mut self,
        target_id: DefId,
        merge_vec: &[(usize, usize)],
        fn_map: &MopFnAliasMap,
        obs: &mut dyn AliasObserver,
    ) {
        let Some(fn_aliases) = fn_map.get(&target_id) else {
            return;
        };
        if fn_aliases.aliases().is_empty() {
            return;
        }
        let unified: crate::analysis::alias::FnAliasPairs = From::from(fn_aliases.clone());
        let slot_args: Vec<usize> = merge_vec.iter().map(|&(_, s)| s).collect();
        self.pts_graph.apply_callee_summary(&unified, &slot_args);
        obs.on_state_change(self);
    }

    pub fn merge_results_pts(&mut self) {
        let pairs = self.pts_graph.fn_alias_pairs(self.arg_size());
        for alias in pairs.aliases() {
            let lv_local = alias.left_local();
            let rv_local = alias.right_local();
            let lv_slot = self.value_to_slot_idx(lv_local).unwrap_or(lv_local);
            let rv_slot = self.value_to_slot_idx(rv_local).unwrap_or(rv_local);
            let mut mop_alias = super::MopAliasPair::new(
                alias.left_local(),
                self.pts_graph.may_drop(lv_slot),
                self.pts_graph.need_drop(lv_slot),
                alias.right_local(),
                self.pts_graph.may_drop(rv_slot),
                self.pts_graph.need_drop(rv_slot),
            );
            mop_alias.fact = alias.clone();
            self.ret_alias.add_alias(mop_alias);
        }
    }
}
