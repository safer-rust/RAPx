use rustc_middle::{
    mir::{Operand, Place, ProjectionElem, TerminatorKind},
    ty::{self},
};

use super::{drop::*, graph::*};
use crate::analysis::core::alias_analysis::default::{
    MopAliasPair, MopFnAliasMap, alias::is_no_alias_intrinsic, block::Term, types::*, value::*,
};
use rustc_data_structures::fx::FxHashSet;

impl<'tcx> SafeDropGraph<'tcx> {
    /* alias analysis for a single block */
    pub fn alias_bb(&mut self, bb_index: usize) {
        for constant in self.mop_graph.blocks[bb_index].const_value.clone() {
            self.mop_graph
                .constants
                .insert(constant.local, constant.value);
        }
        let cur_block = self.mop_graph.blocks[bb_index].clone();
        for assign in cur_block.assignments {
            let lv_idx = self.projection(assign.lv);
            let rv_idx = self.projection(assign.rv);
            // We should perform uaf check before alias analysis.
            // Example: *1 = 4; when *1 is dangling.
            // Perfoming alias analysis first would introduce false positives.
            self.uaf_check(rv_idx, bb_index, assign.span, false);
            self.assign_alias(lv_idx, rv_idx);
            self.clear_drop_info(lv_idx);

            rap_debug!("Alias sets: {:?}", self.mop_graph.alias_sets.clone());
        }
    }

    /* Check the aliases introduced by the terminators (function call) of a scc block */
    pub fn alias_bbcall(&mut self, bb_index: usize, fn_map: &MopFnAliasMap) {
        let cur_block = self.mop_graph.blocks[bb_index].clone();
        if let Term::Call(call) | Term::Drop(call) = cur_block.terminator {
            if let TerminatorKind::Call {
                func: Operand::Constant(ref constant),
                ref args,
                ref destination,
                target: _,
                unwind: _,
                call_source: _,
                fn_span: _,
            } = call.kind
            {
                rap_debug!("alias_bbcall in {:?}: {:?}", bb_index, call);
                let lv = self.projection(destination.clone());
                let mut merge_vec = Vec::new();
                merge_vec.push(lv);
                let mut may_drop_flag = 0;
                if self.mop_graph.values[lv].may_drop {
                    may_drop_flag += 1;
                }
                for arg in args {
                    match arg.node {
                        Operand::Copy(ref p) | Operand::Move(ref p) => {
                            let rv = self.projection(p.clone());
                            self.uaf_check(rv, bb_index, call.source_info.span, true);
                            merge_vec.push(rv);
                            if self.mop_graph.values[rv].may_drop {
                                may_drop_flag += 1;
                            }
                        }
                        Operand::Constant(_) => {
                            merge_vec.push(0);
                        }
                    }
                }
                if let ty::FnDef(target_id, _) = constant.const_.ty().kind() {
                    if may_drop_flag > 1 {
                        // This function does not introduce new aliases.
                        if is_no_alias_intrinsic(*target_id) {
                            return;
                        }
                        if self.mop_graph.tcx.is_mir_available(*target_id) {
                            rap_debug!("fn_map: {:?}", fn_map);
                            if fn_map.contains_key(&target_id) {
                                let fn_aliases = fn_map.get(&target_id).unwrap();
                                rap_debug!("aliases of the fn: {:?}", fn_aliases);
                                if fn_aliases.aliases().is_empty() {
                                    if let Some(l_set_idx) = self.mop_graph.find_alias_set(lv) {
                                        self.mop_graph.alias_sets[l_set_idx].remove(&lv);
                                    }
                                }
                                for alias in fn_aliases.aliases().iter() {
                                    if !alias.valuable() {
                                        continue;
                                    }
                                    self.handle_fn_alias(alias, &merge_vec);
                                }
                            }
                        } else {
                            if self.mop_graph.values[lv].may_drop {
                                for rv in &merge_vec {
                                    if self.mop_graph.values[*rv].may_drop
                                        && lv != *rv
                                        && self.mop_graph.values[lv].is_ptr()
                                    {
                                        self.mop_graph.merge_alias(lv, *rv);
                                        self.clear_drop_info(lv);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    pub fn assign_alias(&mut self, lv_idx: usize, rv_idx: usize) {
        rap_debug!("assign_alias: lv = {:?}. rv = {:?}", lv_idx, rv_idx);
        let r_set_idx = if let Some(idx) = self.mop_graph.find_alias_set(rv_idx) {
            idx
        } else {
            self.mop_graph
                .alias_sets
                .push([rv_idx].into_iter().collect::<FxHashSet<usize>>());
            self.mop_graph.alias_sets.len() - 1
        };

        if let Some(l_set_idx) = self.mop_graph.find_alias_set(lv_idx) {
            if l_set_idx == r_set_idx {
                return;
            }
            self.mop_graph.alias_sets[l_set_idx].remove(&lv_idx);
        }
        self.mop_graph.alias_sets[r_set_idx].insert(lv_idx);

        if self.mop_graph.values[lv_idx].fields.len() > 0
            || self.mop_graph.values[rv_idx].fields.len() > 0
        {
            self.sync_field_alias(lv_idx, rv_idx, 0, true);
        }
        if self.mop_graph.values[rv_idx].father != None {
            self.sync_father_alias(lv_idx, rv_idx, r_set_idx);
        }
    }

    // Update the aliases of fields.
    // Case 1, lv = 1; rv = 2; field of rv: 1;
    // Expected result: [1,2] [1.1,2.1];
    // Case 2, lv = 0.0, rv = 7, field of rv: 0;
    // Expected result: [0.0,7] [0.0.0,7.0]
    pub fn sync_field_alias(&mut self, lv: usize, rv: usize, depth: usize, clear_left: bool) {
        rap_debug!("sync field aliases for lv:{} rv:{}", lv, rv);

        let max_field_depth = match std::env::var_os("MOP") {
            Some(val) if val == "0" => 10,
            Some(val) if val == "1" => 20,
            Some(val) if val == "2" => 30,
            Some(val) if val == "3" => 50,
            _ => 15,
        };

        if depth > max_field_depth {
            return;
        }

        // For the fields of lv; we should remove them from the alias sets;
        if clear_left {
            for lv_field in self.mop_graph.values[lv].fields.clone().into_iter() {
                if let Some(alias_set_idx) = self.mop_graph.find_alias_set(lv_field.1) {
                    self.mop_graph.alias_sets[alias_set_idx].remove(&lv_field.1);
                }
            }
        }
        for rv_field in self.mop_graph.values[rv].fields.clone().into_iter() {
            rap_debug!("rv_field: {:?}", rv_field);
            if !self.mop_graph.values[lv].fields.contains_key(&rv_field.0) {
                let new_index = self.mop_graph.values.len();
                let mut node = Value::new(
                    new_index,
                    self.mop_graph.values[lv].local,
                    self.mop_graph.values[rv_field.1].need_drop,
                    self.mop_graph.values[rv_field.1].may_drop,
                );
                node.kind = self.mop_graph.values[rv_field.1].kind;
                node.father = Some(FatherInfo::new(lv, rv_field.0));
                self.mop_graph.values[lv]
                    .fields
                    .insert(rv_field.0, node.index);
                self.mop_graph.values.push(node);
                self.drop_record
                    .push(DropRecord::from(new_index, &self.drop_record[lv]));
            }
            let lv_field_value_idx = *(self.mop_graph.values[lv].fields.get(&rv_field.0).unwrap());

            rap_debug!(
                "alias_set_id of rv_field {:?}",
                self.mop_graph.find_alias_set(rv_field.1)
            );
            if let Some(alias_set_idx) = self.mop_graph.find_alias_set(rv_field.1) {
                self.mop_graph.alias_sets[alias_set_idx].insert(lv_field_value_idx);
            }
            rap_debug!("alias sets: {:?}", self.mop_graph.alias_sets);
            self.sync_field_alias(lv_field_value_idx, rv_field.1, depth + 1, true);
        }
    }

    // For example,
    // Case 1: lv = 1; rv = 2.0; alias set [2, 3]
    // Expected result: [1, 2.0, 3.0], [2, 3];
    // Case 2: lv = 1.0; rv = 2; alias set [1, 3]
    // Expected result: [1.0, 2], [1, 3]
    pub fn sync_father_alias(&mut self, lv: usize, rv: usize, lv_alias_set_idx: usize) {
        rap_debug!("sync father aliases for lv:{} rv:{}", lv, rv);
        let mut father_id = rv;
        let mut father = self.mop_graph.values[father_id].father.clone();
        while let Some(father_info) = father {
            father_id = father_info.father_value_id;
            let field_id = father_info.field_id;
            let father_value = self.mop_graph.values[father_id].clone();
            if let Some(alias_set_idx) = self.mop_graph.find_alias_set(father_id) {
                for value_idx in self.mop_graph.alias_sets[alias_set_idx].clone() {
                    // create a new node if the node does not exist;
                    let field_value_idx = if self.mop_graph.values[value_idx]
                        .fields
                        .contains_key(&field_id)
                    {
                        *self.mop_graph.values[value_idx]
                            .fields
                            .get(&field_id)
                            .unwrap()
                    } else {
                        let new_index = self.mop_graph.values.len();
                        let mut node = Value::new(
                            new_index,
                            self.mop_graph.values[value_idx].local,
                            self.mop_graph.values[value_idx].need_drop,
                            self.mop_graph.values[value_idx].may_drop,
                        );
                        node.kind = self.mop_graph.values[value_idx].kind;
                        node.father = Some(FatherInfo::new(value_idx, field_id));
                        self.mop_graph.values.push(node.clone());
                        self.mop_graph.values[value_idx]
                            .fields
                            .insert(field_id, node.index);
                        self.drop_record
                            .push(DropRecord::from(new_index, &self.drop_record[lv]));
                        node.index
                    };
                    // add the node to the alias_set of lv;
                    self.mop_graph.alias_sets[lv_alias_set_idx].insert(field_value_idx);
                }
            }
            father = father_value.father;
        }
    }

    /*
     * This is the function for field sensitivity.
     * If the projection is a deref, we directly return its local;
     * If the id is not a ref (e.g., 1.0), we project it to the value index.
     *
     */
    pub fn projection(&mut self, place: Place<'tcx>) -> usize {
        let local = place.local.as_usize();
        let mut value_idx = local;
        // Projections are leveled
        // Case 1: (*6).1 involves two projections: a Deref and a Field.
        // Case 2: (6.0).1 involves two field projections.
        // We should recursively parse the projection.
        for proj in place.projection {
            let new_value_idx = self.mop_graph.values.len();
            match proj {
                ProjectionElem::Deref => {}
                ProjectionElem::Field(field, ty) => {
                    let field_idx = field.as_usize();
                    if !self.mop_graph.values[value_idx]
                        .fields
                        .contains_key(&field_idx)
                    {
                        let ty_env =
                            ty::TypingEnv::post_analysis(self.mop_graph.tcx, self.mop_graph.def_id);
                        let need_drop = ty.needs_drop(self.mop_graph.tcx, ty_env);
                        let may_drop = !is_not_drop(self.mop_graph.tcx, ty);
                        let mut node =
                            Value::new(new_value_idx, local, need_drop, need_drop || may_drop);
                        node.kind = kind(ty);
                        node.father = Some(FatherInfo::new(value_idx, field_idx));
                        self.mop_graph.values[value_idx]
                            .fields
                            .insert(field_idx, node.index);
                        self.mop_graph.values.push(node);
                        // The drop status is the same as its father.
                        self.drop_record.push(DropRecord::from(
                            new_value_idx,
                            &self.drop_record[value_idx],
                        ));
                    }
                    value_idx = *self.mop_graph.values[value_idx]
                        .fields
                        .get(&field_idx)
                        .unwrap();
                }
                _ => {}
            }
        }
        value_idx
    }

    //inter-procedure instruction to merge alias.
    pub fn handle_fn_alias(&mut self, fn_alias: &MopAliasPair, arg_vec: &Vec<usize>) {
        rap_debug!("ret_alias: {:?}", fn_alias);
        if fn_alias.left_local() >= arg_vec.len() || fn_alias.right_local() >= arg_vec.len() {
            return;
        }

        let mut lv = arg_vec[fn_alias.left_local()];
        self.clear_drop_info(lv);
        let mut rv = arg_vec[fn_alias.right_local()];
        let left_local = self.mop_graph.values[lv].local;
        let right_local = self.mop_graph.values[rv].local;

        for index in fn_alias.lhs_fields().iter() {
            if !self.mop_graph.values[lv].fields.contains_key(&index) {
                let new_index = self.mop_graph.values.len();
                let need_drop = fn_alias.lhs_need_drop;
                let may_drop = fn_alias.lhs_may_drop;
                let mut node = Value::new(new_index, left_local, need_drop, may_drop);
                node.kind = ValueKind::RawPtr;
                node.father = Some(FatherInfo::new(lv, *index));
                self.mop_graph.values[lv].fields.insert(*index, node.index);
                self.drop_record
                    .push(DropRecord::from(new_index, &self.drop_record[lv]));
                self.mop_graph.values.push(node);
            }
            lv = *self.mop_graph.values[lv].fields.get(&index).unwrap();
        }
        for index in fn_alias.rhs_fields().iter() {
            if !self.mop_graph.values[rv].fields.contains_key(&index) {
                let new_index = self.mop_graph.values.len();
                let need_drop = fn_alias.rhs_need_drop;
                let may_drop = fn_alias.rhs_may_drop;
                let mut node = Value::new(new_index, right_local, need_drop, may_drop);
                node.kind = ValueKind::RawPtr;
                node.father = Some(FatherInfo::new(rv, *index));
                self.mop_graph.values[rv].fields.insert(*index, node.index);
                self.drop_record
                    .push(DropRecord::from(new_index, &self.drop_record[rv]));
                self.mop_graph.values.push(node);
            }
            rv = *self.mop_graph.values[rv].fields.get(&index).unwrap();
        }
        self.merge_alias(lv, rv);
    }

    pub fn merge_alias(&mut self, e1: usize, e2: usize) {
        rap_debug!("merge alias: {}, {}", e1, e2);
        let mut s1 = self.mop_graph.find_alias_set(e1);
        let mut s2 = self.mop_graph.find_alias_set(e2);

        // Create set for e1 if needed
        if s1.is_none() {
            self.mop_graph
                .alias_sets
                .push([e1].into_iter().collect::<FxHashSet<usize>>());
            s1 = Some(self.mop_graph.alias_sets.len() - 1);
        }

        // Create set for e2 if needed
        if s2.is_none() {
            self.mop_graph
                .alias_sets
                .push([e2].into_iter().collect::<FxHashSet<usize>>());
            s2 = Some(self.mop_graph.alias_sets.len() - 1);
        }

        // After creation, fetch indices (unwrap OK)
        let idx1 = s1.unwrap();
        let idx2 = s2.unwrap();

        if idx1 == idx2 {
            return;
        }

        let set2 = self.mop_graph.alias_sets.remove(idx2);
        // If idx2 < idx1, removing idx2 shifts idx1 down by one
        let idx1 = if idx2 < idx1 { idx1 - 1 } else { idx1 };
        self.mop_graph.alias_sets[idx1].extend(set2);

        if self.mop_graph.values[e1].fields.len() > 0 {
            self.sync_field_alias(e2, e1, 0, false);
        }
        if self.mop_graph.values[e2].fields.len() > 0 {
            self.sync_field_alias(e1, e2, 0, false);
        }
        if self.mop_graph.values[e1].father != None {
            self.sync_father_alias(e2, e1, idx1);
        }
        if self.mop_graph.values[e2].father != None {
            self.sync_father_alias(e1, e2, idx1);
        }
    }
}
