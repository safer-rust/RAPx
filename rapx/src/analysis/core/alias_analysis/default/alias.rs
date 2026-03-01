use super::{MopAliasPair, MopFnAliasMap, block::Term, graph::*, types::*, value::*};
use crate::{analysis::graphs::scc::Scc, def_id::*};
use rustc_data_structures::fx::FxHashSet;
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{Local, Operand, Place, ProjectionElem, TerminatorKind},
    ty,
};
use std::collections::HashSet;

impl<'tcx> MopGraph<'tcx> {
    /* alias analysis for a single block */
    pub fn alias_bb(&mut self, bb_index: usize) {
        for constant in self.blocks[bb_index].const_value.clone() {
            self.constants.insert(constant.local, constant.value);
        }
        let cur_block = self.blocks[bb_index].clone();
        for assign in cur_block.assignments {
            rap_debug!("assign: {:?}", assign);
            let lv_idx = self.projection(assign.lv);
            let rv_idx = self.projection(assign.rv);

            self.assign_alias(lv_idx, rv_idx);
            rap_debug!("Alias sets: {:?}", self.alias_sets)
        }
    }

    /* Check the aliases introduced by the terminator of a basic block, i.e., a function call */
    pub fn alias_bbcall(
        &mut self,
        bb_index: usize,
        fn_map: &mut MopFnAliasMap,
        recursion_set: &mut HashSet<DefId>,
    ) {
        let cur_block = self.blocks[bb_index].clone();
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
                let lv = self.projection(*destination);
                let mut may_drop = false;
                if self.values[lv].may_drop {
                    may_drop = true;
                }

                let mut merge_vec = Vec::new();
                merge_vec.push(lv);

                for arg in args {
                    match arg.node {
                        Operand::Copy(ref p) | Operand::Move(ref p) => {
                            let rv = self.projection(*p);
                            merge_vec.push(rv);
                            if self.values[rv].may_drop {
                                may_drop = true;
                            }
                        }
                        //
                        Operand::Constant(_) => {
                            merge_vec.push(0);
                        }
                    }
                }
                if let &ty::FnDef(target_id, _) = constant.const_.ty().kind() {
                    if may_drop == false {
                        return;
                    }
                    // This function does not introduce new aliases.
                    if is_no_alias_intrinsic(target_id) {
                        return;
                    }
                    if !self.tcx.is_mir_available(target_id) {
                        return;
                    }
                    rap_debug!("Sync aliases for function call: {:?}", target_id);
                    let fn_aliases = if fn_map.contains_key(&target_id) {
                        rap_debug!("Aliases existed");
                        fn_map.get(&target_id).unwrap()
                    } else {
                        /* Fixed-point iteration: this is not perfect */
                        if recursion_set.contains(&target_id) {
                            return;
                        }
                        recursion_set.insert(target_id);
                        let mut mop_graph = MopGraph::new(self.tcx, target_id);
                        mop_graph.find_scc();
                        mop_graph.check(0, fn_map, recursion_set);
                        let ret_alias = mop_graph.ret_alias.clone();
                        rap_debug!("Find aliases of {:?}: {:?}", target_id, ret_alias);
                        fn_map.insert(target_id, ret_alias);
                        recursion_set.remove(&target_id);
                        fn_map.get(&target_id).unwrap()
                    };
                    if fn_aliases.aliases().is_empty() {
                        if let Some(l_set_idx) = self.find_alias_set(lv) {
                            self.alias_sets[l_set_idx].remove(&lv);
                        }
                    }
                    for alias in fn_aliases.aliases().iter() {
                        if !alias.valuable() {
                            continue;
                        }
                        self.handle_fn_alias(alias, &merge_vec);
                        rap_debug!("{:?}", self.alias_sets);
                    }
                } else if self.values[lv].may_drop {
                    for rv in &merge_vec {
                        if self.values[*rv].may_drop && lv != *rv && self.values[lv].is_ptr() {
                            // We assume they are alias;
                            // It is a function call and we should not distinguish left or right;
                            // Merge the alias instead of assign.
                            self.merge_alias(lv, *rv);
                        }
                    }
                }
            }
        }
    }

    /*
     * This is the function for field sensitivity
     * If the projection is a deref, we directly return its local;
     * If the projection is a field, we further make the id and its first element an alias.
     */
    pub fn projection(&mut self, place: Place<'tcx>) -> usize {
        let local = place.local.as_usize();
        rap_debug!("projection: place = {:?}, local = {:?}", place, local);
        let mut value_idx = local;
        // Projections are leveled
        // Case 1: (*6).1 involves two projections: a Deref and a Field.
        // Case 2: (6.0).1 involves two field projections.
        // We should recursively parse the projection.
        for proj in place.projection {
            rap_debug!("proj: {:?}", proj);
            let new_value_idx = self.values.len();
            match proj {
                ProjectionElem::Deref => {}
                ProjectionElem::Field(field, ty) => {
                    let field_idx = field.as_usize();
                    // If the field has not been created as a value, we crate a value;
                    if !self.values[value_idx].fields.contains_key(&field_idx) {
                        let ty_env = ty::TypingEnv::post_analysis(self.tcx, self.def_id);
                        let need_drop = ty.needs_drop(self.tcx, ty_env);
                        let may_drop = !is_not_drop(self.tcx, ty);
                        let mut node =
                            Value::new(new_value_idx, local, need_drop, need_drop || may_drop);
                        node.kind = kind(ty);
                        node.father = Some(FatherInfo::new(value_idx, field_idx));
                        self.values[value_idx].fields.insert(field_idx, node.index);
                        self.values.push(node);
                    }
                    value_idx = *self.values[value_idx].fields.get(&field_idx).unwrap();
                }
                _ => {}
            }
        }
        value_idx
    }

    /// Used to assign alias for a statement.
    /// Operation: dealiasing the left; aliasing the left with right.
    /// Synchronize the fields and father nodes iteratively.
    pub fn assign_alias(&mut self, lv_idx: usize, rv_idx: usize) {
        rap_debug!("assign_alias: lv = {:?}. rv = {:?}", lv_idx, rv_idx);

        let r_set_idx = if let Some(idx) = self.find_alias_set(rv_idx) {
            idx
        } else {
            self.alias_sets
                .push([rv_idx].into_iter().collect::<FxHashSet<usize>>());
            self.alias_sets.len() - 1
        };

        if let Some(l_set_idx) = self.find_alias_set(lv_idx) {
            if l_set_idx == r_set_idx {
                return;
            }
            self.alias_sets[l_set_idx].remove(&lv_idx);
        }
        let new_l_set_idx = r_set_idx;
        self.alias_sets[new_l_set_idx].insert(lv_idx);

        if self.values[lv_idx].fields.len() > 0 || self.values[rv_idx].fields.len() > 0 {
            self.sync_field_alias(lv_idx, rv_idx, 0, true);
        }
        if self.values[rv_idx].father != None {
            self.sync_father_alias(lv_idx, rv_idx, new_l_set_idx);
        }
    }

    // Update the aliases of fields.
    // Case 1, lv = 1; rv = 2; field of rv: 1;
    // Expected result: [1,2] [1.1,2.1];
    // Case 2, lv = 0.0, rv = 7, field of rv: 0;
    // Expected result: [0.0,7] [0.0.0,7.0]
    pub fn sync_field_alias(&mut self, lv: usize, rv: usize, depth: usize, clear_left: bool) {
        rap_debug!("sync field aliases for lv:{} rv:{}", lv, rv);

        let max_field_depth = 15;

        if depth > max_field_depth {
            return;
        }

        // For the fields of lv; we should remove them from the alias sets;
        if clear_left {
            for lv_field in self.values[lv].fields.clone().into_iter() {
                if let Some(alias_set_idx) = self.find_alias_set(lv_field.1) {
                    self.alias_sets[alias_set_idx].remove(&lv_field.1);
                }
            }
        }
        for rv_field in self.values[rv].fields.clone().into_iter() {
            rap_debug!("rv_field: {:?}", rv_field);
            if !self.values[lv].fields.contains_key(&rv_field.0) {
                let mut node = Value::new(
                    self.values.len(),
                    self.values[lv].local,
                    self.values[rv_field.1].need_drop,
                    self.values[rv_field.1].may_drop,
                );
                node.kind = self.values[rv_field.1].kind;
                node.father = Some(FatherInfo::new(lv, rv_field.0));
                self.values[lv].fields.insert(rv_field.0, node.index);
                self.values.push(node);
            }
            let lv_field_value_idx = *(self.values[lv].fields.get(&rv_field.0).unwrap());

            rap_debug!(
                "alias_set_id of rv_field {:?}",
                self.find_alias_set(rv_field.1)
            );
            if let Some(alias_set_idx) = self.find_alias_set(rv_field.1) {
                self.alias_sets[alias_set_idx].insert(lv_field_value_idx);
            }
            rap_debug!("alias sets: {:?}", self.alias_sets);
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
        let mut father = self.values[father_id].father.clone();
        while let Some(father_info) = father {
            father_id = father_info.father_value_id;
            let field_id = father_info.field_id;
            let father_value = self.values[father_id].clone();
            if let Some(alias_set_idx) = self.find_alias_set(father_id) {
                for value_idx in self.alias_sets[alias_set_idx].clone() {
                    // create a new node if the node does not exist;
                    let field_value_idx = if self.values[value_idx].fields.contains_key(&field_id) {
                        *self.values[value_idx].fields.get(&field_id).unwrap()
                    } else {
                        let mut node = Value::new(
                            self.values.len(),
                            self.values[value_idx].local,
                            self.values[value_idx].need_drop,
                            self.values[value_idx].may_drop,
                        );
                        node.kind = self.values[value_idx].kind;
                        node.father = Some(FatherInfo::new(value_idx, field_id));
                        self.values.push(node.clone());
                        self.values[value_idx].fields.insert(field_id, node.index);
                        node.index
                    };
                    // add the node to the alias_set of lv;
                    self.alias_sets[lv_alias_set_idx].insert(field_value_idx);
                }
            }
            father = father_value.father;
        }
    }

    // Handle aliases introduced by function calls.
    pub fn handle_fn_alias(&mut self, fn_alias: &MopAliasPair, arg_vec: &[usize]) {
        rap_debug!(
            "merge aliases returned by function calls, args: {:?}",
            arg_vec
        );
        rap_debug!("fn alias: {}", fn_alias);
        if fn_alias.left_local() >= arg_vec.len() || fn_alias.right_local() >= arg_vec.len() {
            return;
        }

        let mut lv = arg_vec[fn_alias.left_local()];
        let mut rv = arg_vec[fn_alias.right_local()];
        let left_local = self.values[lv].local;
        let right_local = self.values[rv].local;

        for index in fn_alias.lhs_fields().iter() {
            if !self.values[lv].fields.contains_key(index) {
                let need_drop = fn_alias.lhs_need_drop;
                let may_drop = fn_alias.lhs_may_drop;
                let mut node = Value::new(self.values.len(), left_local, need_drop, may_drop);
                node.kind = ValueKind::RawPtr;
                node.father = Some(FatherInfo::new(lv, *index));
                self.values[lv].fields.insert(*index, node.index);
                self.values.push(node);
            }
            lv = *self.values[lv].fields.get(index).unwrap();
        }
        for index in fn_alias.rhs_fields().iter() {
            if !self.values[rv].fields.contains_key(index) {
                let need_drop = fn_alias.rhs_need_drop;
                let may_drop = fn_alias.rhs_may_drop;
                let mut node = Value::new(self.values.len(), right_local, need_drop, may_drop);
                node.kind = ValueKind::RawPtr;
                node.father = Some(FatherInfo::new(rv, *index));
                self.values[rv].fields.insert(*index, node.index);
                self.values.push(node);
            }
            rv = *self.values[rv].fields.get(index).unwrap();
        }
        // It is a function call and we should not distinguish left or right;
        // Merge the alias instead of assign.
        self.merge_alias(lv, rv);
    }

    pub fn get_field_seq(&self, value: &Value) -> Vec<usize> {
        let mut field_id_seq = vec![];
        let mut node_ref = value;
        while let Some(father) = &node_ref.father {
            field_id_seq.push(father.field_id);
            node_ref = &self.values[father.father_value_id];
        }
        field_id_seq
    }

    /// Checks whether a sequence of field projections on a local MIR variable is valid.
    /// For example, if the type of a local (e.g., 0) has two fields, 0.2 or 0.3 are both invalid.
    fn is_valid_field(&self, local: usize, field_seq: &[usize]) -> bool {
        let body = self.tcx.optimized_mir(self.def_id);
        let mut ty = body.local_decls[Local::from_usize(local)].ty;
        for &fidx in field_seq {
            while let ty::TyKind::Ref(_, inner, _) | ty::TyKind::RawPtr(inner, _) = ty.kind() {
                ty = *inner;
            }
            if let ty::Adt(def, _) = ty.kind() {
                let field_count = def.all_fields().count();
                if fidx >= field_count {
                    return false;
                }
            } else {
                // 不是 ADT（struct/tuple），不能投影 field
                return false;
            }
        }
        true
    }

    //merge the result of current path to the final result.
    pub fn merge_results(&mut self) {
        rap_debug!("merge results");
        let f_node: Vec<Option<FatherInfo>> =
            self.values.iter().map(|v| v.father.clone()).collect();
        for node in self.values.iter() {
            if node.local > self.arg_size {
                continue;
            }
            for idx in 1..self.values.len() {
                if !self.is_aliasing(idx, node.index) {
                    continue;
                }

                let mut replace = None;
                if self.values[idx].local > self.arg_size {
                    for (i, fidx) in f_node.iter().enumerate() {
                        if let Some(father_info) = fidx {
                            if i != idx && i != node.index {
                                // && father_info.father_value_id == f_node[idx] {
                                for (j, v) in self.values.iter().enumerate() {
                                    if j != idx
                                        && j != node.index
                                        && self.is_aliasing(j, father_info.father_value_id)
                                        && v.local <= self.arg_size
                                    {
                                        replace = Some(&self.values[j]);
                                    }
                                }
                            }
                        }
                    }
                }

                if (self.values[idx].local <= self.arg_size || replace.is_some())
                    && idx != node.index
                    && node.local != self.values[idx].local
                {
                    let left_node;
                    let right_node;
                    match self.values[idx].local {
                        0 => {
                            left_node = match replace {
                                Some(replace_node) => replace_node,
                                None => &self.values[idx],
                            };
                            right_node = node;
                        }
                        _ => {
                            left_node = node;
                            right_node = match replace {
                                Some(replace_node) => replace_node,
                                None => &self.values[idx],
                            };
                        }
                    }
                    let mut new_alias = MopAliasPair::new(
                        left_node.local,
                        left_node.may_drop,
                        left_node.need_drop,
                        right_node.local,
                        right_node.may_drop,
                        right_node.need_drop,
                    );
                    new_alias.fact.lhs_fields = self.get_field_seq(left_node);
                    new_alias.fact.rhs_fields = self.get_field_seq(right_node);
                    if new_alias.left_local() == new_alias.right_local() {
                        continue;
                    }
                    if !self.is_valid_field(left_node.local, &new_alias.fact.lhs_fields)
                        || !self.is_valid_field(right_node.local, &new_alias.fact.rhs_fields)
                    {
                        rap_debug!("new_alias with invalid field: {:?}", new_alias);
                        continue;
                    }
                    rap_debug!("new_alias: {:?}", new_alias);
                    self.ret_alias.add_alias(new_alias);
                }
            }
        }
        self.compress_aliases();
    }

    /// Compresses the alias analysis results with a two-step procedure:
    ///
    /// 1. **Field Truncation:**
    ///    For each alias fact, any `lhs_fields` or `rhs_fields` projection longer than one element
    ///    is truncated to just its first element (e.g., `1.0.1` becomes `1.0`, `1.2.2.0.0` becomes `1.2`).
    ///    This aggressively flattens all field projections to a single field level.
    ///
    /// 2. **Containment Merging:**
    ///    For all pairs of alias facts with the same locals, if both the truncated `lhs_fields` and
    ///    `rhs_fields` of one are a (strict) prefix of another, only the more general (shorter) alias
    ///    is kept. For example:
    ///      - Keep (0, 1), remove (0.0, 1.1)
    ///      - But do **not** merge (0, 1.0) and (0, 1.1), since these have different non-prefix fields.
    ///
    /// Call this after constructing the alias set to minimize and canonicalize the result.
    pub fn compress_aliases(&mut self) {
        // Step 1: Truncate fields to only the first element if present
        let mut truncated_facts = Vec::new();
        for fact in self.ret_alias.alias_set.iter() {
            let mut new_fact = fact.clone();
            if !new_fact.fact.lhs_fields.is_empty() {
                new_fact.fact.lhs_fields = vec![new_fact.fact.lhs_fields[0]];
            }
            if !new_fact.fact.rhs_fields.is_empty() {
                new_fact.fact.rhs_fields = vec![new_fact.fact.rhs_fields[0]];
            }
            truncated_facts.push(new_fact);
        }
        // Clean up alias set and replace with truncated
        self.ret_alias.alias_set.clear();
        for fact in truncated_facts {
            self.ret_alias.alias_set.insert(fact);
        }

        // Step 2: Containment merging
        // For the same (left_local, rhs_local), if (a, b) is a prefix of (a', b'), keep only (a, b)
        let aliases: Vec<MopAliasPair> = self.ret_alias.alias_set.iter().cloned().collect();
        let n = aliases.len();
        let mut to_remove: HashSet<MopAliasPair> = HashSet::new();

        for i in 0..n {
            for j in 0..n {
                if i == j || to_remove.contains(&aliases[j]) {
                    continue;
                }
                let a = &aliases[i].fact;
                let b = &aliases[j].fact;
                // Only merge if both lhs/rhs locals are equal and BOTH are strict prefixes
                if a.left_local() == b.left_local() && a.right_local() == b.right_local() {
                    if a.lhs_fields.len() <= b.lhs_fields.len()
                    && a.lhs_fields == b.lhs_fields[..a.lhs_fields.len()]
                    && a.rhs_fields.len() <= b.rhs_fields.len()
                    && a.rhs_fields == b.rhs_fields[..a.rhs_fields.len()]
                    // Exclude case where fields are exactly the same (avoid self-removal)
                    && (a.lhs_fields.len() < b.lhs_fields.len() || a.rhs_fields.len() < b.rhs_fields.len())
                    {
                        to_remove.insert(aliases[j].clone());
                    }
                }
            }
        }
        for alias in to_remove {
            self.ret_alias.alias_set.remove(&alias);
        }
    }

    #[inline(always)]
    pub fn find_alias_set(&self, e: usize) -> Option<usize> {
        self.alias_sets.iter().position(|set| set.contains(&e))
    }

    #[inline(always)]
    pub fn is_aliasing(&self, e1: usize, e2: usize) -> bool {
        let s1 = self.find_alias_set(e1);
        let s2 = self.find_alias_set(e2);
        s1.is_some() && s1 == s2
    }

    pub fn merge_alias(&mut self, e1: usize, e2: usize) {
        let mut s1 = self.find_alias_set(e1);
        let mut s2 = self.find_alias_set(e2);

        // Create set for e1 if needed
        if s1.is_none() {
            self.alias_sets
                .push([e1].into_iter().collect::<FxHashSet<usize>>());
            s1 = Some(self.alias_sets.len() - 1);
        }

        // Create set for e2 if needed
        if s2.is_none() {
            self.alias_sets
                .push([e2].into_iter().collect::<FxHashSet<usize>>());
            s2 = Some(self.alias_sets.len() - 1);
        }

        // After creation, fetch indices (unwrap OK)
        let idx1 = s1.unwrap();
        let idx2 = s2.unwrap();

        if idx1 == idx2 {
            return;
        }

        let set2 = self.alias_sets.remove(idx2);
        // If idx2 < idx1, removing idx2 shifts idx1 down by one
        let idx1 = if idx2 < idx1 { idx1 - 1 } else { idx1 };
        self.alias_sets[idx1].extend(set2);

        if self.values[e1].fields.len() > 0 {
            self.sync_field_alias(e2, e1, 0, false);
        }
        if self.values[e2].fields.len() > 0 {
            self.sync_field_alias(e1, e2, 0, false);
        }
        if self.values[e1].father != None {
            self.sync_father_alias(e2, e1, idx1);
        }
        if self.values[e2].father != None {
            self.sync_father_alias(e1, e2, idx1);
        }
    }

    #[inline(always)]
    pub fn get_alias_set(&mut self, e: usize) -> Option<FxHashSet<usize>> {
        if let Some(idx) = self.find_alias_set(e) {
            Some(self.alias_sets[idx].clone())
        } else {
            None
        }
    }
}

pub fn is_no_alias_intrinsic(def_id: DefId) -> bool {
    let v = [call_mut_opt(), clone_opt(), take_opt()];
    contains(&v, def_id)
}
