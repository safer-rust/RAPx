use super::{MopFnAliasMap, graph::*};
use crate::def_id::*;
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{Operand, ProjectionElem, TerminatorKind},
    ty::{self, TyCtxt, TypingEnv},
};
use std::collections::HashSet;

impl<'tcx> AliasGraph<'tcx> {
    /// Resolve a MIR place to its value index, creating field nodes lazily if needed.
    pub fn projection(&mut self, place: rustc_middle::mir::Place<'tcx>) -> usize {
        let local = place.local.as_usize();
        let mut value_idx = local;
        for proj in place.projection {
            match proj {
                ProjectionElem::Deref => {}
                ProjectionElem::Field(field, ty) => {
                    let field_idx = field.as_usize();
                    if !self.values[value_idx].fields.contains_key(&field_idx) {
                        if self.values.len()
                            < crate::analysis::points_to::graph::MAX_VALUES_PER_PATH
                        {
                            let ty_env = TypingEnv::post_analysis(self.tcx(), self.def_id());
                            let need_drop = ty.needs_drop(self.tcx(), ty_env);
                            let may_drop = !super::types::is_not_drop(self.tcx(), ty);
                            let mut node = super::value::Value::new(self.values.len(), local);
                            node.father = Some(super::value::FatherInfo::new(value_idx, field_idx));
                            let node_index = node.index;
                            self.values[value_idx].fields.insert(field_idx, node.index);
                            self.values.push(node);
                            let field_slot = crate::analysis::points_to::slot::Slot {
                                local,
                                fields: self.get_field_seq(node_index).into_iter().rev().collect(),
                            };
                            self.values[node_index].slot_idx =
                                Some(self.pts_graph.ensure_slot(field_slot, may_drop, need_drop));
                            self.pts_graph.set_slot_kind(
                                self.values[node_index].slot_idx.unwrap(),
                                super::types::kind(ty),
                            );
                        } else {
                            break;
                        }
                    }
                    value_idx = *self.values[value_idx].fields.get(&field_idx).unwrap();
                }
                _ => {}
            }
        }
        value_idx
    }

    pub fn call_target_of(&self, bb_index: usize) -> Option<DefId> {
        let term = self.terminator(bb_index)?;
        match &term.kind {
            TerminatorKind::Call {
                func: Operand::Constant(c),
                ..
            } => match c.ty().kind() {
                ty::FnDef(id, _) => Some(*id),
                _ => None,
            },
            _ => None,
        }
    }

    pub fn get_field_seq(&self, value_idx: usize) -> Vec<usize> {
        let mut seq = vec![];
        let mut cur = value_idx;
        let mut iter = 0usize;
        while let Some(ref father) = self.values[cur].father {
            iter += 1;
            if iter > 1000 {
                break;
            }
            seq.push(father.field_id);
            cur = father.father_value_id;
        }
        seq
    }
}

pub fn is_no_alias_intrinsic(def_id: DefId) -> bool {
    let v = [call_mut_opt(), clone_opt(), take_opt(), replace_opt()];
    contains(&v, def_id)
}

pub fn ensure_fn_aliases_cached<'tcx>(
    tcx: TyCtxt<'tcx>,
    target_id: DefId,
    fn_map: &mut MopFnAliasMap,
    recursion_set: &mut HashSet<DefId>,
) {
    if fn_map.contains_key(&target_id) || recursion_set.contains(&target_id) {
        return;
    }
    if !tcx.is_mir_available(target_id) {
        return;
    }
    recursion_set.insert(target_id);
    let mut alias_graph = AliasGraph::new(tcx, target_id);
    alias_graph.path_graph.find_scc();
    alias_graph.process_function_paths(fn_map, recursion_set);
    let ret_alias = alias_graph.ret_alias.clone();
    rap_debug!("Find aliases of {:?}: {:?}", target_id, ret_alias);
    fn_map.insert(target_id, ret_alias);
    recursion_set.remove(&target_id);
}
