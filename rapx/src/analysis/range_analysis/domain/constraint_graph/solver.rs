
use crate::analysis::range_analysis::domain::domain::*;
use crate::analysis::range_analysis::Range;

use crate::analysis::range_analysis::domain::symbolic_expr::*;
use crate::compat::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::*;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::rc::Rc;

use super::ConstraintGraph;

impl<'tcx, T> ConstraintGraph<'tcx, T>
where
    T: IntervalArithmetic + ConstConvert + Debug,
{
    fn fix_intersects(&mut self, component: &HashSet<&'tcx Place<'tcx>>) {
        for &place in component.iter() {

            if let Some(sit) = self.symbmap.get_mut(place) {
                let node = self.vars.get(place).unwrap();

                for &op in sit.iter() {
                    let op = &mut self.oprs[op];
                    let sinknode = self.vars.get(op.get_sink()).unwrap();

                    op.op_fix_intersects(node, sinknode);
                }
            }
        }
    }

    fn step_range(
        &mut self,
        op: usize,
        cg_map: &FxHashMap<DefId, Rc<RefCell<ConstraintGraph<'tcx, T>>>>,
        vars_map: &mut FxHashMap<DefId, Vec<RefCell<VarNodes<'tcx, T>>>>,
        trace_op: &str,
        step_fn: impl FnOnce(&Range<T>, &Range<T>) -> Range<T>,
    ) -> bool {
        let op_kind = &self.oprs[op];
        let sink = op_kind.get_sink();
        let old_interval = self.vars.get(sink).unwrap().get_range().clone();
        let estimated_interval = op_kind.eval_interproc(&self.vars, cg_map, vars_map);
        let updated = step_fn(&old_interval, &estimated_interval);
        self.vars.get_mut(sink).unwrap().set_range(updated.clone());
        rap_trace!(
            "{} in {} set {:?}: E {:?} U {:?} {:?} -> {:?}",
            trace_op, op, sink, estimated_interval, updated, old_interval, updated
        );
        old_interval != updated
    }

    pub fn widen(
        &mut self,
        op: usize,
        cg_map: &FxHashMap<DefId, Rc<RefCell<ConstraintGraph<'tcx, T>>>>,
        vars_map: &mut FxHashMap<DefId, Vec<RefCell<VarNodes<'tcx, T>>>>,
    ) -> bool {
        self.step_range(op, cg_map, vars_map, "WIDEN", |old, est| old.widen(est))
    }

    pub fn narrow(
        &mut self,
        op: usize,
        cg_map: &FxHashMap<DefId, Rc<RefCell<ConstraintGraph<'tcx, T>>>>,
        vars_map: &mut FxHashMap<DefId, Vec<RefCell<VarNodes<'tcx, T>>>>,
    ) -> bool {
        self.step_range(op, cg_map, vars_map, "NARROW", |old, est| old.narrow(est))
    }

    fn run_worklist(
        &mut self,
        comp_use_map: &HashMap<&'tcx Place<'tcx>, HashSet<usize>>,
        entry_points: &HashSet<&'tcx Place<'tcx>>,
        cg_map: &FxHashMap<DefId, Rc<RefCell<ConstraintGraph<'tcx, T>>>>,
        vars_map: &mut FxHashMap<DefId, Vec<RefCell<VarNodes<'tcx, T>>>>,
        trace_char: &str,
        step_fn: impl Fn(&mut Self, usize, &FxHashMap<DefId, Rc<RefCell<ConstraintGraph<'tcx, T>>>>, &mut FxHashMap<DefId, Vec<RefCell<VarNodes<'tcx, T>>>>) -> bool,
        iter_limit: usize,
    ) {
        let mut worklist: Vec<&'tcx Place<'tcx>> = entry_points.iter().cloned().collect();
        let mut iteration = 0;
        while let Some(place) = worklist.pop() {
            iteration += 1;
            if iter_limit > 0 && iteration > iter_limit {
                rap_trace!("Iteration limit reached, breaking out of {}\n", trace_char);
                break;
            }
            if let Some(op_set) = comp_use_map.get(place) {
                for &op in op_set {
                    if step_fn(self, op, cg_map, vars_map) {
                        let sink = self.oprs[op].get_sink();
                        rap_trace!("{} {:?}\n", trace_char, sink);
                        worklist.push(sink);
                    }
                }
            }
        }
        rap_trace!("{} finished after {} iterations\n", trace_char, iteration);
    }

    fn pre_update(
        &mut self,
        comp_use_map: &HashMap<&'tcx Place<'tcx>, HashSet<usize>>,
        entry_points: &HashSet<&'tcx Place<'tcx>>,
        cg_map: &FxHashMap<DefId, Rc<RefCell<ConstraintGraph<'tcx, T>>>>,
        vars_map: &mut FxHashMap<DefId, Vec<RefCell<VarNodes<'tcx, T>>>>,
    ) {
        self.run_worklist(comp_use_map, entry_points, cg_map, vars_map, "W",
            |this, op, cg, vm| this.widen(op, cg, vm), 0)
    }

    fn pos_update(
        &mut self,
        comp_use_map: &HashMap<&'tcx Place<'tcx>, HashSet<usize>>,
        entry_points: &HashSet<&'tcx Place<'tcx>>,
        cg_map: &FxHashMap<DefId, Rc<RefCell<ConstraintGraph<'tcx, T>>>>,
        vars_map: &mut FxHashMap<DefId, Vec<RefCell<VarNodes<'tcx, T>>>>,
    ) {
        self.run_worklist(comp_use_map, entry_points, cg_map, vars_map, "N",
            |this, op, cg, vm| this.narrow(op, cg, vm), 1000)
    }

    fn generate_entry_points(
        &mut self,
        component: &HashSet<&'tcx Place<'tcx>>,
        entry_points: &mut HashSet<&'tcx Place<'tcx>>,
        cg_map: &FxHashMap<DefId, Rc<RefCell<ConstraintGraph<'tcx, T>>>>,
        vars_map: &mut FxHashMap<DefId, Vec<RefCell<VarNodes<'tcx, T>>>>,
    ) {
        for &place in component {
            let op = self.defmap.get(place).unwrap();
            if let BasicOpKind::Essa(essaop) = &mut self.oprs[*op] {
                if essaop.is_unresolved() {
                    let source = essaop.get_source();
                    let new_range = essaop.eval(&self.vars);
                    let sink_node = self.vars.get_mut(source).unwrap();
                    sink_node.set_range(new_range);
                }
                essaop.mark_resolved();
            }
            if !self.vars[place].get_range().is_unknown() {
                entry_points.insert(place);
            }
        }
    }

    fn propagate_to_next_scc(
        &mut self,
        component: &HashSet<&'tcx Place<'tcx>>,
        cg_map: &FxHashMap<DefId, Rc<RefCell<ConstraintGraph<'tcx, T>>>>,
        vars_map: &mut FxHashMap<DefId, Vec<RefCell<VarNodes<'tcx, T>>>>,
    ) {
        for &place in component.iter() {
            let node = self.vars.get_mut(place).unwrap();
            for &op in self.usemap.get(place).unwrap().iter() {
                let op_kind = &mut self.oprs[op];
                let sink = op_kind.get_sink();
                if !component.contains(sink) {
                    let new_range = op_kind.eval_interproc(&self.vars, cg_map, vars_map);
                    let sink_node = self.vars.get_mut(sink).unwrap();
                    rap_trace!(
                        "prop component {:?} set {:?} to {:?} through {:?}\n",
                        component,
                        new_range,
                        sink,
                        op_kind.get_instruction()
                    );
                    sink_node.set_range(new_range);

                    if let BasicOpKind::Essa(essaop) = op_kind {
                        if essaop.get_intersect().get_range().is_unknown() {
                            essaop.mark_unresolved();
                        }
                    }
                }
            }
        }
    }

    pub fn solve_const_func_call(
        &mut self,
        cg_map: &FxHashMap<DefId, Rc<RefCell<ConstraintGraph<'tcx, T>>>>,
        vars_map: &mut FxHashMap<DefId, Vec<RefCell<VarNodes<'tcx, T>>>>,
    ) {
        for (&sink, op) in &self.const_func_place {
            rap_trace!(
                "solve_const_func_call for sink {:?} with opset {:?}\n",
                sink,
                op
            );
            if let BasicOpKind::Call(_) = &self.oprs[*op] {
                let new_range = self.oprs[*op].eval_interproc(&self.vars, cg_map, vars_map);
                rap_trace!("Setting range for {:?} to {:?}\n", sink, new_range);
                self.vars.get_mut(sink).unwrap().set_range(new_range);
            }
        }
    }

    pub fn store_vars(&mut self, varnodes_vec: &mut Vec<RefCell<VarNodes<'tcx, T>>>) {
        rap_trace!("Storing vars\n");
        let old_vars = self.vars.clone();
        varnodes_vec.push(RefCell::new(old_vars));
    }

    pub fn reset_vars(&mut self, varnodes_vec: &mut Vec<RefCell<VarNodes<'tcx, T>>>) {
        rap_trace!("Resetting vars\n");
        self.vars = varnodes_vec[0].borrow_mut().clone();
    }

    pub fn find_intervals(
        &mut self,
        cg_map: &FxHashMap<DefId, Rc<RefCell<ConstraintGraph<'tcx, T>>>>,
        vars_map: &mut FxHashMap<DefId, Vec<RefCell<VarNodes<'tcx, T>>>>,
    ) {



        self.solve_const_func_call(cg_map, vars_map);
        self.numSCCs = self.worklist.len();
        let mut seen = HashSet::new();
        let mut components = Vec::new();

        for &place in self.worklist.iter().rev() {
            if seen.contains(place) {
                continue;
            }

            if let Some(component) = self.components.get(place) {
                for &p in component {
                    seen.insert(p);
                }

                components.push(component.clone());
            }
        }
        rap_trace!("TOLO:{:?}\n", components);

        for component in components {
            rap_trace!("===start component {:?}===\n", component);
            if component.len() == 1 {
                self.numAloneSCCs += 1;

                self.fix_intersects(&component);

                let variable: &Place<'tcx> = *component.iter().next().unwrap();
                let varnode = self.vars.get_mut(variable).unwrap();
                if varnode.get_range().is_unknown() {
                    varnode.set_default();
                }
            } else {

                let comp_use_map = self.build_use_map(&component);

                let mut entry_points = HashSet::new();


                self.generate_entry_points(&component, &mut entry_points, cg_map, vars_map);
                rap_trace!("entry_points {:?}  \n", entry_points);

                self.pre_update(&comp_use_map, &entry_points, cg_map, vars_map);
                self.fix_intersects(&component);
                self.pos_update(&comp_use_map, &entry_points, cg_map, vars_map);
            }
            self.propagate_to_next_scc(&component, cg_map, vars_map);
        }
        self.merge_return_places();
        let Some(varnodes_vec) = vars_map.get_mut(&self.self_def_id) else {
            rap_trace!(
                "No variable map entry for this function {:?}, skipping Nuutila\n",
                self.self_def_id
            );
            return;
        };
        self.store_vars(varnodes_vec);
    }

    pub fn merge_return_places(&mut self) {
        rap_trace!("====Merging return places====\n");
        for &place in self.rerurn_places.iter() {
            rap_debug!("merging return place {:?}\n", place);
            let mut merged_range = Range::bottom();
            if let Some(opset) = self.vars.get(place) {
                merged_range = merged_range.unionwith(opset.get_range());
            }
            if let Some(return_node) = self.vars.get_mut(&Place::return_place()) {
                rap_debug!("Assigning final merged range {:?} to _0", merged_range);
                return_node.set_range(merged_range);
            } else {
                // This case is unlikely for functions that return a value, as `_0`
                // should have been created during the initial graph build.
                // We add a trace message for robustness.
                rap_trace!(
                    "Warning: RETURN_PLACE (_0) not found in self.vars. Cannot assign merged return range."
                );
            }
        }
    }

    pub fn add_control_dependence_edges(&mut self) {
        rap_trace!("====Add control dependence edges====\n");
        self.print_symbmap();
        for (&place, opset) in self.symbmap.iter() {
            for &op in opset.iter() {
                let bop_index = self.oprs.len();
                let opkind = &self.oprs[op];
                let control_edge = ControlDep::new(
                    IntervalType::Basic(BasicInterval::default()),
                    opkind.get_sink(),
                    opkind.get_instruction().unwrap(),
                    place,
                );
                rap_trace!(
                    "Adding control_edge {:?} for place {:?} at index {}\n",
                    control_edge,
                    place,
                    bop_index
                );
                self.oprs.push(BasicOpKind::ControlDep(control_edge));
                self.usemap.entry(place).or_default().insert(bop_index);
            }
        }
    }

    pub fn del_control_dependence_edges(&mut self) {
        rap_trace!("====Delete control dependence edges====\n");

        let mut remove_from = self.oprs.len();
        while remove_from > 0 {
            match &self.oprs[remove_from - 1] {
                BasicOpKind::ControlDep(dep) => {
                    let place = dep.source;
                    rap_trace!(
                        "removing control_edge at idx {}: {:?}\n",
                        remove_from - 1,
                        dep
                    );
                    if let Some(set) = self.usemap.get_mut(&place) {
                        set.remove(&(remove_from - 1));
                        if set.is_empty() {
                            self.usemap.remove(&place);
                        }
                    }
                    remove_from -= 1;
                }
                _ => break,
            }
        }

        self.oprs.truncate(remove_from);
    }

    pub fn build_nuutila(&mut self, single: bool) {
        rap_trace!("====Building Nuutila====\n");
        self.build_symbolic_intersect_map();

        if single {
        } else {
            for place in self.vars.keys().copied() {
                self.dfs.insert(place, -1);
            }

            self.add_control_dependence_edges();

            let places: Vec<_> = self.vars.keys().copied().collect();
            rap_trace!("places{:?}\n", places);
            for place in places {
                if self.dfs[&place] < 0 {
                    rap_trace!("start place{:?}\n", place);
                    let mut stack = Vec::new();
                    self.visit(place, &mut stack);
                }
            }

            self.del_control_dependence_edges();
        }
        rap_trace!("components{:?}\n", self.components);
        rap_trace!("worklist{:?}\n", self.worklist);
        rap_trace!("dfs{:?}\n", self.dfs);
    }

    pub fn visit(&mut self, place: &'tcx Place<'tcx>, stack: &mut Vec<&'tcx Place<'tcx>>) {
        self.dfs.entry(place).and_modify(|v| *v = self.index);
        self.index += 1;
        self.root.insert(place, place);
        let uses = self.usemap.get(place).unwrap().clone();
        for op in uses {
            let name = self.oprs[op].get_sink();
            rap_trace!("place {:?} get name{:?}\n", place, name);
            if self.dfs.get(name).copied().unwrap_or(-1) < 0 {
                self.visit(name, stack);
            }

            if !self.in_component.contains(name)
                && self.dfs[self.root[place]] >= self.dfs[self.root[name]]
            {
                *self.root.get_mut(place).unwrap() = self.root.get(name).copied().unwrap();



            }
        }

        if self.root.get(place).copied().unwrap() == place {
            self.worklist.push_back(place);

            let mut scc = HashSet::new();
            scc.insert(place);

            self.in_component.insert(place);

            while let Some(top) = stack.last() {
                if self.dfs.get(top).copied().unwrap_or(-1) > self.dfs.get(place).copied().unwrap()
                {
                    let node = stack.pop().unwrap();
                    self.in_component.insert(node);

                    scc.insert(node);
                } else {
                    break;
                }
            }

            self.components.insert(place, scc);
        } else {
            stack.push(place);
        }
    }
}
