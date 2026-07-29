use crate::analysis::range_analysis::domain::ConstraintGraph;
use crate::analysis::range_analysis::domain::domain::CallOp;
use crate::analysis::range_analysis::domain::domain::{ConstConvert, IntervalArithmetic, VarNodes};
use crate::analysis::range_analysis::{Range, RangeType};
use crate::compat::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::Operand;
use rustc_middle::mir::Place;
use std::cell::RefCell;
use std::fmt::Debug;
use std::rc::Rc;

impl<'tcx, T: IntervalArithmetic + ConstConvert + Debug> CallOp<'tcx, T> {
    pub fn eval_call(
        &self,
        caller_vars: &VarNodes<'tcx, T>,
        cg_map: &FxHashMap<DefId, Rc<RefCell<ConstraintGraph<'tcx, T>>>>,
        vars_map: &mut FxHashMap<DefId, Vec<RefCell<VarNodes<'tcx, T>>>>,
    ) -> Range<T> {
        match self.fun_path.as_str() {
            "std::iter::IntoIterator::into_iter" => match self.args.first() {
                Some(Operand::Copy(place)) | Some(Operand::Move(place)) => {
                    rap_trace!(
                        "Iterator detected on place {:?}, returning its range",
                        place
                    );
                    if let Some(var_node) = caller_vars.get(place) {
                        let range = var_node.get_range().clone();
                        rap_trace!(
                            "Iterator detected on place {:?}, returning its range: {:?}",
                            place,
                            range
                        );
                        return range;
                    }
                }
                _ => {}
            },
            "std::iter::Iterator::next" => match self.args.first() {
                Some(Operand::Copy(place)) | Some(Operand::Move(place)) => {
                    rap_trace!(
                        "Iterator next detected on place {:?}, returning its range",
                        place
                    );
                    if let Some(var_node) = caller_vars.get(place) {
                        let range = var_node.get_range().clone();
                        rap_trace!(
                            "Iterator next detected on place {:?}, returning its range: {:?}",
                            place,
                            range
                        );
                        return range;
                    }
                }
                _ => {}
            },
            "core::slice::<impl [T]>::len" => {
                let mut result = Range::bottom();
                match self.args.last() {
                    Some(Operand::Copy(place)) | Some(Operand::Move(place)) => {
                        let range = caller_vars[place].get_range().clone();
                        let len = range.get_upper().clone() - range.get_lower().clone();
                        result = Range::exact(len.clone());
                    }
                    Some(Operand::Constant(c)) => {}
                    None => {}
                    #[cfg(rapx_rustc_ge_196)]
                    _ => {}
                }
                rap_trace!(
                    "len() detected on place {:?}, returning its range: {:?}",
                    self.sink,
                    result
                );
                return result;
            }
            "std::ops::IndexMut::index_mut" => {
                let mut result = Range::bottom();

                match self.args.last() {
                    Some(Operand::Copy(place)) | Some(Operand::Move(place)) => {
                        result = caller_vars[place].get_range().clone();
                    }
                    Some(Operand::Constant(c)) => {}
                    None => {}
                    #[cfg(rapx_rustc_ge_196)]
                    _ => {}
                }

                rap_trace!(
                    "IndexMut detected on place {:?}, returning its range: {:?}",
                    self.sink,
                    result
                );
                return result;
            }
            "std::ops::Index::index" => {
                let mut result = Range::bottom();

                match self.args.last() {
                    Some(Operand::Copy(place)) | Some(Operand::Move(place)) => {
                        result = caller_vars[place].get_range().clone();
                    }
                    Some(Operand::Constant(c)) => {}
                    None => {}
                    #[cfg(rapx_rustc_ge_196)]
                    _ => {}
                }

                rap_trace!(
                    "Index detected on place {:?}, returning its range: {:?}",
                    self.sink,
                    result
                );
                return result;
            }
            "core::panicking::panic" | "std::panicking::panic" => {
                rap_trace!("Panic call detected, returning bottom range.");
                return Range::new(T::max_value(), T::min_value(), RangeType::Empty);
            }
            _ => {}
        }
        // 1. Find the callee's ConstraintGraph in the map.
        if let Some(rc_callee_cg_cell) = cg_map.get(&self.def_id) {
            rap_debug!(
                "Evaluating call to {:?} with args {:?}",
                self.def_id,
                self.args
            );
            // 2. Try to get a mutable borrow of the callee's graph.
            //    Using `try_borrow_mut` is safer than `borrow_mut` to avoid panicking on recursive calls.
            if let Ok(mut callee_cg) = rc_callee_cg_cell.try_borrow_mut() {
                // 3. Pass arguments from caller to callee.
                //    This assumes arguments are in order and `_1`, `_2`, ... in the callee MIR.
                for (i, caller_arg_operand) in self.args.iter().enumerate() {
                    rap_debug!(
                        "Processing argument {}: {:?} to callee {:?}",
                        i,
                        caller_arg_operand,
                        self.def_id
                    );
                    match caller_arg_operand {
                        Operand::Copy(caller_arg_place) | Operand::Move(caller_arg_place) => {
                            // Add the variable node for the caller's argument.
                            // Callee arguments are typically `_1`, `_2`, ...
                            let callee_arg_local = rustc_middle::mir::Local::from_usize(i + 1);

                            // Find the corresponding Place and VarNode in the callee.
                            if let Some(callee_arg_node) = callee_cg.vars.values_mut().find(|v| {
                                v.v.local == callee_arg_local && v.v.projection.is_empty()
                            }) {
                                // Get the range from the caller's variable and set it for the callee's argument.
                                if let Some(caller_arg_node) = caller_vars.get(&caller_arg_place) {
                                    let arg_range = caller_arg_node.get_range().clone();
                                    callee_arg_node.set_range(arg_range);
                                    rap_debug!(
                                        "Passing argument from {:?} to callee {:?} : {:?} {:?} -> {:?}",
                                        caller_arg_place,
                                        self.def_id,
                                        callee_arg_node.get_value(),
                                        caller_arg_node.get_range(),
                                        callee_arg_node.get_range()
                                    );
                                }
                            }
                        }
                        Operand::Constant(const_operand) => {
                            rap_debug!(
                                "constant argument {:?} to callee {:?}",
                                const_operand,
                                self.def_id
                            );
                            let callee_arg_local = rustc_middle::mir::Local::from_usize(i + 1);
                            if let Some(const_value) = T::from_const(&const_operand.const_) {
                                if let Some(callee_arg_node) =
                                    callee_cg.vars.values_mut().find(|v| {
                                        v.v.local == callee_arg_local && v.v.projection.is_empty()
                                    })
                                {
                                    // Get the range from the caller's variable and set it for the callee's argument.

                                    let arg_range = Range::new(
                                        const_value.clone(),
                                        const_value.clone(),
                                        RangeType::Regular,
                                    );
                                    callee_arg_node.set_range(arg_range.clone());
                                    rap_debug!(
                                        "Passing argument from {:?} to callee {:?} : {:?} {:?} -> {:?}",
                                        const_value,
                                        self.def_id,
                                        callee_arg_node.get_value(),
                                        arg_range,
                                        callee_arg_node.get_range()
                                    );
                                }
                            }
                            // Find the corresponding Place and VarNode in the callee.
                        }
                        #[cfg(rapx_rustc_ge_196)]
                        Operand::RuntimeChecks(_) => {}
                    }
                }

                // 4. Run analysis on the callee.
                //    NOTE: This is a simplification. A full implementation would use memoization
                //    or a bottom-up analysis order to avoid re-analyzing functions repeatedly.
                //    For now, we re-run it to ensure argument values are propagated.
                callee_cg.find_intervals(cg_map, vars_map);

                // 5. Retrieve the return value.
                //    The return value is stored in `_0` (RETURN_PLACE).
                let return_place_local = 0 as usize; // `_0` is typically the first local.

                // Find all variables that contribute to the return value.
                // The `rerurn_places` set in the callee's graph tracks these.
                if let Some(return_node) = callee_cg.vars.get_mut(&Place::return_place()) {
                    let return_range = return_node.get_range().clone();
                    rap_debug!(" final return range {:?} ", return_range);
                    return return_range;
                }
                let Some(callee_varnodes_vec) = vars_map.get_mut(&self.def_id) else {
                    panic!(
                        "No variable map entry for this function {:?}, skipping Nuutila\n",
                        self.def_id
                    );
                };
                callee_cg.reset_vars(callee_varnodes_vec);
            } else {
                // Recursive call detected or graph is already borrowed.
                // Conservatively return a full range.
                rap_trace!(
                    "Recursive call or existing borrow for {:?}, returning top.",
                    self.def_id
                );
                return Range::top();
            }
        }

        // Callee not found (e.g., external library function, function pointer).
        // Return a conservative full range.
        rap_trace!(
            "Callee ConstraintGraph for {:?} not found, returning top.",
            self.def_id
        );
        Range::top()
}
}
