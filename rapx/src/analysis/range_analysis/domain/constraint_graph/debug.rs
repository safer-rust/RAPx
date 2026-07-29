
use super::ConstraintGraph;
use crate::analysis::range_analysis::domain::domain::BasicOpKind;
use crate::analysis::range_analysis::domain::domain::{ConstConvert, IntervalArithmetic};
use crate::analysis::range_analysis::domain::symbolic_expr::IntervalTypeTrait;
use rustc_middle::mir::Place;
use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Write};

impl<'tcx, T> ConstraintGraph<'tcx, T>
where
    T: IntervalArithmetic + ConstConvert + Debug,
{
    pub fn to_dot(&self) -> String {
        let mut dot = String::new();
        writeln!(&mut dot, "digraph ConstraintGraph {{").unwrap();
        writeln!(&mut dot, "    layout=neato;").unwrap();
        writeln!(&mut dot, "    overlap=false;").unwrap();
        writeln!(&mut dot, "    splines=true;").unwrap();
        writeln!(&mut dot, "    sep=\"+1.0\";").unwrap();
        writeln!(&mut dot, "    rankdir=TB;").unwrap();
        writeln!(&mut dot, "    ranksep=1.8;").unwrap();
        writeln!(&mut dot, "    nodesep=0.8;").unwrap();
        writeln!(&mut dot, "    edge [len=2.0];").unwrap();
        writeln!(&mut dot, "    node [fontname=\"Fira Code\"];").unwrap();
        writeln!(&mut dot, "\n    // Variable Nodes").unwrap();
        writeln!(&mut dot, "    subgraph cluster_vars {{").unwrap();
        writeln!(&mut dot, "        rank=same;").unwrap();
        for (place, _var_node) in &self.vars {
            let place_id = format!("{:?}", place);
            let label = format!("{:?}", place);
            writeln!(
                &mut dot,
                "        \"{}\" [label=\"{}\", shape=ellipse, style=filled, fillcolor=lightblue, width=1.2, fixedsize=false];",
                place_id, label
            ).unwrap();
        }
        writeln!(&mut dot, "    }}").unwrap();

        writeln!(&mut dot, "\n    // Operation Nodes").unwrap();
        writeln!(&mut dot, "    subgraph cluster_ops {{").unwrap();
        writeln!(&mut dot, "        rank=same;").unwrap();
        for (op_idx, op) in self.oprs.iter().enumerate() {
            let op_id = format!("op_{}", op_idx);
            let label = match op {
                BasicOpKind::Unary(o) => format!("Unary({:?})", o.op),
                BasicOpKind::Binary(o) => format!("Binary({:?})", o.op),
                BasicOpKind::Essa(_) => "Essa".to_string(),
                BasicOpKind::ControlDep(_) => "ControlDep".to_string(),
                BasicOpKind::Phi(_) => "Φ (Phi)".to_string(),
                BasicOpKind::Use(_) => "Use".to_string(),
                BasicOpKind::Call(c) => format!("Call({:?})", c.def_id),
                BasicOpKind::Ref(r) => format!("Ref({:?})", r.borrowkind),
                BasicOpKind::Aggregate(r) => format!("AggregateOp({:?})", r.unique_adt),
            };
            writeln!(
                &mut dot,
                "        \"{}\" [label=\"{}\", shape=box, style=filled, fillcolor=lightgrey, width=1.5, fixedsize=false];",
                op_id, label
            ).unwrap();
        }
        writeln!(&mut dot, "    }}").unwrap();

        writeln!(&mut dot, "\n    // Definition Edges (op -> var)").unwrap();
        for (place, op_idx) in &self.defmap {
            writeln!(&mut dot, "    \"op_{}\" -> \"{:?}\";", op_idx, place).unwrap();
        }

        writeln!(&mut dot, "\n    // Use Edges (var -> op)").unwrap();
        for (place, op_indices) in &self.usemap {
            for op_idx in op_indices {
                writeln!(&mut dot, "    \"{:?}\" -> \"op_{}\";", place, op_idx).unwrap();
            }
        }

        writeln!(&mut dot, "\n    // Symbolic Bound Edges (var -> op)").unwrap();
        for (place, op_indices) in &self.symbmap {
            for op_idx in op_indices {
                writeln!(
                    &mut dot,
                    "    \"{:?}\" -> \"op_{}\" [color=blue, style=dashed];",
                    place, op_idx
                ).unwrap();
            }
        }

        writeln!(&mut dot, "}}").unwrap();
        dot
    }

    pub fn print_vars(&self) {
        for (&key, value) in &self.vars {
            rap_trace!("Var: {:?}. {:?} ", key, value.get_range());
        }
    }

    pub(crate) fn print_symbmap(&self) {
        for (&key, value) in &self.symbmap {
            for op in value.iter() {
                if let Some(op) = self.oprs.get(*op) {
                    rap_trace!("symbmap op: {:?}. {:?}\n ", key, op);
                } else {
                    rap_trace!("symbmap op: {:?} not found\n ", op);
                }
            }
        }
    }

    pub(crate) fn print_defmap(&self) {
        for (key, value) in self.defmap.clone() {
            rap_trace!(
                "place: {:?} def in stmt:{:?} {:?}",
                key,
                self.oprs[value].get_type_name(),
                self.oprs[value].get_instruction()
            );
        }
    }

    pub(crate) fn print_compusemap(
        &self,
        component: &HashSet<&'tcx Place<'tcx>>,
        comp_use_map: &HashMap<&'tcx Place<'tcx>, HashSet<usize>>,
    ) {
        for (key, value) in comp_use_map.clone() {
            if component.contains(key) {
                for v in value {
                    rap_trace!(
                        "compusemap place: {:?} use in stmt:{:?} {:?}",
                        key,
                        self.oprs[v].get_type_name(),
                        self.oprs[v].get_instruction()
                    );
                }
            }
        }
    }

    pub(crate) fn print_usemap(&self) {
        for (key, value) in self.usemap.clone() {
            for v in value {
                rap_trace!(
                    "place: {:?} use in stmt:{:?} {:?}",
                    key,
                    self.oprs[v].get_type_name(),
                    self.oprs[v].get_instruction()
                );
            }
        }
    }

    pub(crate) fn print_symbexpr(&self) {
        let mut vars: Vec<_> = self.vars.iter().collect();

        vars.sort_by_key(|(local, _)| local.local.index());

        for (&local, value) in vars {
            rap_info!(
                "Var: {:?}. [ {:?} , {:?} ]",
                local,
                value.interval.get_lower_expr(),
                value.interval.get_upper_expr()
            );
        }
    }
}
