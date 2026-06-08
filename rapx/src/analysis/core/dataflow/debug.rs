use std::fmt::Write;

use rustc_middle::{mir::Local, ty::TyCtxt};

use crate::graphs::dataflow::*;

fn escaped_string(s: String) -> String {
    s.replace("{", "\\{")
        .replace("}", "\\}")
        .replace("<", "\\<")
        .replace(">", "\\>")
        .replace("\"", "\\\"")
}

impl DataflowEdge {
    pub fn to_dot_graph<'tcx>(&self) -> String {
        let mut attr = String::new();
        let mut dot = String::new();
        write!(
            attr,
            "label=\"{}\" ",
            escaped_string(format!("{}_{:?}", self.seq, self.op))
        )
        .unwrap();
        write!(dot, "{:?} -> {:?} [{}]", self.src, self.dst, attr).unwrap();
        dot
    }
}

impl DataflowNode {
    pub fn to_dot_graph<'tcx>(
        &self,
        tcx: &TyCtxt<'tcx>,
        local: Local,
        color: Option<String>,
        is_marker: bool,
    ) -> String {
        let mut attr = String::new();
        let mut dot = String::new();
        if is_marker {
            assert!(self.ops.len() == 1);
            match self.ops[0] {
                NodeOp::Nop => {
                    write!(attr, "label=\"{:?} ", local).unwrap();
                }
                NodeOp::Const(ref src_desc, ref src_ty) => {
                    write!(
                        attr,
                        "label=\"<f0> {:?} {} {} ",
                        local,
                        escaped_string(src_desc.clone()),
                        escaped_string(src_ty.clone()),
                    )
                    .unwrap();
                }
                NodeOp::Use => {
                    write!(attr, "label=\"{:?} ", local).unwrap();
                }
                NodeOp::Aggregate(_) => {
                    write!(attr, "label=\"{:?} ", local).unwrap();
                }
                _ => {
                    panic!("Wrong arm!  {:?} {:?}", local, self.ops[0]);
                }
            }
        } else {
            write!(attr, "label=\"<f0> {:?} ", local).unwrap();
        }
        let mut seq = 1;
        self.ops.iter().for_each(|op| {
            match op {
                NodeOp::Nop => {}
                NodeOp::Const(..) => {}
                NodeOp::Call(def_id) => {
                    let func_name = tcx.def_path_str(def_id);
                    write!(
                        attr,
                        "| <f{}> ({})fn {} ",
                        seq,
                        seq - 1,
                        escaped_string(func_name)
                    )
                    .unwrap();
                }
                NodeOp::Aggregate(agg_kind) => match agg_kind {
                    AggKind::Adt(def_id) => {
                        let agg_name = format!("{}::{{..}}", tcx.def_path_str(def_id));
                        write!(
                            attr,
                            "| <f{}> ({})Agg {} ",
                            seq,
                            seq - 1,
                            escaped_string(agg_name)
                        )
                        .unwrap();
                    }
                    AggKind::Closure(def_id) => {
                        let agg_name = tcx.def_path_str(def_id);
                        write!(
                            attr,
                            "| <f{}> ({})Clos {} ",
                            seq,
                            seq - 1,
                            escaped_string(agg_name)
                        )
                        .unwrap();
                    }
                    _ => {
                        write!(attr, "| <f{}> ({}){:?} ", seq, seq - 1, agg_kind).unwrap();
                    }
                },
                _ => {
                    write!(attr, "| <f{}> ({}){:?} ", seq, seq - 1, op).unwrap();
                }
            };
            seq += 1;
        });
        write!(attr, "\" ").unwrap();
        match color {
            None => {}
            Some(color) => {
                write!(attr, "color={} ", color).unwrap();
            }
        }
        if is_marker {
            write!(attr, "style=dashed ").unwrap();
        }
        write!(dot, "{:?} [{}]", local, attr).unwrap();
        dot
    }
}

impl DataflowGraph {
    pub fn to_dot_graph<'tcx>(&self, tcx: &TyCtxt<'tcx>) -> String {
        let mut dot = String::new();
        let name = tcx.def_path_str(self.def_id);

        writeln!(dot, "digraph \"{}\" {{", &name).unwrap();
        writeln!(dot, "    node [shape=record];").unwrap();
        for (local, node) in self.nodes.iter_enumerated() {
            let node_dot = if local <= Local::from_usize(self.argc) {
                node.to_dot_graph(tcx, local, Some(String::from("red")), false)
            } else if local < Local::from_usize(self.n_locals) {
                node.to_dot_graph(tcx, local, None, false)
            } else {
                node.to_dot_graph(tcx, local, None, true)
            };
            writeln!(dot, "    {}", node_dot).unwrap();
        }
        for edge in self.edges.iter() {
            let edge_dot = edge.to_dot_graph();
            writeln!(dot, "    {}", edge_dot).unwrap();
        }
        writeln!(dot, "}}").unwrap();
        dot
    }
}
