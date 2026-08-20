use crate::{
    analysis::dataflow::*,
    check::opt::OptCheck,
};
use annotate_snippets::Level;

use crate::check::opt::report::OptReport;

use super::super::LEVEL;
use rustc_middle::{
    mir::Local,
    ty::{Mutability, TyCtxt, TyKind},
};
use rustc_span::Span;
use std::cell::Cell;

crate::def_paths! {
    clone: "std::clone::Clone::clone",
    to_owned: "std::borrow::ToOwned::to_owned",
    deref: "std::ops::Deref::deref",
}


fn find_downside_use_as_param(graph: &Graph, clone_node_idx: Local) -> Option<(Local, EdgeIdx)> {
    let mut record = None;
    let captured_edge = Cell::new(0);
    let deref_id = DEFPATHS.get().unwrap().deref.last_def_id();
    let mut edge_operator = |graph: &Graph, idx: EdgeIdx| {
        captured_edge.set(idx);
        Graph::equivalent_edge_validator(graph, idx)
    };
    graph.find_first_node(
        clone_node_idx,
        Direction::Downside,
        &mut |graph: &Graph, idx: Local| {
            if idx == clone_node_idx {
                return false;
            }
            let node = &graph.nodes[idx];
            for op in node.ops.iter() {
                if let NodeOp::Call(def_id) = op {
                    if *def_id == deref_id {
                        return false;
                    }
                    record = Some((idx, captured_edge.get()));
                    return true;
                }
            }
            false
        },
        &mut edge_operator,
    );
    record
}

pub struct UsedAsImmutableCheck {
    record: Vec<(Span, Span)>,
}

impl OptCheck for UsedAsImmutableCheck {
    fn new() -> Self {
        Self { record: Vec::new() }
    }

    fn check(&mut self, graph: &Graph, tcx: &TyCtxt) {
        let _ = &DEFPATHS.get_or_init(|| DefPaths::new(tcx));
        let def_paths = &DEFPATHS.get().unwrap();
        let level = LEVEL.lock().unwrap();
        for (idx, node) in graph.nodes.iter_enumerated() {
            if node.ops.len() > 1 {
                //filter mutable variables
                continue;
            }
            if let NodeOp::Call(def_id) = node.ops[0] {
                if def_id == def_paths.clone.last_def_id()
                    // || *def_id == def_paths.to_string.last_def_id()
                    || def_id == def_paths.to_owned.last_def_id()
                {
                    if let Some((node_idx, edge_idx)) = find_downside_use_as_param(graph, idx) {
                        let use_node = &graph.nodes[node_idx];

                        let seq = graph.edges[edge_idx].seq;
                        let filtered_in_edges: Vec<&usize> = use_node
                            .in_edges
                            .iter()
                            .filter(|idx| graph.edges[**idx].seq == seq)
                            .collect();
                        let index = filtered_in_edges.binary_search(&&edge_idx).unwrap();
                        if let NodeOp::Call(callee_def_id) = use_node.ops[seq] {
                            let callee_fn_sig = tcx.fn_sig(callee_def_id).skip_binder();
                            #[cfg(not(rapx_ge_99))]
                            let fn_sig = tcx.try_normalize_erasing_regions(
                                rustc_middle::ty::TypingEnv::post_analysis(*tcx, def_id),
                                callee_fn_sig,
                            );
                            #[cfg(rapx_ge_99)]
                            let fn_sig = tcx.try_normalize_erasing_regions(
                                rustc_middle::ty::TypingEnv::post_analysis(*tcx, def_id),
                                rustc_type_ir::Unnormalized::dummy(callee_fn_sig),
                            );
                            if fn_sig.is_ok() {
                                let fn_sig = fn_sig.unwrap().skip_binder();
                                let ty = fn_sig.inputs().iter().nth(index).unwrap();
                                if let TyKind::Ref(_, _, Mutability::Mut) = ty.kind() {
                                    break;
                                }
                                let callee_func_name = format!("{:?}", callee_def_id);
                                if *level != 2
                                    && (callee_func_name.contains("into")
                                        || callee_func_name.contains("new"))
                                {
                                    //we filter out funcs that may cause false positive
                                    break;
                                }
                                let clone_span = node.span;
                                let use_span = use_node.span;
                                self.record.push((clone_span, use_span));
                            }
                        }
                    }
                }
            }
        }
    }

    fn report(&self, graph: &Graph) {
        for (clone_span, use_span) in self.record.iter() {
            report_used_as_immutable(graph, *clone_span, *use_span);
        }
    }

    fn cnt(&self) -> usize {
        self.record.len()
    }
}

fn report_used_as_immutable(graph: &Graph, clone_span: Span, use_span: Span) {
    OptReport::from_graph(graph)
        .file_name(clone_span)
        .title("Unnecessary memory cloning detected")
        .annotate(Level::Error, clone_span, "Cloning happens here.")
        .annotate(Level::Error, use_span, "Used here")
        .footer("Use borrowings instead.")
        .emit();
}
