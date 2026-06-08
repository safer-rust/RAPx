use crate::{
    analysis::{
        core::dataflow::*,
        utils::def_path::DefPath,
    },
    check::opt::OptCheck,
    utils::log::{relative_pos_range, span_to_filename, span_to_line_number, span_to_source_code},
};
use annotate_snippets::{Level, Renderer, Snippet};
use once_cell::sync::OnceCell;
use rustc_ast::Mutability;

use super::super::LEVEL;
use rustc_middle::{
    mir::Local,
    ty::{TyCtxt, TyKind},
};
use rustc_span::Span;
use std::cell::Cell;
use std::collections::HashSet;

static DEFPATHS: OnceCell<DefPaths> = OnceCell::new();

struct DefPaths {
    clone: DefPath,
    //to_string: DefPath,
    to_owned: DefPath,
    deref: DefPath,
}

impl DefPaths {
    pub fn new(tcx: &TyCtxt<'_>) -> Self {
        Self {
            clone: DefPath::new("std::clone::Clone::clone", tcx),
            //to_string: DefPath::new("std::string::ToString::to_string", tcx),
            to_owned: DefPath::new("std::borrow::ToOwned::to_owned", tcx),
            deref: DefPath::new("std::ops::Deref::deref", tcx),
        }
    }
}

// whether the cloned value is used as a parameter
fn find_downside_use_as_param(graph: &Graph, clone_node_idx: Local) -> Option<(Local, EdgeIdx)> {
    let mut record = None;
    let edge_idx = Cell::new(0 as usize);
    let deref_id = DEFPATHS.get().unwrap().deref.last_def_id();
    let mut node_operator = |graph: &Graph, idx: Local| {
        if idx == clone_node_idx {
            return DFSStatus::Continue; //the start point, clone, is a Call node as well
        }
        let node = &graph.nodes[idx];
        for op in node.ops.iter() {
            if let NodeOp::Call(def_id) = op {
                if *def_id == deref_id {
                    //we permit deref here
                    return DFSStatus::Continue;
                }
                record = Some((idx, edge_idx.get())); //here, the edge_idx must be the upside edge of the node
                return DFSStatus::Stop;
            }
        }
        DFSStatus::Continue
    };
    let mut edge_operator = |graph: &Graph, idx: EdgeIdx| {
        edge_idx.set(idx);
        Graph::equivalent_edge_validator(graph, idx) //can not support ref->deref->ref link
    };
    let mut seen = HashSet::new();
    graph.dfs(
        clone_node_idx,
        Direction::Downside,
        &mut node_operator,
        &mut edge_operator,
        true,
        &mut seen,
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
                            let fn_sig = tcx.try_normalize_erasing_regions(
                                rustc_middle::ty::TypingEnv::post_analysis(*tcx, def_id),
                                tcx.fn_sig(callee_def_id).skip_binder(),
                            );
                            if fn_sig.is_ok() {
                                let fn_sig = fn_sig.unwrap().skip_binder();
                                let ty = fn_sig.inputs().iter().nth(index).unwrap();
                                if let TyKind::Ref(_, _, mutability) = ty.kind() {
                                    //not &mut T
                                    if *mutability == Mutability::Mut {
                                        break;
                                    }
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
    let code_source = span_to_source_code(graph.span);
    let filename = span_to_filename(clone_span);
    let snippet = Snippet::source(&code_source)
        .line_start(span_to_line_number(graph.span))
        .origin(&filename)
        .fold(true)
        .annotation(
            Level::Error
                .span(relative_pos_range(graph.span, clone_span))
                .label("Cloning happens here."),
        )
        .annotation(
            Level::Error
                .span(relative_pos_range(graph.span, use_span))
                .label("Used here"),
        );
    let message = Level::Warning
        .title("Unnecessary memory cloning detected")
        .snippet(snippet)
        .footer(Level::Help.title("Use borrowings instead."));
    let renderer = Renderer::styled();
    println!("{}", renderer.render(message));
}
