use std::collections::HashSet;

use once_cell::sync::OnceCell;

use rustc_ast::BinOpKind;
use rustc_hir::{Expr, ExprKind, intravisit};
use rustc_middle::{mir::Local, ty::TyCtxt};
use rustc_span::Span;

use crate::{
    analysis::{dataflow::*, utils::def_path::DefPath},
    utils::log::{relative_pos_range, span_to_filename, span_to_line_number, span_to_source_code},
};
use annotate_snippets::{Level, Renderer, Snippet};

use super::super::super::NO_STD;

static DEFPATHS: OnceCell<DefPaths> = OnceCell::new();

struct DefPaths {
    ops_range: DefPath,
    vec_len: DefPath,
    slice_len: DefPath,
    ops_index: DefPath,
    ops_index_mut: DefPath,
}

impl DefPaths {
    pub fn new(tcx: &TyCtxt<'_>) -> Self {
        let no_std = NO_STD.lock().unwrap();
        if *no_std {
            Self {
                ops_range: DefPath::new("core::ops::Range", tcx),
                vec_len: DefPath::new("alloc::vec::Vec::len", tcx),
                slice_len: DefPath::new("core::slice::len", tcx),
                ops_index: DefPath::new("core::ops::Index::index", tcx),
                ops_index_mut: DefPath::new("core::ops::IndexMut::index_mut", tcx),
            }
        } else {
            Self {
                ops_range: DefPath::new("std::ops::Range", tcx),
                vec_len: DefPath::new("std::vec::Vec::len", tcx),
                slice_len: DefPath::new("slice::len", tcx),
                ops_index: DefPath::new("std::ops::Index::index", tcx),
                ops_index_mut: DefPath::new("std::ops::IndexMut::index_mut", tcx),
            }
        }
    }
}

use crate::check::opt::OptCheck;

pub struct BoundsLenCheck {
    pub record: Vec<(Local, Vec<Local>)>,
}

struct IfFinder {
    record: Vec<(Span, Vec<Span>)>,
}
struct LtFinder {
    record: Vec<Span>,
}
struct IndexFinder {
    record: Vec<Span>,
}

impl intravisit::Visitor<'_> for LtFinder {
    fn visit_expr(&mut self, ex: &Expr) {
        if let ExprKind::Binary(op, ..) = ex.kind {
            if op.node == BinOpKind::Lt {
                self.record.push(ex.span);
            }
        }
        intravisit::walk_expr(self, ex);
    }
}

impl<'tcx> intravisit::Visitor<'tcx> for IfFinder {
    fn visit_expr(&mut self, ex: &'tcx Expr<'tcx>) {
        if let ExprKind::If(cond, e1, _) = ex.kind {
            let mut lt_finder = LtFinder { record: vec![] };
            intravisit::walk_expr(&mut lt_finder, cond);
            if !lt_finder.record.is_empty() {
                let mut index_finder = IndexFinder { record: vec![] };
                intravisit::walk_expr(&mut index_finder, e1);
                if !index_finder.record.is_empty() {
                    self.record.push((lt_finder.record[0], index_finder.record));
                }
            }
        }
        intravisit::walk_expr(self, ex);
    }
}

impl<'tcx> intravisit::Visitor<'tcx> for IndexFinder {
    fn visit_expr(&mut self, ex: &'tcx Expr<'tcx>) {
        if let ExprKind::Index(_, ex2, _) = ex.kind {
            self.record.push(ex2.span);
        }
        intravisit::walk_expr(self, ex);
    }
}

impl OptCheck for BoundsLenCheck {
    fn new() -> Self {
        Self { record: vec![] }
    }

    fn check(&mut self, graph: &Graph, tcx: &TyCtxt) {
        let _ = &DEFPATHS.get_or_init(|| DefPaths::new(tcx));
        for (node_idx, node) in graph.nodes.iter_enumerated() {
            if let Some(upperbound_node_idx) = extract_upperbound_node_if_ops_range(graph, node) {
                if let Some(vec_len_node_idx) = find_upside_len_node(graph, upperbound_node_idx) {
                    let maybe_vec_node_idx = graph.get_upside_idx(vec_len_node_idx, 0).unwrap();
                    let maybe_vec_node_idxs =
                        graph.collect_equivalent_locals(maybe_vec_node_idx, true);
                    let mut index_record = vec![];
                    for index_node_idx in find_downside_index_node(graph, node_idx).into_iter() {
                        let maybe_vec_node_idx = graph.get_upside_idx(index_node_idx, 0).unwrap();
                        if maybe_vec_node_idxs.contains(&maybe_vec_node_idx) {
                            index_record.push(index_node_idx);
                        }
                    }
                    if !index_record.is_empty() {
                        self.record.push((upperbound_node_idx, index_record));
                    }
                }
            }
        }
        let def_id = graph.def_id;
        let body = tcx.hir_body_owned_by(def_id.as_local().unwrap());
        let mut if_finder = IfFinder { record: vec![] };
        intravisit::walk_body(&mut if_finder, body);
        for (cond, slice_index_record) in if_finder.record.iter() {
            if let Some((node_idx, node)) = graph.query_node_by_span(*cond, true) {
                let left_arm = graph.edges[node.in_edges[0]].src;
                let right_arm = graph.edges[node.in_edges[1]].src;
                if find_upside_len_node(graph, right_arm).is_some() {
                    let index_set = graph.collect_ancestor_locals(left_arm, true);
                    let len_set = graph.collect_ancestor_locals(right_arm, true);
                    let mut slice_node_indice = vec![];
                    for slice_index_idx in slice_index_record {
                        if let Some((index_node_idx, _)) =
                            graph.query_node_by_span(*slice_index_idx, true)
                        {
                            let index_ancestors =
                                graph.collect_ancestor_locals(index_node_idx, true);
                            let indexed_node_idx =
                                find_indexed_node_from_index(graph, index_node_idx);
                            if let Some(indexed_node_idx) = indexed_node_idx {
                                let indexed_ancestors =
                                    graph.collect_ancestor_locals(indexed_node_idx, true);
                                // Warning: We only checks index without checking the indexed value
                                if index_ancestors.intersection(&index_set).next().is_some()
                                    && indexed_ancestors.intersection(&len_set).next().is_some()
                                {
                                    slice_node_indice.push(index_node_idx);
                                }
                            }
                        }
                    }
                    self.record.push((node_idx, slice_node_indice));
                }
            }
        }
    }

    fn report(&self, graph: &Graph) {
        for (upperbound_node_idx, index_record) in self.record.iter() {
            report_upperbound_bug(graph, *upperbound_node_idx, index_record);
        }
    }

    fn cnt(&self) -> usize {
        self.record.iter().map(|(_, spans)| spans.len()).sum()
    }
}

fn find_indexed_node_from_index(graph: &Graph, index_node_idx: Local) -> Option<Local> {
    let def_paths = &DEFPATHS.get().unwrap();
    let index_node = &graph.nodes[index_node_idx];
    for edge_idx in index_node.out_edges.iter() {
        let dst_node_idx = graph.edges[*edge_idx].dst;
        let dst_node = &graph.nodes[dst_node_idx];
        for op in dst_node.ops.iter() {
            if let NodeOp::Call(def_id) = op {
                if *def_id == def_paths.ops_index.last_def_id()
                    || *def_id == def_paths.ops_index_mut.last_def_id()
                {
                    let index_operator_node =
                        &graph.nodes[graph.edges[index_node.out_edges[0]].dst];

                    return Some(graph.edges[index_operator_node.in_edges[0]].src);
                }
            }
            if graph.is_marker(dst_node_idx) {
                for edge_idx_ in dst_node.in_edges.iter() {
                    let edge = &graph.edges[*edge_idx_];
                    if let EdgeOp::Index = edge.op {
                        return Some(edge.src);
                    }
                }
            }
        }
    }
    None
}

fn extract_upperbound_node_if_ops_range(graph: &Graph, node: &GraphNode) -> Option<Local> {
    let def_paths = &DEFPATHS.get().unwrap();
    let target_def_id = def_paths.ops_range.last_def_id();
    for op in node.ops.iter() {
        if let NodeOp::Aggregate(AggKind::Adt(def_id)) = op {
            if *def_id == target_def_id {
                let upperbound_edge = &graph.edges[node.in_edges[1]]; // the second field
                return Some(upperbound_edge.src);
            }
        }
    }
    None
}

fn find_upside_len_node(graph: &Graph, node_idx: Local) -> Option<Local> {
    let mut len_node_idx = None;
    let def_paths = &DEFPATHS.get().unwrap();
    // Warning: may traverse all upside nodes and the new result will overwrite on the previous result
    let mut node_operator = |graph: &Graph, idx: Local| -> DFSStatus {
        let node = &graph.nodes[idx];
        for op in node.ops.iter() {
            if let NodeOp::Call(def_id) = op {
                if *def_id == def_paths.vec_len.last_def_id()
                    || *def_id == def_paths.slice_len.last_def_id()
                {
                    len_node_idx = Some(idx);
                    return DFSStatus::Stop;
                }
            }
        }
        DFSStatus::Continue
    };
    let mut seen = HashSet::new();
    graph.dfs(
        node_idx,
        Direction::Upside,
        &mut node_operator,
        &mut Graph::equivalent_edge_validator,
        false,
        &mut seen,
    );
    len_node_idx
}

fn find_downside_index_node(graph: &Graph, node_idx: Local) -> Vec<Local> {
    let mut index_node_idxs: Vec<Local> = vec![];
    let def_paths = &DEFPATHS.get().unwrap();
    // Warning: traverse all downside nodes
    let mut node_operator = |graph: &Graph, idx: Local| -> DFSStatus {
        let node = &graph.nodes[idx];
        for op in node.ops.iter() {
            if let NodeOp::Call(def_id) = op {
                if *def_id == def_paths.ops_index.last_def_id()
                    || *def_id == def_paths.ops_index_mut.last_def_id()
                {
                    index_node_idxs.push(idx);
                    break;
                }
            }
        }
        DFSStatus::Continue
    };
    let mut seen = HashSet::new();
    graph.dfs(
        node_idx,
        Direction::Downside,
        &mut node_operator,
        &mut Graph::always_true_edge_validator,
        true,
        &mut seen,
    );
    index_node_idxs
}

fn report_upperbound_bug(graph: &Graph, upperbound_node_idx: Local, index_record: &Vec<Local>) {
    let upperbound_span = graph.nodes[upperbound_node_idx].span;
    let code_source = span_to_source_code(graph.span);
    let filename = span_to_filename(upperbound_span);
    let mut snippet = Snippet::source(&code_source)
        .line_start(span_to_line_number(graph.span))
        .origin(&filename)
        .fold(true)
        .annotation(
            Level::Info
                .span(relative_pos_range(graph.span, upperbound_span))
                .label("Index is upperbounded."),
        );
    for node_idx in index_record {
        let index_span = graph.nodes[*node_idx].span;
        snippet = snippet.annotation(
            Level::Error
                .span(relative_pos_range(graph.span, index_span))
                .label("Checked here."),
        );
    }
    let message = Level::Warning
        .title("Unnecessary bounds checkings detected")
        .snippet(snippet)
        .footer(Level::Help.title("Use unsafe APIs instead."));
    let renderer = Renderer::styled();
    println!("{}", renderer.render(message));
}
