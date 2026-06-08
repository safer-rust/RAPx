use std::collections::HashSet;

use crate::{
    analysis::{
        core::dataflow::*,
        utils::def_path::DefPath,
    },
    check::opt::OptCheck,
    utils::log::{relative_pos_range, span_to_filename, span_to_line_number, span_to_source_code},
};
use once_cell::sync::OnceCell;
use rustc_middle::{mir::Local, ty::TyCtxt};

use annotate_snippets::{Level, Renderer, Snippet};
use rustc_span::Span;

static DEFPATHS: OnceCell<DefPaths> = OnceCell::new();

use super::super::super::LEVEL;
use rustc_hir::{Expr, ExprKind, intravisit};
use rustc_middle::ty::TypeckResults;

struct DefPaths {
    vec_new: DefPath,
    vec_push: DefPath,
    vec_with_capacity: DefPath,
    vec_reserve: DefPath,
}

impl DefPaths {
    pub fn new(tcx: &TyCtxt<'_>) -> Self {
        Self {
            vec_new: DefPath::new("std::vec::Vec::new", tcx),
            vec_push: DefPath::new("std::vec::Vec::push", tcx),
            vec_with_capacity: DefPath::new("std::vec::Vec::with_capacity", tcx),
            vec_reserve: DefPath::new("std::vec::Vec::reserve", tcx),
        }
    }
}

pub struct LoopFinder<'tcx> {
    pub typeck_results: &'tcx TypeckResults<'tcx>,
    pub record: Vec<(Span, Vec<Span>)>,
}

pub struct PushFinder<'tcx> {
    typeck_results: &'tcx TypeckResults<'tcx>,
    record: Vec<Span>,
}

impl<'tcx> intravisit::Visitor<'tcx> for PushFinder<'tcx> {
    fn visit_expr(&mut self, ex: &'tcx Expr<'tcx>) {
        if let ExprKind::MethodCall(.., span) = ex.kind {
            let def_id = self
                .typeck_results
                .type_dependent_def_id(ex.hir_id)
                .unwrap();
            let target_def_id = (&DEFPATHS.get().unwrap()).vec_push.last_def_id();
            if def_id == target_def_id {
                self.record.push(span);
            }
        }
        intravisit::walk_expr(self, ex);
    }
}

impl<'tcx> intravisit::Visitor<'tcx> for LoopFinder<'tcx> {
    fn visit_expr(&mut self, ex: &'tcx Expr<'tcx>) {
        if let ExprKind::Loop(block, ..) = ex.kind {
            let mut push_finder = PushFinder {
                typeck_results: self.typeck_results,
                record: Vec::new(),
            };
            intravisit::walk_block(&mut push_finder, block);
            // if !push_finder.record.is_empty() {
            //     self.record.push((ex.span, push_finder.record));
            // }
            if push_finder.record.len() == 1 {
                // we only use simple cases
                self.record.push((ex.span, push_finder.record));
            }
        }
        intravisit::walk_expr(self, ex);
    }
}

pub struct UnreservedVecCheck {
    record: Vec<Span>,
}

fn is_vec_new_node(node: &GraphNode) -> bool {
    for op in node.ops.iter() {
        if let NodeOp::Call(def_id) = op {
            let def_paths = &DEFPATHS.get().unwrap();
            if *def_id == def_paths.vec_new.last_def_id() {
                return true;
            }
        }
    }
    false
}

fn is_vec_push_node(node: &GraphNode) -> bool {
    for op in node.ops.iter() {
        if let NodeOp::Call(def_id) = op {
            let def_paths = &DEFPATHS.get().unwrap();
            if *def_id == def_paths.vec_push.last_def_id() {
                return true;
            }
        }
    }
    false
}

fn find_upside_reservation(graph: &Graph, node_idx: Local) -> Option<Local> {
    let mut reservation_node_idx = None;
    let def_paths = &DEFPATHS.get().unwrap();
    let mut node_operator = |graph: &Graph, idx: Local| -> DFSStatus {
        let node = &graph.nodes[idx];
        for op in node.ops.iter() {
            if let NodeOp::Call(def_id) = op {
                if *def_id == def_paths.vec_with_capacity.last_def_id()
                    || *def_id == def_paths.vec_reserve.last_def_id()
                {
                    reservation_node_idx = Some(idx);
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
    reservation_node_idx
}

impl OptCheck for UnreservedVecCheck {
    fn new() -> Self {
        Self { record: Vec::new() }
    }

    fn check(&mut self, graph: &Graph, tcx: &TyCtxt) {
        let _ = &DEFPATHS.get_or_init(|| DefPaths::new(tcx));
        let level = LEVEL.lock().unwrap();
        if *level == 2 {
            for (node_idx, node) in graph.nodes.iter_enumerated() {
                if is_vec_new_node(node) {
                    self.record.push(node.span);
                }
                if is_vec_push_node(node) {
                    if let None = find_upside_reservation(graph, node_idx) {
                        self.record.push(node.span);
                    }
                }
            }
        }

        let def_id = graph.def_id;
        let body = tcx.hir_body_owned_by(def_id.as_local().unwrap());
        let typeck_results = tcx.typeck(def_id.as_local().unwrap());
        let mut loop_finder = LoopFinder {
            typeck_results,
            record: Vec::new(),
        };
        intravisit::walk_body(&mut loop_finder, body);
        for (_, push_record) in loop_finder.record {
            for push_span in push_record {
                if let Some((node_idx, _)) = graph.query_node_by_span(push_span, false) {
                    if let None = find_upside_reservation(graph, node_idx) {
                        self.record.push(push_span);
                    }
                }
            }
        }
    }

    fn report(&self, graph: &Graph) {
        for span in self.record.iter() {
            report_unreserved_vec_bug(graph, *span);
        }
    }

    fn cnt(&self) -> usize {
        self.record.len()
    }
}

fn report_unreserved_vec_bug(graph: &Graph, span: Span) {
    let code_source = span_to_source_code(graph.span);
    let filename = span_to_filename(span);
    let snippet: Snippet<'_> = Snippet::source(&code_source)
        .line_start(span_to_line_number(graph.span))
        .origin(&filename)
        .fold(true)
        .annotation(
            Level::Error
                .span(relative_pos_range(graph.span, span))
                .label("Space unreserved."),
        );
    let message = Level::Warning
        .title("Improper data collection detected")
        .snippet(snippet)
        .footer(Level::Help.title("Reserve enough space."));
    let renderer = Renderer::styled();
    println!("{}", renderer.render(message));
}
