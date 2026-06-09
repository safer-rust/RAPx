use crate::{
    analysis::{
        dataflow::*,
        utils::def_path::DefPath,
    },
    check::opt::OptCheck,
    utils::log::{relative_pos_range, span_to_filename, span_to_line_number, span_to_source_code},
};
use annotate_snippets::{Level, Renderer, Snippet};
use once_cell::sync::OnceCell;

use rustc_hir::{Expr, ExprKind, intravisit};
use rustc_middle::{
    mir::Local,
    ty::{TyCtxt, TypeckResults},
};
use rustc_span::Span;
use std::collections::HashSet;
static DEFPATHS: OnceCell<DefPaths> = OnceCell::new();

struct DefPaths {
    hashset_insert: DefPath,
    hashmap_insert: DefPath,
    hashset_new: DefPath,
    hashmap_new: DefPath,
    hashset_with: DefPath,
    hashmap_with: DefPath,
    clone: DefPath,
}

impl DefPaths {
    pub fn new(tcx: &TyCtxt<'_>) -> Self {
        Self {
            hashset_insert: DefPath::new("std::collections::HashSet::insert", tcx),
            hashmap_insert: DefPath::new("std::collections::HashMap::insert", tcx),
            hashset_new: DefPath::new("std::collections::HashSet::new", tcx),
            hashset_with: DefPath::new("std::collections::HashSet::with_capacity", tcx),
            hashmap_new: DefPath::new("std::collections::HashMap::new", tcx),
            hashmap_with: DefPath::new("std::collections::HashMap::with_capacity", tcx),
            clone: DefPath::new("std::clone::Clone::clone", tcx),
        }
    }
}

struct HashInsertFinder<'tcx> {
    typeck_results: &'tcx TypeckResults<'tcx>,
    record: HashSet<Span>,
}

impl<'tcx> intravisit::Visitor<'tcx> for HashInsertFinder<'tcx> {
    fn visit_expr(&mut self, ex: &'tcx Expr<'tcx>) {
        if let ExprKind::MethodCall(..) = ex.kind {
            let def_id = self
                .typeck_results
                .type_dependent_def_id(ex.hir_id)
                .unwrap();
            if def_id == DEFPATHS.get().unwrap().hashset_insert.last_def_id()
                || def_id == DEFPATHS.get().unwrap().hashmap_insert.last_def_id()
            {
                self.record.insert(ex.span);
            }
        }
        intravisit::walk_expr(self, ex);
    }
}

// check that the param of insert is moved from a cloned value
fn find_first_param_upside_clone(graph: &Graph, node: &GraphNode) -> Option<Local> {
    let mut clone_node_idx = None;
    let def_paths = &DEFPATHS.get().unwrap();
    let target_def_id = def_paths.clone.last_def_id();
    let mut node_operator = |graph: &Graph, idx: Local| -> DFSStatus {
        let node = &graph.nodes[idx];
        for op in node.ops.iter() {
            if let NodeOp::Call(def_id) = op {
                if *def_id == target_def_id {
                    clone_node_idx = Some(idx);
                    return DFSStatus::Stop;
                }
            }
        }
        DFSStatus::Continue
    };
    let mut seen = HashSet::new();
    graph.dfs(
        graph.edges[node.in_edges[1]].src, // the first param is self, so we use 1
        Direction::Upside,
        &mut node_operator,
        &mut Graph::equivalent_edge_validator,
        false,
        &mut seen,
    );
    clone_node_idx
}

// find the upside "new" node or "with_capacity" node of the "insert" node if it exists
fn find_hash_new_node(graph: &Graph, node: &GraphNode) -> Option<Local> {
    let mut new_node_idx = None;
    let def_paths = &DEFPATHS.get().unwrap();
    let mut node_operator = |graph: &Graph, idx: Local| -> DFSStatus {
        let node = &graph.nodes[idx];
        for op in node.ops.iter() {
            if let NodeOp::Call(def_id) = op {
                if *def_id == def_paths.hashset_new.last_def_id()
                    || *def_id == def_paths.hashmap_new.last_def_id()
                    || *def_id == def_paths.hashset_with.last_def_id()
                    || *def_id == def_paths.hashmap_with.last_def_id()
                {
                    new_node_idx = Some(idx);
                    return DFSStatus::Stop;
                }
            }
        }
        DFSStatus::Continue
    };
    let mut seen = HashSet::new();
    graph.dfs(
        graph.edges[node.in_edges[0]].src, // the first param is self
        Direction::Upside,
        &mut node_operator,
        &mut Graph::equivalent_edge_validator,
        false,
        &mut seen,
    );
    new_node_idx
}

fn report_hash_key_cloning(graph: &Graph, clone_span: Span, insert_span: Span) {
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
                .span(relative_pos_range(graph.span, insert_span))
                .label("Used here."),
        );
    let message = Level::Warning
        .title("Unnecessary memory cloning detected")
        .snippet(snippet)
        .footer(Level::Help.title("Use borrowings as keys."));
    let renderer = Renderer::styled();
    println!("{}", renderer.render(message));
}

pub struct HashKeyCloningCheck {
    record: Vec<(Span, Span)>,
}

impl OptCheck for HashKeyCloningCheck {
    fn new() -> Self {
        Self { record: Vec::new() }
    }

    fn check(&mut self, graph: &Graph, tcx: &TyCtxt) {
        let _ = &DEFPATHS.get_or_init(|| DefPaths::new(tcx));
        let def_id = graph.def_id;
        let body = tcx.hir_body_owned_by(def_id.as_local().unwrap());
        let typeck_results = tcx.typeck(def_id.as_local().unwrap());
        let mut hash_finder = HashInsertFinder {
            typeck_results,
            record: HashSet::new(),
        };
        intravisit::walk_body(&mut hash_finder, body);
        for node in graph.nodes.iter() {
            if hash_finder.record.contains(&node.span) {
                if let Some(clone_node_idx) = find_first_param_upside_clone(graph, node) {
                    if let Some(new_node_idx) = find_hash_new_node(graph, node) {
                        if !graph.is_connected(new_node_idx, Local::from_usize(0)) {
                            let clone_span = graph.nodes[clone_node_idx].span;
                            self.record.push((clone_span, node.span));
                        }
                    }
                }
            }
        }
    }

    fn report(&self, graph: &Graph) {
        for (clone_span, insert_span) in self.record.iter() {
            report_hash_key_cloning(graph, *clone_span, *insert_span);
        }
    }

    fn cnt(&self) -> usize {
        self.record.len()
    }
}
