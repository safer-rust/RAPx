use crate::{analysis::dataflow::*, check::opt::OptCheck};
use rustc_hir::intravisit;
use rustc_middle::mir::Local;
use rustc_middle::ty::TyCtxt;

use annotate_snippets::Level;
use rustc_span::Span;

use crate::check::opt::check_utils::node_matches_call;
use crate::check::opt::report::OptReport;

use super::super::super::LEVEL;
use super::super::super::loop_visitors::LoopFinder;

crate::def_paths! {
    vec_new: "std::vec::Vec::new",
    vec_push: "std::vec::Vec::push",
    vec_with_capacity: "std::vec::Vec::with_capacity",
    vec_reserve: "std::vec::Vec::reserve",
}

pub struct UnreservedVecCheck {
    record: Vec<Span>,
}

fn find_upside_reservation(graph: &Graph, node_idx: Local) -> Option<Local> {
    let def_paths = &DEFPATHS.get().unwrap();
    graph.find_first_node(
        node_idx,
        Direction::Upside,
        &mut |graph: &Graph, idx: Local| {
            let node = &graph.nodes[idx];
            for op in node.ops.iter() {
                if let NodeOp::Call(def_id) = op {
                    if *def_id == def_paths.vec_with_capacity.last_def_id()
                        || *def_id == def_paths.vec_reserve.last_def_id()
                    {
                        return true;
                    }
                }
            }
            false
        },
        &mut Graph::equivalent_edge_validator,
    )
}

impl OptCheck for UnreservedVecCheck {
    fn new() -> Self {
        Self { record: Vec::new() }
    }

    fn check(&mut self, graph: &Graph, tcx: &TyCtxt) {
        let def_paths = &DEFPATHS.get_or_init(|| DefPaths::new(tcx));
        let level = LEVEL.lock().unwrap();
        if *level == 2 {
            for (node_idx, node) in graph.nodes.iter_enumerated() {
                if node_matches_call(node, &[def_paths.vec_new.last_def_id()]) {
                    self.record.push(node.span);
                }
                if node_matches_call(node, &[def_paths.vec_push.last_def_id()]) {
                    if let None = find_upside_reservation(graph, node_idx) {
                        self.record.push(node.span);
                    }
                }
            }
        }

        let def_id = graph.def_id;
        let body = tcx.hir_body_owned_by(def_id.as_local().unwrap());
        let typeck_results = tcx.typeck(def_id.as_local().unwrap());
        let target_def_id = def_paths.vec_push.last_def_id();
        let mut loop_finder = LoopFinder::new(typeck_results, target_def_id);
        intravisit::walk_body(&mut loop_finder, body);
        for (_, push_record) in loop_finder.into_record() {
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
    OptReport::from_graph(graph)
        .file_name(span)
        .title("Improper data collection detected")
        .annotate(Level::Error, span, "Space unreserved.")
        .footer("Reserve enough space.")
        .emit();
}
