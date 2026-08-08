use annotate_snippets::Level;

use crate::{analysis::dataflow::*, check::opt::OptCheck};
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

use crate::check::opt::check_utils::node_matches_call;
use crate::check::opt::report::OptReport;

crate::def_paths! {
    vec_remove: "std::vec::Vec::remove",
    vec_insert: "std::vec::Vec::insert",
}

pub struct VecRemoveCheck {
    record: Vec<Span>,
}

fn is_0_usize(node: &GraphNode) -> bool {
    for op in node.ops.iter() {
        if let NodeOp::Const(desc, _) = op {
            if desc.eq("0_usize") {
                return true;
            }
        }
    }
    false
}

impl OptCheck for VecRemoveCheck {
    fn new() -> Self {
        Self { record: vec![] }
    }

    fn check(&mut self, graph: &Graph, tcx: &TyCtxt) {
        let def_paths = &DEFPATHS.get_or_init(|| DefPaths::new(tcx));
        for node in graph.nodes.iter() {
            if node_matches_call(
                node,
                &[
                    def_paths.vec_remove.last_def_id(),
                    def_paths.vec_insert.last_def_id(),
                ],
            ) {
                let index_edge = &graph.edges[node.in_edges[1]];
                let index_node = &graph.nodes[index_edge.src];
                if is_0_usize(index_node) {
                    self.record.push(node.span);
                }
            }
        }
    }

    fn report(&self, graph: &Graph) {
        for span in self.record.iter() {
            report_vec_remove_bug(graph, *span);
        }
    }

    fn cnt(&self) -> usize {
        self.record.len()
    }
}

fn report_vec_remove_bug(graph: &Graph, span: Span) {
    OptReport::from_graph(graph)
        .title("Improper data collection detected")
        .annotate(
            Level::Error,
            span,
            "Vec increasement / decreasement happens here.",
        )
        .footer("Use VecQueue instead of Vec.")
        .emit();
}
