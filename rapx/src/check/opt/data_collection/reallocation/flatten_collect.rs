use rustc_middle::ty::TyCtxt;

use crate::{analysis::dataflow::*, check::opt::OptCheck};
use annotate_snippets::Level;
use rustc_span::Span;

use crate::check::opt::check_utils::node_matches_call;
use crate::check::opt::report::OptReport;

crate::def_paths! {
    flat_map: "std::iter::Iterator::flat_map",
    flatten: "std::iter::Iterator::flatten",
    collect: "std::iter::Iterator::collect",
}

pub struct FlattenCollectCheck {
    record: Vec<Span>,
}

impl OptCheck for FlattenCollectCheck {
    fn new() -> Self {
        Self { record: Vec::new() }
    }

    fn check(&mut self, graph: &Graph, tcx: &TyCtxt) {
        let _ = &DEFPATHS.get_or_init(|| DefPaths::new(tcx));
        let def_paths = DEFPATHS.get().unwrap();
        for node in graph.nodes.iter() {
            if node_matches_call(
                node,
                &[
                    def_paths.flat_map.last_def_id(),
                    def_paths.flatten.last_def_id(),
                ],
            ) {
                for edge_idx in node.out_edges.iter() {
                    let dst_idx = graph.edges[*edge_idx].dst;
                    let dst_node = &graph.nodes[dst_idx];
                    if node_matches_call(dst_node, &[def_paths.collect.last_def_id()]) {
                        self.record.push(dst_node.span);
                    }
                }
            }
        }
    }

    fn report(&self, graph: &Graph) {
        for span in self.record.iter() {
            report_flatten_collect(graph, *span);
        }
    }

    fn cnt(&self) -> usize {
        self.record.len()
    }
}

fn report_flatten_collect(graph: &Graph, span: Span) {
    OptReport::from_graph(graph)
        .file_name(span)
        .message_level(Level::Error)
        .title("Data collection inefficiency detected")
        .annotate(Level::Error, span, "Flatten then collect.")
        .footer("Use extend manually.")
        .emit();
}
