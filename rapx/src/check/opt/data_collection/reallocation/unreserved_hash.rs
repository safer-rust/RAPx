use crate::{analysis::dataflow::*, check::opt::OptCheck};
use rustc_middle::{mir::Local, ty::TyCtxt};

use annotate_snippets::Level;
use rustc_span::Span;

use crate::check::opt::check_utils::node_matches_call;
use crate::check::opt::report::OptReport;

crate::def_paths! {
    hashset_insert: "std::collections::HashSet::insert",
    hashmap_insert: "std::collections::HashMap::insert",
    hashset_new: "std::collections::HashSet::new",
    hashmap_new: "std::collections::HashMap::new",
    entry: "std::collections::HashMap::entry",
}

pub struct UnreservedHashCheck {
    record: Vec<(Span, Span)>,
}

fn find_downside_hash_insert_node(graph: &Graph, node_idx: Local) -> Option<Local> {
    let def_paths = &DEFPATHS.get().unwrap();
    graph.find_first_node(
        node_idx,
        Direction::Downside,
        &mut |graph: &Graph, idx: Local| {
            let node = &graph.nodes[idx];
            for op in node.ops.iter() {
                if let NodeOp::Call(def_id) = op {
                    if *def_id == def_paths.hashmap_insert.last_def_id()
                        || *def_id == def_paths.hashset_insert.last_def_id()
                        || *def_id == def_paths.entry.last_def_id()
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

impl OptCheck for UnreservedHashCheck {
    fn new() -> Self {
        Self { record: Vec::new() }
    }

    fn check(&mut self, graph: &Graph, tcx: &TyCtxt) {
        let def_paths = &DEFPATHS.get_or_init(|| DefPaths::new(tcx));
        for (node_idx, node) in graph.nodes.iter_enumerated() {
            if node_matches_call(
                node,
                &[
                    def_paths.hashmap_new.last_def_id(),
                    def_paths.hashset_new.last_def_id(),
                ],
            ) {
                if let Some(insert_idx) = find_downside_hash_insert_node(graph, node_idx) {
                    let insert_node = &graph.nodes[insert_idx];
                    self.record.push((node.span, insert_node.span));
                }
            }
        }
    }

    fn report(&self, graph: &Graph) {
        for (hash_span, insert_span) in self.record.iter() {
            report_unreserved_hash_bug(graph, *hash_span, *insert_span);
        }
    }

    fn cnt(&self) -> usize {
        self.record.len()
    }
}

fn report_unreserved_hash_bug(graph: &Graph, hash_span: Span, insert_span: Span) {
    OptReport::from_graph(graph)
        .file_name(hash_span)
        .title("Improper data collection detected")
        .annotate(Level::Error, hash_span, "Space unreserved.")
        .annotate(Level::Info, insert_span, "Insertion happens here.")
        .footer("Reserve enough space.")
        .emit();
}
