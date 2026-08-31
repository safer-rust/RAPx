use annotate_snippets::Level;

use crate::{analysis::dataflow::*, check::opt::OptCheck};
use rustc_middle::{mir::Local, ty::TyCtxt};
use rustc_span::Span;

use crate::check::opt::check_utils::node_matches_any_call;
use crate::check::opt::report::OptReport;

crate::def_paths! {
    hashset_new: "std::collections::HashSet::new",
    hashset_with_capacity: "std::collections::HashSet::with_capacity",
    hashmap_new: "std::collections::HashMap::new",
    hashmap_with_capacity: "std::collections::HashMap::with_capacity",
    btreeset_new: "std::collections::BTreeSet::new",
    btreemap_new: "std::collections::BTreeMap::new",
}

pub struct LocalSetCheck {
    record: Vec<Span>,
}

impl OptCheck for LocalSetCheck {
    fn new() -> Self {
        Self { record: Vec::new() }
    }

    fn check(&mut self, graph: &Graph, tcx: &TyCtxt) {
        let def_paths = &DEFPATHS.get_or_init(|| DefPaths::new(tcx));
        for (node_idx, node) in graph.nodes.iter_enumerated() {
            if node_matches_any_call(node, |id| {
                id == def_paths.hashset_new.last_def_id()
                    || id == def_paths.hashmap_new.last_def_id()
                    || id == def_paths.btreemap_new.last_def_id()
                    || id == def_paths.btreeset_new.last_def_id()
                    || id == def_paths.hashmap_with_capacity.last_def_id()
                    || id == def_paths.hashset_with_capacity.last_def_id()
            }) && !graph.is_connected(Local::from_usize(0), node_idx)
            {
                self.record.push(node.span);
            }
        }
    }

    fn report(&self, graph: &Graph) {
        for span in self.record.iter() {
            report_local_set(graph, *span);
        }
    }

    fn cnt(&self) -> usize {
        self.record.len()
    }
}

fn report_local_set(graph: &Graph, span: Span) {
    OptReport::from_graph(graph)
        .file_name(span)
        .title("Unnecessary data collection initialization detected")
        .annotate(Level::Error, span, "Initialization happens here")
        .footer("Move it into parameter list and use hash table to save allocation.")
        .emit();
}
