use annotate_snippets::{Level, Renderer, Snippet};

use once_cell::sync::OnceCell;

use crate::{
    analysis::{
        core::dataflow::*,
        utils::def_path::DefPath,
    },
    check::opt::OptCheck,
    utils::log::{relative_pos_range, span_to_filename, span_to_line_number, span_to_source_code},
};
use rustc_hir::def_id::DefId;
use rustc_middle::{mir::Local, ty::TyCtxt};
use rustc_span::Span;

struct DefPaths {
    hashset_new: DefPath,
    hashset_with_capacity: DefPath,
    hashmap_new: DefPath,
    hashmap_with_capacity: DefPath,
    btreeset_new: DefPath,
    btreemap_new: DefPath,
}

static DEFPATHS: OnceCell<DefPaths> = OnceCell::new();

impl DefPaths {
    pub fn new(tcx: &TyCtxt<'_>) -> Self {
        Self {
            hashset_new: DefPath::new("std::collections::HashSet::new", tcx),
            hashset_with_capacity: DefPath::new("std::collections::HashSet::with_capacity", tcx),
            hashmap_new: DefPath::new("std::collections::HashMap::new", tcx),
            hashmap_with_capacity: DefPath::new("std::collections::HashMap::with_capacity", tcx),
            btreeset_new: DefPath::new("std::collections::BTreeSet::new", tcx),
            btreemap_new: DefPath::new("std::collections::BTreeMap::new", tcx),
        }
    }

    fn has_id(&self, id: DefId) -> bool {
        id == self.hashset_new.last_def_id()
            || id == self.hashmap_new.last_def_id()
            || id == self.btreemap_new.last_def_id()
            || id == self.btreeset_new.last_def_id()
            || id == self.hashmap_with_capacity.last_def_id()
            || id == self.hashset_with_capacity.last_def_id()
    }
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
            for op in node.ops.iter() {
                if let NodeOp::Call(def_id) = op {
                    if def_paths.has_id(*def_id)
                        && !graph.is_connected(Local::from_usize(0), node_idx)
                    {
                        self.record.push(node.span);
                    }
                }
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
    let code_source = span_to_source_code(graph.span);
    let filename = span_to_filename(span);
    let snippet = Snippet::source(&code_source)
        .line_start(span_to_line_number(graph.span))
        .origin(&filename)
        .fold(true)
        .annotation(
            Level::Error
                .span(relative_pos_range(graph.span, span))
                .label("Initialization happens here"),
        );
    let message = Level::Warning
        .title("Unnecessary data collection initialization detected")
        .snippet(snippet)
        .footer(
            Level::Help.title("Move it into parameter list and use hash table to save allocation."),
        );
    let renderer = Renderer::styled();
    println!("{}", renderer.render(message));
}
