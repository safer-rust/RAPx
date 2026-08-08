use annotate_snippets::Level;

use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

use crate::{analysis::dataflow::*, check::opt::OptCheck};

use crate::check::opt::report::OptReport;

crate::def_paths! {
    vec_from_elem: "std::vec::from_elem",
}

pub struct VecInitCheck {
    record: Vec<Span>,
}

impl OptCheck for VecInitCheck {
    fn new() -> Self {
        Self { record: Vec::new() }
    }

    fn check(&mut self, graph: &Graph, tcx: &TyCtxt) {
        let def_paths = &DEFPATHS.get_or_init(|| DefPaths::new(tcx));
        for node in graph.nodes.iter() {
            for op in node.ops.iter() {
                if let NodeOp::Call(def_id) = op {
                    if *def_id == def_paths.vec_from_elem.last_def_id() {
                        self.record.push(node.span);
                    }
                }
            }
        }
    }

    fn report(&self, graph: &Graph) {
        for span in self.record.iter() {
            report_vec_init(graph, *span);
        }
    }

    fn cnt(&self) -> usize {
        self.record.len()
    }
}

fn report_vec_init(graph: &Graph, span: Span) {
    OptReport::from_graph(graph)
        .file_name(span)
        .title("Unnecessary data collection initialization detected")
        .annotate(Level::Error, span, "Initialization happens here")
        .footer("Use unsafe APIs to skip initialization.")
        .emit();
}
