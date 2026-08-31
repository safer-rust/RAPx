use annotate_snippets::Level;

use crate::{
    analysis::dataflow::Graph, check::opt::OptCheck, check::opt::loop_visitors::MethodCallFinder,
};
use rustc_hir::intravisit;
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

use crate::check::opt::report::OptReport;

crate::def_paths! {
    slice_contains: "slice::contains",
}

pub struct SliceContainsCheck {
    record: Vec<Span>,
}

impl OptCheck for SliceContainsCheck {
    fn new() -> Self {
        Self { record: Vec::new() }
    }

    fn check(&mut self, graph: &Graph, tcx: &TyCtxt) {
        let _ = &DEFPATHS.get_or_init(|| DefPaths::new(tcx));
        let def_id = graph.def_id;
        let body = tcx.hir_body_owned_by(def_id.as_local().unwrap());
        let typeck_results = tcx.typeck(def_id.as_local().unwrap());
        let target_def_id = DEFPATHS.get().unwrap().slice_contains.last_def_id();
        let mut finder = MethodCallFinder::new(typeck_results, target_def_id);
        intravisit::walk_body(&mut finder, body);
        self.record = finder.into_record();
    }

    fn report(&self, graph: &Graph) {
        for contains_span in self.record.iter() {
            report_slice_contains_bug(graph, *contains_span);
        }
    }

    fn cnt(&self) -> usize {
        self.record.len()
    }
}

fn report_slice_contains_bug(graph: &Graph, contains_span: Span) {
    OptReport::from_graph(graph)
        .title("Improper data collection detected")
        .annotate(Level::Error, contains_span, "Slice contains happens here.")
        .footer("Use Set instead of Slice.")
        .emit();
}
