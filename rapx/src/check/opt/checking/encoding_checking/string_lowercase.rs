use annotate_snippets::Level;

use rustc_hir::intravisit;
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

use crate::analysis::dataflow::Graph;
use crate::check::opt::OptCheck;
use crate::check::opt::loop_visitors::MethodCallFinder;

use crate::check::opt::report::OptReport;

crate::def_paths! {
    string_to_lowercase: "str::to_lowercase",
}

pub struct StringLowercaseCheck {
    record: Vec<Span>,
}

impl OptCheck for StringLowercaseCheck {
    fn new() -> Self {
        Self { record: Vec::new() }
    }

    fn check(&mut self, graph: &Graph, tcx: &TyCtxt) {
        let _ = &DEFPATHS.get_or_init(|| DefPaths::new(tcx));
        let def_id = graph.def_id;
        let body = tcx.hir_body_owned_by(def_id.as_local().unwrap());
        let typeck_results = tcx.typeck(def_id.as_local().unwrap());
        let target_def_id = DEFPATHS.get().unwrap().string_to_lowercase.last_def_id();
        let mut finder = MethodCallFinder::new(typeck_results, target_def_id);
        intravisit::walk_body(&mut finder, body);
        self.record = finder.into_record();
    }

    fn report(&self, graph: &Graph) {
        for contains_span in self.record.iter() {
            report_string_ascii_bug(graph, *contains_span);
        }
    }

    fn cnt(&self) -> usize {
        self.record.len()
    }
}

fn report_string_ascii_bug(graph: &Graph, contains_span: Span) {
    OptReport::from_graph(graph)
        .title("Unnecessary encoding checkings detected.")
        .annotate(Level::Error, contains_span, "Checked here.")
        .footer("Use to_ascii_lowercase instead.")
        .emit();
}
