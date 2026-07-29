use once_cell::sync::OnceCell;

use rustc_hir::intravisit;
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

use crate::analysis::dataflow::Graph;
use crate::helpers::def_path::DefPath;
use crate::utils::span::{
    relative_pos_range, span_to_filename, span_to_first_line, span_to_line_number,
    span_to_source_code, span_to_trimmed_span,
};
use annotate_snippets::{Level, Renderer, Snippet};

use super::super::super::LEVEL;
use super::super::super::NO_STD;
use super::super::super::loop_visitors::LoopFinder;
static DEFPATHS: OnceCell<DefPaths> = OnceCell::new();

struct DefPaths {
    vec_push: DefPath,
}

impl DefPaths {
    pub fn new(tcx: &TyCtxt<'_>) -> Self {
        let no_std = NO_STD.lock().unwrap();
        if *no_std {
            Self {
                vec_push: DefPath::new("alloc::vec::Vec::push", tcx),
            }
        } else {
            Self {
                vec_push: DefPath::new("std::vec::Vec::push", tcx),
            }
        }
    }
}

use crate::check::opt::OptCheck;

pub struct BoundsLoopPushCheck {
    pub record: Vec<(Span, Vec<Span>)>,
}

impl OptCheck for BoundsLoopPushCheck {
    fn new() -> Self {
        Self { record: Vec::new() }
    }

    fn check(&mut self, graph: &Graph, tcx: &TyCtxt) {
        let def_paths = &DEFPATHS.get_or_init(|| DefPaths::new(tcx));
        let level = LEVEL.lock().unwrap();
        if *level == 2 {
            let def_id = graph.def_id;
            let body = tcx.hir_body_owned_by(def_id.as_local().unwrap());
            let typeck_results = tcx.typeck(def_id.as_local().unwrap());
            let target_def_id = def_paths.vec_push.last_def_id();
            let mut loop_finder = LoopFinder::new(typeck_results, target_def_id);
            intravisit::walk_body(&mut loop_finder, body);
            self.record = loop_finder.into_record();
        }
    }

    fn report(&self, _: &Graph) {
        for (loop_span, push_record) in self.record.iter() {
            report_loop_push_bug(*loop_span, push_record);
        }
    }

    fn cnt(&self) -> usize {
        self.record.iter().map(|(_, spans)| spans.len()).sum()
    }
}

fn report_loop_push_bug(loop_span: Span, push_record: &Vec<Span>) {
    let code_source = span_to_source_code(loop_span);
    let filename = span_to_filename(loop_span);
    let mut snippet = Snippet::source(&code_source)
        .line_start(span_to_line_number(loop_span))
        .origin(&filename)
        .fold(true)
        .annotation(
            Level::Info
                .span(relative_pos_range(
                    loop_span,
                    span_to_trimmed_span(span_to_first_line(loop_span)),
                ))
                .label("A loop operation."),
        );
    for push_span in push_record {
        snippet = snippet.annotation(
            Level::Error
                .span(relative_pos_range(loop_span, *push_span))
                .label("Push happens here."),
        );
    }
    let message = Level::Warning
        .title("Unnecessary bounds checkings detected")
        .snippet(snippet);
    let renderer = Renderer::styled();
    rap_warn!("{}", renderer.render(message));
}
