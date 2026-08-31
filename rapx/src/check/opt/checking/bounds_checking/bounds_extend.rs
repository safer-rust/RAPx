use once_cell::sync::OnceCell;

use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

use crate::{analysis::dataflow::*, helpers::def_path::DefPath};
use annotate_snippets::Level;

use crate::check::opt::check_utils::node_matches_call;
use crate::check::opt::report::OptReport;

use super::super::super::LEVEL;
use super::super::super::NO_STD;
use crate::check::opt::OptCheck;
static DEFPATHS: OnceCell<DefPaths> = OnceCell::new();

struct DefPaths {
    vec_extend_from_slice: DefPath,
}

impl DefPaths {
    pub fn new(tcx: &TyCtxt<'_>) -> Self {
        let no_std = NO_STD.lock().unwrap();
        if *no_std {
            Self {
                vec_extend_from_slice: DefPath::new("alloc::vec::Vec::extend_from_slice", &tcx),
            }
        } else {
            Self {
                vec_extend_from_slice: DefPath::new("std::vec::Vec::extend_from_slice", &tcx),
            }
        }
    }
}

pub struct BoundsExtendCheck {
    pub record: Vec<Span>,
}

impl OptCheck for BoundsExtendCheck {
    fn new() -> Self {
        Self { record: Vec::new() }
    }

    fn check(&mut self, graph: &Graph, tcx: &TyCtxt) {
        let level = LEVEL.lock().unwrap();
        if *level <= 1 {
            return;
        }
        let def_paths = &DEFPATHS.get_or_init(|| DefPaths::new(tcx));
        for node in graph.nodes.iter() {
            if node_matches_call(node, &[def_paths.vec_extend_from_slice.last_def_id()]) {
                self.record.push(node.span);
            }
        }
    }

    fn report(&self, graph: &Graph) {
        for span in self.record.iter() {
            report_extend_bug(graph, *span);
        }
    }

    fn cnt(&self) -> usize {
        self.record.len()
    }
}

fn report_extend_bug(graph: &Graph, span: Span) {
    OptReport::from_graph(graph)
        .title("Unnecessary bound checkings detected")
        .annotate(Level::Error, span, "Checked here.")
        .footer("Manipulate memory directly.")
        .emit();
}
