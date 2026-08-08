pub mod array_encoding;
pub mod string_lowercase;
pub mod string_push;
pub mod vec_encoding;

use crate::{analysis::dataflow::*, check::opt::OptCheck};

use annotate_snippets::Level;

use crate::check::opt::report::OptReport;

use rustc_middle::{mir::Local, ty::TyCtxt};
use rustc_span::Span;

use array_encoding::ArrayEncodingCheck;
use string_lowercase::StringLowercaseCheck;
use string_push::StringPushCheck;
use vec_encoding::VecEncodingCheck;

pub struct EncodingCheck {
    vec_encoding: VecEncodingCheck,
    array_encoding: ArrayEncodingCheck,
    string_push: StringPushCheck,
    string_lowercase: StringLowercaseCheck,
}

impl OptCheck for EncodingCheck {
    fn new() -> Self {
        Self {
            vec_encoding: VecEncodingCheck::new(),
            array_encoding: ArrayEncodingCheck::new(),
            string_push: StringPushCheck::new(),
            string_lowercase: StringLowercaseCheck::new(),
        }
    }

    fn check(&mut self, graph: &Graph, tcx: &TyCtxt) {
        self.vec_encoding.check(graph, tcx);
        self.array_encoding.check(graph, tcx);
        self.string_push.check(graph, tcx);
        self.string_lowercase.check(graph, tcx);
    }

    fn report(&self, graph: &Graph) {
        self.vec_encoding.report(graph);
        self.array_encoding.report(graph);
        self.string_push.report(graph);
        self.string_lowercase.report(graph);
    }

    fn cnt(&self) -> usize {
        self.vec_encoding.cnt()
            + self.array_encoding.cnt()
            + self.string_lowercase.cnt()
            + self.string_push.cnt()
    }
}

fn report_encoding_bug(graph: &Graph, span: Span) {
    OptReport::from_graph(graph)
        .title("Unnecessary encoding checkings detected")
        .annotate(Level::Error, span, "Checked here.")
        .footer("Use unsafe APIs.")
        .emit();
}

fn value_is_from_const(graph: &Graph, value_idx: Local) -> bool {
    let mut edge_validator = |graph: &Graph, idx: EdgeIdx| {
        let edge = &graph.edges[idx];
        let dst_node = &graph.nodes[edge.dst];
        let same_seq_edge_cnt = dst_node
            .in_edges
            .iter()
            .filter(|edge_idx| graph.edges[**edge_idx].seq == edge.seq)
            .count();
        match same_seq_edge_cnt {
            1 => Graph::always_true_edge_validator(graph, idx),
            2 => {
                if let EdgeOp::Index = edge.op {
                    DFSStatus::Continue
                } else {
                    DFSStatus::Stop
                }
            }
            _ => DFSStatus::Stop,
        }
    };
    graph
        .find_first_node(
            value_idx,
            Direction::Upside,
            &mut |graph: &Graph, idx: Local| {
                let node = &graph.nodes[idx];
                node.ops.iter().any(|op| {
                    if let NodeOp::Const(_, src_ty) = op {
                        src_ty.contains("u8")
                    } else {
                        false
                    }
                })
            },
            &mut edge_validator,
        )
        .is_some()
}
