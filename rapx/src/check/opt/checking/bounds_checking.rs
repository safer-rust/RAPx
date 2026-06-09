use rustc_middle::ty::TyCtxt;

use crate::analysis::dataflow::Graph;
use crate::check::opt::OptCheck;

pub mod bounds_extend;
pub mod bounds_len;
pub mod bounds_loop_push;

use bounds_extend::BoundsExtendCheck;
use bounds_len::BoundsLenCheck;
use bounds_loop_push::BoundsLoopPushCheck;

pub struct BoundsCheck {
    bounds_len: BoundsLenCheck,
    bounds_loop_push: BoundsLoopPushCheck,
    bounds_extend: BoundsExtendCheck,
}

impl OptCheck for BoundsCheck {
    fn new() -> Self {
        Self {
            bounds_len: BoundsLenCheck::new(),
            bounds_loop_push: BoundsLoopPushCheck::new(),
            bounds_extend: BoundsExtendCheck::new(),
        }
    }

    fn check(&mut self, graph: &Graph, tcx: &TyCtxt) {
        self.bounds_len.check(graph, tcx);
        self.bounds_loop_push.check(graph, tcx);
        self.bounds_extend.check(graph, tcx);
    }

    fn report(&self, graph: &Graph) {
        self.bounds_len.report(graph);
        self.bounds_loop_push.report(graph);
        self.bounds_extend.report(graph);
    }

    fn cnt(&self) -> usize {
        self.bounds_extend.cnt() + self.bounds_len.cnt() + self.bounds_loop_push.cnt()
    }
}
