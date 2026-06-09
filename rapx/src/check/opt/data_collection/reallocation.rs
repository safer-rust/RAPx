pub mod flatten_collect;
pub mod unreserved_hash;
pub mod unreserved_vec;

use flatten_collect::FlattenCollectCheck;
use unreserved_hash::UnreservedHashCheck;
use unreserved_vec::UnreservedVecCheck;

use crate::analysis::dataflow::Graph;
use crate::check::opt::OptCheck;

use rustc_middle::ty::TyCtxt;

pub struct ReservationCheck {
    unreserved_hash: UnreservedHashCheck,
    unreserved_vec: UnreservedVecCheck,
    flatten_collect: FlattenCollectCheck,
}

impl OptCheck for ReservationCheck {
    fn new() -> Self {
        Self {
            unreserved_hash: UnreservedHashCheck::new(),
            unreserved_vec: UnreservedVecCheck::new(),
            flatten_collect: FlattenCollectCheck::new(),
        }
    }

    fn check(&mut self, graph: &Graph, tcx: &TyCtxt) {
        self.unreserved_hash.check(graph, tcx);
        self.unreserved_vec.check(graph, tcx);
        self.flatten_collect.check(graph, tcx);
    }

    fn report(&self, graph: &Graph) {
        self.unreserved_hash.report(graph);
        self.unreserved_vec.report(graph);
        self.flatten_collect.report(graph);
    }

    fn cnt(&self) -> usize {
        self.unreserved_hash.cnt() + self.unreserved_vec.cnt() + self.flatten_collect.cnt()
    }
}
