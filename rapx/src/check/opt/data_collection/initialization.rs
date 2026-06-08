pub mod local_set;
pub mod vec_init;

use local_set::LocalSetCheck;
use vec_init::VecInitCheck;

use crate::analysis::core::dataflow::Graph;
use crate::check::opt::OptCheck;

use super::super::LEVEL;
use rustc_middle::ty::TyCtxt;

pub struct InitializationCheck {
    local_set: LocalSetCheck,
    vec_init: VecInitCheck,
}

impl OptCheck for InitializationCheck {
    fn new() -> Self {
        Self {
            local_set: LocalSetCheck::new(),
            vec_init: VecInitCheck::new(),
        }
    }

    fn check(&mut self, graph: &Graph, tcx: &TyCtxt) {
        let level = LEVEL.lock().unwrap();
        if *level == 2 {
            self.local_set.check(graph, tcx);
            self.vec_init.check(graph, tcx);
        }
    }

    fn report(&self, graph: &Graph) {
        self.local_set.report(graph);
        self.vec_init.report(graph);
    }

    fn cnt(&self) -> usize {
        self.local_set.cnt() + self.vec_init.cnt()
    }
}
