mod report;
mod vm;

use rustc_middle::ty::TyCtxt;

/// Detect leaked ownership released into raw pointers or references through VM replay.
#[allow(non_camel_case_types)]
pub struct rCanary<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> rCanary<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self { tcx }
    }

    pub fn start(&self) {
        let leaks = vm::detect(self.tcx);
        for local in self.tcx.mir_keys(()) {
            let def_id = local.to_def_id();
            if let Some(spans) = leaks.get(&def_id) {
                report::emit(
                    self.tcx,
                    def_id,
                    self.tcx.optimized_mir(def_id),
                    spans.iter().copied(),
                );
            }
        }
    }
}
