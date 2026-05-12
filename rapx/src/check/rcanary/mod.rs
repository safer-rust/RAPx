pub mod ranalyzer;

use crate::analysis::{
    Analysis,
    core::ownedheap_analysis::{OHAResultMap, OwnedHeapAnalysis, default::OwnedHeapAnalyzer},
};
use ranalyzer::{FlowAnalysis, IcxSliceFroBlock, IntraFlowContext, MirGraph};
use rustc_middle::ty::TyCtxt;
use std::collections::HashMap;

#[allow(non_camel_case_types)]
#[derive(Clone)]
pub struct rCanary<'tcx> {
    tcx: TyCtxt<'tcx>,
    adt_owner: OHAResultMap,
    mir_graph: MirGraph,
}

impl<'tcx> rCanary<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, adt_owner: OHAResultMap) -> Self {
        Self {
            tcx,
            adt_owner: adt_owner,
            mir_graph: HashMap::default(),
        }
    }

    pub fn start(&mut self) {
        let mut heap = OwnedHeapAnalyzer::new(self.tcx);
        heap.run();
        let adt_owner = heap.get_all_items();
        let rcx_boxed = Box::new(rCanary::new(self.tcx, adt_owner));
        let rcx = Box::leak(rcx_boxed);
        FlowAnalysis::new(rcx).start();
    }

    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    pub fn adt_owner(&self) -> &OHAResultMap {
        &self.adt_owner
    }

    pub fn adt_owner_mut(&mut self) -> &mut OHAResultMap {
        &mut self.adt_owner
    }

    pub fn mir_graph(&self) -> &MirGraph {
        &self.mir_graph
    }

    pub fn mir_graph_mut(&mut self) -> &mut MirGraph {
        &mut self.mir_graph
    }
}

pub trait Tcx<'tcx, 'o, 'a> {
    fn tcx(&'o self) -> TyCtxt<'tcx>;
}

pub trait Rcx<'tcx, 'o, 'a> {
    fn rcx(&'o self) -> &'a rCanary<'tcx>;

    fn tcx(&'o self) -> TyCtxt<'tcx>;
}

pub trait RcxMut<'tcx, 'o, 'a> {
    fn rcx(&'o self) -> &'o rCanary<'tcx>;

    fn rcx_mut(&'o mut self) -> &'o mut rCanary<'tcx>;

    fn tcx(&'o self) -> TyCtxt<'tcx>;
}

pub trait IcxMut<'tcx, 'ctx, 'o> {
    fn icx(&'o self) -> &'o IntraFlowContext<'tcx, 'ctx>;

    fn icx_mut(&'o mut self) -> &'o mut IntraFlowContext<'tcx, 'ctx>;
}

pub trait IcxSliceMut<'tcx, 'ctx, 'o> {
    fn icx_slice(&'o self) -> &'o IcxSliceFroBlock<'tcx, 'ctx>;

    fn icx_slice_mut(&'o mut self) -> &'o mut IcxSliceFroBlock<'tcx, 'ctx>;
}
