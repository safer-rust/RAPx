use rustc_data_structures::fx::FxHashSet;
use rustc_middle::{mir::Terminator, ty::TyCtxt};
use rustc_span::{Span, def_id::DefId};

/// Reusable CFG block structure shared by analyses built over MIR.
#[derive(Debug, Clone)]
pub struct CfgBlock<'tcx> {
    pub index: usize,
    pub is_cleanup: bool,
    pub next: FxHashSet<usize>,
    pub terminator: Option<Terminator<'tcx>>,
}

impl<'tcx> CfgBlock<'tcx> {
    pub fn new(index: usize, is_cleanup: bool) -> Self {
        Self {
            index,
            is_cleanup,
            next: FxHashSet::default(),
            terminator: None,
        }
    }

    pub fn add_next(&mut self, index: usize) {
        self.next.insert(index);
    }
}

/// Control-flow graph metadata independent from any particular analysis facts.
#[derive(Clone)]
pub struct ControlFlowGraph<'tcx> {
    pub def_id: DefId,
    pub tcx: TyCtxt<'tcx>,
    pub arg_size: usize,
    pub span: Span,
    pub blocks: Vec<CfgBlock<'tcx>>,
}

impl<'tcx> ControlFlowGraph<'tcx> {
    pub fn new(
        def_id: DefId,
        tcx: TyCtxt<'tcx>,
        span: Span,
        arg_size: usize,
        blocks: Vec<CfgBlock<'tcx>>,
    ) -> Self {
        Self {
            def_id,
            tcx,
            arg_size,
            span,
            blocks,
        }
    }
}
