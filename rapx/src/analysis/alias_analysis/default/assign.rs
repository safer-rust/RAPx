use rustc_middle::mir::Place;
use rustc_span::Span;

#[derive(PartialEq, Debug, Copy, Clone)]
pub enum AssignType {
    Copy,
    Move,
    InitBox,
    Variant,
}

//self-defined assignments structure.
#[derive(Debug, Clone)]
pub struct Assignment<'tcx> {
    pub lv: Place<'tcx>,
    pub rv: Place<'tcx>,
    pub atype: AssignType,
    pub span: Span,
}

impl<'tcx> Assignment<'tcx> {
    pub fn new(
        lv: Place<'tcx>,
        rv: Place<'tcx>,
        atype: AssignType,
        span: Span,
    ) -> Assignment<'tcx> {
        Assignment {
            lv,
            rv,
            atype,
            span,
        }
    }
}
