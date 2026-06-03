use super::assign::*;
use crate::graphs::scc::SccInfo;
use rustc_data_structures::fx::FxHashSet;
use rustc_middle::mir::Terminator;

/// Each block is a strongly-connected component on the control-flow graph.
#[derive(Debug, Clone)]
pub struct Block<'tcx> {
    pub index: usize,
    pub is_cleanup: bool,
    pub next: FxHashSet<usize>,
    pub assignments: Vec<Assignment<'tcx>>,
    pub const_value: Vec<ConstValue>,
    // Used in scc handling: to clear the assignments of the enter node.
    pub assigned_locals: FxHashSet<usize>,
    pub terminator: Term<'tcx>,
    /// All nodes belongs to a SCC.
    /// This field could be a single node SCC.
    /// The loops in the CFG are natural loops, so each SCC has only one enter.
    pub scc: SccInfo,
}

#[derive(Debug, Clone)]
pub enum Term<'tcx> {
    Call(Terminator<'tcx>),
    Drop(Terminator<'tcx>),
    Switch(Terminator<'tcx>),
    None,
}

#[derive(Debug, Clone)]
pub struct ConstValue {
    pub local: usize,
    pub value: usize,
}

impl ConstValue {
    pub fn new(local: usize, value: usize) -> Self {
        ConstValue { local, value }
    }
}

impl<'tcx> Block<'tcx> {
    pub fn new(index: usize, is_cleanup: bool) -> Block<'tcx> {
        Block {
            index,
            is_cleanup,
            next: FxHashSet::<usize>::default(),
            assignments: Vec::<Assignment<'tcx>>::new(),
            const_value: Vec::<ConstValue>::new(),
            assigned_locals: FxHashSet::<usize>::default(),
            terminator: Term::None,
            scc: SccInfo::new(index),
        }
    }

    pub fn add_next(&mut self, index: usize) {
        self.next.insert(index);
    }
}
