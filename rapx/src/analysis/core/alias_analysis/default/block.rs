use super::assign::*;

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

#[derive(Debug, Clone)]
pub struct AliasBlockFacts<'tcx> {
    pub assignments: Vec<Assignment<'tcx>>,
    pub const_value: Vec<ConstValue>,
}

impl<'tcx> AliasBlockFacts<'tcx> {
    pub fn new() -> Self {
        Self {
            assignments: Vec::new(),
            const_value: Vec::new(),
        }
    }
}
