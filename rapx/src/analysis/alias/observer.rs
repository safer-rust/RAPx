use crate::analysis::alias::default::graph::AliasGraph;
use rustc_span::Span;

pub trait AliasObserver {
    fn on_value_use(&mut self, _graph: &AliasGraph, _vidx: usize, _span: Span, _in_call: bool) {}
    fn on_value_assign(&mut self, _graph: &AliasGraph, _vidx: usize) {}
    fn on_state_change(&mut self, _graph: &AliasGraph) {}
    fn track_all_moves(&self) -> bool {
        false
    }
}

pub struct NoopAliasObserver;
impl AliasObserver for NoopAliasObserver {
    fn track_all_moves(&self) -> bool {
        true
    }
}
