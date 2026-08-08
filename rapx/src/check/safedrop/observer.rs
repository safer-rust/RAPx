use rustc_span::Span;

use crate::analysis::alias::default::graph::AliasGraph;
use crate::analysis::alias::observer::AliasObserver;

use super::bug_records::*;
use super::checks;
use super::drop::DropRecord;

pub struct SafeDropObserver<'a> {
    pub drop_record: &'a mut Vec<DropRecord>,
    pub bug_records: &'a mut BugRecords,
    pub current_bb: usize,
}

impl AliasObserver for SafeDropObserver<'_> {
    fn on_value_use(&mut self, graph: &AliasGraph, vidx: usize, span: Span, in_call: bool) {
        checks::sync_drop_record(graph, self.drop_record);
        checks::uaf_check(
            graph,
            self.drop_record,
            self.bug_records,
            vidx,
            self.current_bb,
            span,
            in_call,
        );
    }

    fn on_value_assign(&mut self, graph: &AliasGraph, vidx: usize) {
        checks::sync_drop_record(graph, self.drop_record);
        checks::clear_drop_info(graph, self.drop_record, vidx);
    }

    fn on_state_change(&mut self, graph: &AliasGraph) {
        checks::sync_drop_record(graph, self.drop_record);
    }
}
