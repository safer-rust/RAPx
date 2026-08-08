use super::checks;
use super::graph::*;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct LocalSpot {
    pub bb: Option<usize>,
    pub local: Option<usize>,
}

impl LocalSpot {
    pub fn new(bb: usize, local: usize) -> Self {
        LocalSpot {
            bb: Some(bb),
            local: Some(local),
        }
    }
    pub fn from_local(local: usize) -> Self {
        LocalSpot {
            bb: None,
            local: Some(local),
        }
    }
    pub fn default() -> Self {
        LocalSpot {
            bb: None,
            local: None,
        }
    }
}

#[derive(Debug, Clone)]
pub struct DropRecord {
    pub value_index: usize,
    pub is_dropped: bool,
    pub drop_spot: LocalSpot,
    pub prop_chain: Vec<usize>,
    pub has_dropped_field: bool,
}

impl DropRecord {
    pub fn new(value_index: usize, is_dropped: bool, drop_spot: LocalSpot) -> Self {
        DropRecord {
            value_index,
            is_dropped,
            drop_spot,
            prop_chain: Vec::new(),
            has_dropped_field: false,
        }
    }
    pub fn false_record(value_index: usize) -> Self {
        DropRecord {
            value_index,
            is_dropped: false,
            drop_spot: LocalSpot::default(),
            prop_chain: Vec::new(),
            has_dropped_field: false,
        }
    }
    pub fn from(value_index: usize, record: &DropRecord) -> Self {
        DropRecord {
            value_index,
            is_dropped: record.is_dropped,
            drop_spot: record.drop_spot.clone(),
            prop_chain: record.prop_chain.clone(),
            has_dropped_field: record.has_dropped_field,
        }
    }
    pub fn clear(&mut self) {
        self.is_dropped = false;
        self.drop_spot = LocalSpot::default();
        self.prop_chain.clear();
        self.has_dropped_field = false;
    }
}

impl<'tcx> SafeDropGraph<'tcx> {
    /*
     * Mark the node as dropped.
     * flag_cleanup: used to distinguish if a bug occurs in the unwinding path.
     */
    pub fn add_to_drop_record(
        &mut self,
        value_idx: usize, // the value to be dropped
        bb_idx: usize,    // the block via_idx is dropped
        flag_cleanup: bool,
    ) {
        rap_debug!(
            "add_to_drop_record: value_idx = {}, bb_idx = {}",
            value_idx,
            bb_idx
        );
        if self
            .alias_graph
            .value_to_slot_idx(value_idx)
            .map_or(false, |si| self.alias_graph.pts_graph.slot_is_ref_count(si))
        {
            return;
        }
        if self.df_check(value_idx, bb_idx, self.alias_graph.span(), flag_cleanup) {
            return;
        }
        if !self.drop_record[value_idx].is_dropped {
            let local = self
                .alias_graph
                .value_to_slot_idx(value_idx)
                .and_then(|si| self.alias_graph.pts_graph.get_slot(si))
                .map(|s| s.local)
                .unwrap_or(value_idx);
            let drop_spot = LocalSpot::new(bb_idx, local);
            self.drop_record[value_idx] = DropRecord::new(value_idx, true, drop_spot);
            rap_debug!("{:?}", self.drop_record[value_idx]);
            checks::push_drop_info(
                &self.alias_graph,
                &mut self.drop_record,
                value_idx,
                drop_spot,
            );
        }
    }
}
