use super::graph::*;
use rustc_middle::mir::SourceInfo;
use std::usize;

#[derive(Debug, Copy, Clone)]
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
        _info: &SourceInfo,
        flag_cleanup: bool,
    ) {
        rap_debug!(
            "add_to_drop_record: value_idx = {}, bb_idx = {}",
            value_idx,
            bb_idx
        );
        //Rc drop
        if self.mop_graph.values[value_idx].is_ref_count() {
            return;
        }
        if self.df_check(value_idx, bb_idx, self.mop_graph.span, flag_cleanup) {
            return;
        }
        if !self.drop_record[value_idx].is_dropped {
            let drop_spot = LocalSpot::new(bb_idx, self.mop_graph.values[value_idx].local);
            self.drop_record[value_idx] = DropRecord::new(value_idx, true, drop_spot);
            rap_debug!("{:?}", self.drop_record[value_idx]);
            self.push_drop_info(value_idx, drop_spot);
        }
    }

    pub fn push_drop_info(&mut self, value_idx: usize, drop_spot: LocalSpot) {
        self.push_drop_bottom_up(value_idx, drop_spot);
        self.push_drop_top_down(value_idx, drop_spot);
        //self.push_drop_alias(value_idx, drop_spot);
    }

    pub fn push_drop_alias(&mut self, value_idx: usize, drop_spot: LocalSpot) {
        rap_debug!("push_drop_alias: value_idx = {}", value_idx,);
        if let Some(aliases) = self.mop_graph.get_alias_set(value_idx) {
            for i in aliases {
                if i != value_idx {
                    self.drop_record[i] = DropRecord::new(i, true, drop_spot);
                    self.drop_record[i].prop_chain = self.drop_record[value_idx].prop_chain.clone();
                    self.drop_record[i].prop_chain.push(i);
                    rap_debug!("{:?}", self.drop_record[i]);
                }
            }
        }
    }

    ///drop the fields of the root node.
    pub fn push_drop_top_down(&mut self, value_idx: usize, drop_spot: LocalSpot) {
        rap_debug!("push_drop_top_down: value_idx = {}", value_idx);
        let mut prop_chain = vec![value_idx];
        for (_field_id, field_value_id) in self.mop_graph.values[value_idx].fields.clone() {
            self.drop_record[field_value_id] = DropRecord::new(field_value_id, true, drop_spot);
            prop_chain.push(field_value_id);
            self.drop_record[field_value_id].prop_chain = prop_chain.clone();
            rap_debug!("{:?}", self.drop_record[field_value_id]);
            self.push_drop_top_down(field_value_id, drop_spot);
        }
    }

    pub fn push_drop_bottom_up(&mut self, value_idx: usize, drop_spot: LocalSpot) {
        rap_debug!("push_drop_bottom_up: value_idx = {}", value_idx);
        let mut father = self.mop_graph.values[value_idx].father.clone();
        let mut prop_chain = vec![value_idx];
        while let Some(father_info) = father {
            let father_idx = father_info.father_value_id;
            self.drop_record[father_idx].has_dropped_field = true;
            if !self.drop_record[father_idx].is_dropped {
                prop_chain.push(father_idx);
                self.drop_record[father_idx].prop_chain = prop_chain.clone();
                self.drop_record[father_idx].drop_spot = drop_spot;
            }
            rap_debug!("{:?}", self.drop_record[father_idx]);
            father = self.mop_graph.values[father_idx].father.clone();
        }
    }

    pub fn fetch_drop_info(&mut self, value_idx: usize) {
        self.fetch_drop_from_bottom(value_idx);
        self.fetch_drop_from_top(value_idx);
        self.fetch_drop_from_alias(value_idx);
    }

    pub fn clear_drop_info(&mut self, value_idx: usize) {
        rap_debug!("clear_drop: value_idx = {}", value_idx);
        self.drop_record[value_idx].clear();
        self.clear_field_drop(value_idx);
        self.clear_father_drop(value_idx);
    }

    pub fn clear_father_drop(&mut self, value_idx: usize) {
        rap_debug!("clear_drop_father: value_idx = {}", value_idx);
        // to fix: this is an over approximation.
        let mut father = self.mop_graph.values[value_idx].father.clone();
        while let Some(father_info) = father {
            let father_idx = father_info.father_value_id;
            if !self.drop_record[father_idx].is_dropped {
                self.drop_record[father_idx].clear();
            }
            father = self.mop_graph.values[father_idx].father.clone();
        }
    }

    pub fn clear_field_drop(&mut self, value_idx: usize) {
        rap_debug!("clear_field_drop: value_idx = {}", value_idx);
        for (_field_id, field_value_id) in self.mop_graph.values[value_idx].fields.clone() {
            self.drop_record[field_value_id].clear();
            self.clear_field_drop(field_value_id);
        }
    }

    pub fn fetch_drop_from_bottom(&mut self, value_idx: usize) {
        rap_debug!("fetch_drop_from_bottom: value_idx = {}", value_idx);
        for (_field_id, field_value_id) in self.mop_graph.values[value_idx].fields.clone() {
            rap_debug!("{:?}", self.drop_record[field_value_id]);
            self.fetch_drop_from_alias(field_value_id);
            if self.drop_record[field_value_id].is_dropped {
                self.push_drop_bottom_up(
                    field_value_id,
                    self.drop_record[field_value_id].drop_spot,
                );
                rap_debug!("{:?}", self.drop_record[value_idx]);
                break;
            }
            self.fetch_drop_from_bottom(field_value_id);
        }
    }

    pub fn fetch_drop_from_top(&mut self, value_idx: usize) {
        rap_debug!("fetch_drop_from_top: value_idx = {}", value_idx);
        let mut father = self.mop_graph.values[value_idx].father.clone();
        while let Some(father_info) = father {
            let father_idx = father_info.father_value_id;
            self.fetch_drop_from_alias(father_idx);
            if self.drop_record[father_idx].is_dropped {
                self.push_drop_top_down(father_idx, self.drop_record[father_idx].drop_spot);
                rap_debug!("{:?}", self.drop_record[value_idx]);
                break;
            }
            father = self.mop_graph.values[father_idx].father.clone();
        }
    }

    pub fn fetch_drop_from_alias(&mut self, value_idx: usize) {
        rap_debug!("fetch_drop_from_alias: value_idx = {}", value_idx);
        if let Some(aliases) = self.mop_graph.get_alias_set(value_idx) {
            for idx in aliases {
                // set idx as dropped if any of its alias has been dropped.
                if self.drop_record[idx].is_dropped {
                    self.drop_record[value_idx] = self.drop_record[idx].clone();
                    self.drop_record[value_idx].value_index = value_idx;
                    self.drop_record[value_idx].prop_chain.push(value_idx);
                }
            }
        }
    }
}
