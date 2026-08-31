use crate::compat::FxHashMap;

#[derive(Debug, Clone)]
pub struct Value {
    pub index: usize,
    pub local: usize,
    pub father: Option<FatherInfo>,
    pub fields: FxHashMap<usize, usize>,
    pub slot_idx: Option<usize>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FatherInfo {
    pub father_value_id: usize,
    pub field_id: usize,
}

impl FatherInfo {
    pub fn new(father_value_id: usize, field_id: usize) -> Self {
        FatherInfo {
            father_value_id,
            field_id,
        }
    }
}

impl Value {
    pub fn new(index: usize, local: usize) -> Self {
        Value {
            index,
            local,
            father: None,
            fields: FxHashMap::default(),
            slot_idx: None,
        }
    }
}
