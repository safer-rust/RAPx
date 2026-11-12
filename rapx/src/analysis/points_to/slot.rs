/// Identifies a memory slot: a local variable with optional field projections.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Slot {
    pub local: usize,
    pub fields: Vec<usize>,
}

/// Reserved projection index for the value behind a pointer.
pub const DEREF_PROJECTION: usize = usize::MAX;

impl Slot {
    pub fn new(local: usize) -> Self {
        Slot {
            local,
            fields: Vec::new(),
        }
    }

    pub fn project(&self, field_idx: usize) -> Self {
        let mut fields = self.fields.clone();
        fields.push(field_idx);
        Slot {
            local: self.local,
            fields,
        }
    }

    pub fn from_mir_place(place: &rustc_middle::mir::Place) -> Self {
        let local = place.local.as_usize();
        let fields: Vec<usize> = place
            .projection
            .iter()
            .filter_map(|elem| match elem {
                rustc_middle::mir::ProjectionElem::Field(idx, _) => Some(idx.as_usize()),
                _ => None,
            })
            .collect();
        Slot { local, fields }
    }

    pub fn from_mir_place_with_deref(place: &rustc_middle::mir::Place) -> Self {
        let fields = place
            .projection
            .iter()
            .filter_map(|elem| match elem {
                rustc_middle::mir::ProjectionElem::Field(idx, _) => Some(idx.as_usize()),
                rustc_middle::mir::ProjectionElem::Deref => Some(DEREF_PROJECTION),
                _ => None,
            })
            .collect();
        Slot {
            local: place.local.as_usize(),
            fields,
        }
    }
}

/// An abstract memory location a pointer can point to.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum AbstractLoc {
    Slot(Slot),
    Null,
}
