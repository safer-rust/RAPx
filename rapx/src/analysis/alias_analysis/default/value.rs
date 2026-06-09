use crate::analysis::alias_analysis::default::types::ValueKind;
use rustc_data_structures::fx::FxHashMap;

/// Represents a value node in the alias analysis graph.
/// Each value may correspond to local variables, or fields of structures temporarily crated in the alias analysis
#[derive(Debug, Clone)]
pub struct Value {
    /// A unique value index, which is the same as `local` if the number within the range of local
    /// variables; When encountering fields (e.g., 1.1), the index points to the unique field of the local.
    pub index: usize,
    /// Real local variable identifier in mir.
    pub local: usize,
    /// Indicates whether this value needs to be dropped at the end of its lifetime.
    pub need_drop: bool,
    /// Indicates whether this value may need to be dropped (uncertain drop semantics).
    pub may_drop: bool,
    /// The type of this value node (see `ValueKind`).
    pub kind: ValueKind,
    /// Information about this value’s parent, if it is a field of a parent node.
    pub father: Option<FatherInfo>,
    /// Mapping from field IDs to their value node IDs for field accesses.
    /// First field: field id; Second field: value id;
    pub fields: FxHashMap<usize, usize>,
}

/// Represents the relation between a field and its parent (father).
#[derive(Debug, Clone, PartialEq)]
pub struct FatherInfo {
    /// The value ID of the parent node.
    pub father_value_id: usize,
    /// The ID of the field within the parent.
    pub field_id: usize,
}

impl FatherInfo {
    /// Construct a new `FatherInfo` with the specified father value ID and field ID.
    pub fn new(father_value_id: usize, field_id: usize) -> Self {
        FatherInfo {
            father_value_id,
            field_id,
        }
    }
}

impl Value {
    /// Create a new value node with the provided properties.
    /// The `kind` defaults to `ValueKind::Adt` and `father` defaults to `None`.
    pub fn new(index: usize, local: usize, need_drop: bool, may_drop: bool) -> Self {
        Value {
            index,
            local,
            need_drop,
            may_drop,
            kind: ValueKind::Adt,
            father: None,
            fields: FxHashMap::default(),
        }
    }

    /// Returns whether this value is a tuple type.
    pub fn is_tuple(&self) -> bool {
        self.kind == ValueKind::Tuple
    }

    /// Returns whether this value is a pointer (raw pointer or reference).
    pub fn is_ptr(&self) -> bool {
        self.kind == ValueKind::RawPtr || self.kind == ValueKind::Ref
    }

    /// Returns whether this value is a reference type.
    pub fn is_ref(&self) -> bool {
        self.kind == ValueKind::Ref
    }

    /// Returns whether this value is of a corner case type as defined in `ValueKind`.
    pub fn is_ref_count(&self) -> bool {
        self.kind == ValueKind::SpecialPtr
    }
}
