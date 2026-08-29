pub mod default;

use rustc_middle::ty::{Ty, TyKind};
use rustc_span::def_id::DefId;

use std::{
    collections::{HashMap, HashSet},
    env,
    fmt::{self, Display},
};

use crate::{Analysis, utils::source::get_fn_name_byid};

#[repr(u8)]
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum HeapOwnership {
    False = 0,
    True = 1,
    Unknown = 2,
}

impl Default for HeapOwnership {
    fn default() -> Self {
        Self::Unknown
    }
}

impl HeapOwnership {
    pub fn is_onheap(&self) -> bool {
        match self {
            HeapOwnership::True => true,
            _ => false,
        }
    }
}

impl Display for HeapOwnership {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let name = match self {
            HeapOwnership::False => "0",
            HeapOwnership::True => "1",
            HeapOwnership::Unknown => "2",
        };
        write!(f, "{}", name)
    }
}

/// This is the type for storing the heap analysis results.
/// The result is represented as a hashmap, where the key is `DefId` and the value contains the
/// information of whether the type contains data on heap.
/// Since a type could be a enumerate type, the value is represented as a vec, indicating the heap
/// information of each variant.
/// Also, because it may contain type parameters or generic types,
/// the heap information is a tuple containing the information of each type parameter.
pub type HeapOwnershipResultMap = HashMap<DefId, Vec<(HeapOwnership, Vec<bool>)>>;
pub struct HeapOwnershipResultMapWrapper(pub HashMap<DefId, Vec<(HeapOwnership, Vec<bool>)>>);

impl Display for HeapOwnershipResultMapWrapper {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "=== Print heap ownership analysis results ===")?;
        for (def_id, units) in &self.0 {
            let fn_name = get_fn_name_byid(def_id);
            let owning = units
                .iter()
                .map(Self::format_heap_unit)
                .collect::<Vec<_>>()
                .join(", ");
            writeln!(f, "Type: {:?}: {}", fn_name, owning)?;
        }
        Ok(())
    }
}

impl HeapOwnershipResultMapWrapper {
    fn format_heap_unit((heap, bits): &(HeapOwnership, Vec<bool>)) -> String {
        let bit_str = bits
            .iter()
            .map(|b| if *b { "1" } else { "0" })
            .collect::<Vec<_>>()
            .join(",");
        format!("{:?}, <{}>", heap, bit_str)
    }
}
/// This trait provides features for owned heap analysis, which is used to determine if a type owns
/// memory on heap. Owned heap should be automatically released by default.
pub trait HeapOwnershipAnalysis: Analysis {
    /// The function returns the result of owned heap analysis for all types.
    fn get_all_items(&self) -> HeapOwnershipResultMap;

    /// If a type is a heap owner, the function returns Result<true>. If the specified type is
    /// illegal, the function returns Err.
    fn is_heapowner<'tcx>(hares: HeapOwnershipResultMap, ty: Ty<'tcx>) -> Result<bool, &'static str> {
        match ty.kind() {
            TyKind::Adt(adtdef, ..) => {
                let heapinfo = hares.get(&adtdef.0.0.did).unwrap();
                for item in heapinfo {
                    if item.0 == HeapOwnership::True {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            _ => Err("The input is not an ADT"),
        }
    }

    /// A type might be a heap owner if it is not a heap owner directly but contains type
    /// parameters that may make the type become a heap owner after monomorphization.
    fn maybe_heapowner<'tcx>(hares: HeapOwnershipResultMap, ty: Ty<'tcx>) -> Result<bool, &'static str> {
        match ty.kind() {
            TyKind::Adt(adtdef, ..) => {
                let heapinfo = hares.get(&adtdef.0.0.did).unwrap();
                for item in heapinfo {
                    if item.0 == HeapOwnership::False && item.1.contains(&true) {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            _ => Err("The input is not an ADT"),
        }
    }
}
