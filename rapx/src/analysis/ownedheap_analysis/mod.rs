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
pub enum OwnedHeap {
    False = 0,
    True = 1,
    Unknown = 2,
}

impl Default for OwnedHeap {
    fn default() -> Self {
        Self::Unknown
    }
}

impl OwnedHeap {
    pub fn is_onheap(&self) -> bool {
        match self {
            OwnedHeap::True => true,
            _ => false,
        }
    }
}

impl Display for OwnedHeap {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let name = match self {
            OwnedHeap::False => "0",
            OwnedHeap::True => "1",
            OwnedHeap::Unknown => "2",
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
pub type OHAResultMap = HashMap<DefId, Vec<(OwnedHeap, Vec<bool>)>>;
pub struct OHAResultMapWrapper(pub HashMap<DefId, Vec<(OwnedHeap, Vec<bool>)>>);

impl Display for OHAResultMapWrapper {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "=== Print owned heap analysis resuts ===")?;
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

impl OHAResultMapWrapper {
    fn format_heap_unit((heap, bits): &(OwnedHeap, Vec<bool>)) -> String {
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
pub trait OwnedHeapAnalysis: Analysis {
    /// The function returns the result of owned heap analysis for all types.
    fn get_all_items(&self) -> OHAResultMap;

    /// If a type is a heap owner, the function returns Result<true>. If the specified type is
    /// illegal, the function returns Err.
    fn is_heapowner<'tcx>(hares: OHAResultMap, ty: Ty<'tcx>) -> Result<bool, &'static str> {
        match ty.kind() {
            TyKind::Adt(adtdef, ..) => {
                let heapinfo = hares.get(&adtdef.0.0.did).unwrap();
                for item in heapinfo {
                    if item.0 == OwnedHeap::True {
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
    fn maybe_heapowner<'tcx>(hares: OHAResultMap, ty: Ty<'tcx>) -> Result<bool, &'static str> {
        match ty.kind() {
            TyKind::Adt(adtdef, ..) => {
                let heapinfo = hares.get(&adtdef.0.0.did).unwrap();
                for item in heapinfo {
                    if item.0 == OwnedHeap::False && item.1.contains(&true) {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            _ => Err("The input is not an ADT"),
        }
    }
}
