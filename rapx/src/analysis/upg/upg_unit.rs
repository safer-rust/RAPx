use crate::analysis::helpers::fn_info::*;
use rustc_hir::{Safety, def_id::DefId};
use rustc_middle::mir::Local;
use std::collections::HashSet;

#[derive(Debug, Clone)]
pub struct UPGUnit {
    pub caller: FnInfo,
    pub callees: HashSet<FnInfo>,
    pub raw_ptrs: HashSet<Local>,
    pub static_muts: HashSet<DefId>,
    pub caller_cons: HashSet<FnInfo>,
    pub mut_methods: Vec<DefId>,
}

/// Counts of different unit categories collected across all UPG units.
///
/// Fields are indexed as per the original comment:
///   [uf/um, sf-uf, sf-um, uf-uf, uf-um, um(sf)-uf, um(uf)-uf, um(sf)-um,
///    um(uf)-um, sm(sf)-uf, sm(uf)-uf, sm(sf)-um, sm(uf)-um]
#[derive(Debug, Clone, Default)]
pub struct BasicUnitCounts {
    /// uf/um — unsafe caller with no callees
    pub unsafe_fn_or_method_no_callees: u32,
    /// sf-uf — safe non-method caller calling unsafe non-method
    pub safe_fn_call_unsafe_fn: u32,
    /// sf-um — safe non-method caller calling unsafe method
    pub safe_fn_call_unsafe_method: u32,
    /// uf-uf — unsafe non-method caller calling unsafe non-method
    pub unsafe_fn_call_unsafe_fn: u32,
    /// uf-um — unsafe non-method caller calling unsafe method
    pub unsafe_fn_call_unsafe_method: u32,
    /// um(sf)-uf — unsafe method with safe cons calling unsafe non-method
    pub unsafe_method_safe_cons_call_unsafe_fn: u32,
    /// um(uf)-uf — unsafe method with unsafe cons calling unsafe non-method
    pub unsafe_method_unsafe_cons_call_unsafe_fn: u32,
    /// um(sf)-um — unsafe method with safe cons calling unsafe method
    pub unsafe_method_safe_cons_call_unsafe_method: u32,
    /// um(uf)-um — unsafe method with unsafe cons calling unsafe method
    pub unsafe_method_unsafe_cons_call_unsafe_method: u32,
    /// sm(sf)-uf — safe method with safe cons calling unsafe non-method
    pub safe_method_safe_cons_call_unsafe_fn: u32,
    /// sm(uf)-uf — safe method with unsafe cons calling unsafe non-method
    pub safe_method_unsafe_cons_call_unsafe_fn: u32,
    /// sm(sf)-um — safe method with safe cons calling unsafe method
    pub safe_method_safe_cons_call_unsafe_method: u32,
    /// sm(uf)-um — safe method with unsafe cons calling unsafe method
    pub safe_method_unsafe_cons_call_unsafe_method: u32,
}

impl BasicUnitCounts {
    pub fn as_slice_mut(&mut self) -> &mut [u32] {
        let ptr = self as *mut Self as *mut u32;
        unsafe { std::slice::from_raw_parts_mut(ptr, 13) }
    }
}

impl UPGUnit {
    pub fn new(
        caller: FnInfo,
        callees: HashSet<FnInfo>,
        raw_ptrs: HashSet<Local>,
        static_muts: HashSet<DefId>,
        caller_cons: HashSet<FnInfo>,
        mut_methods: Vec<DefId>,
    ) -> Self {
        Self {
            caller,
            callees,
            raw_ptrs,
            static_muts,
            caller_cons,
            mut_methods,
        }
    }

    pub fn count_basic_units(&self, counts: &mut BasicUnitCounts) {
        let data = counts.as_slice_mut();

        if self.caller.fn_safety == Safety::Unsafe && self.callees.is_empty() {
            data[0] += 1;
        }
        if self.caller.fn_safety == Safety::Safe && self.caller.fn_kind != FnKind::Method {
            for callee in &self.callees {
                if callee.fn_kind == FnKind::Method {
                    data[2] += 1;
                } else {
                    data[1] += 1;
                }
            }
        }
        if self.caller.fn_safety == Safety::Unsafe && self.caller.fn_kind != FnKind::Method {
            for callee in &self.callees {
                if callee.fn_kind == FnKind::Method {
                    data[4] += 1;
                } else {
                    data[3] += 1;
                }
            }
        }
        if self.caller.fn_safety == Safety::Unsafe && self.caller.fn_kind == FnKind::Method {
            let mut unsafe_cons = 0;
            let mut safe_cons = 0;
            for cons in &self.caller_cons {
                if cons.fn_safety == Safety::Unsafe {
                    unsafe_cons += 1;
                } else {
                    safe_cons += 1;
                }
            }
            if unsafe_cons == 0 && safe_cons == 0 {
                safe_cons = 1;
            }
            for callee in &self.callees {
                if callee.fn_kind == FnKind::Method {
                    data[7] += safe_cons;
                    data[8] += unsafe_cons;
                } else {
                    data[5] += safe_cons;
                    data[6] += unsafe_cons;
                }
            }
        }
        if self.caller.fn_safety == Safety::Safe && self.caller.fn_kind == FnKind::Method {
            let mut unsafe_cons = 0;
            let mut safe_cons = 0;
            for cons in &self.caller_cons {
                if cons.fn_safety == Safety::Unsafe {
                    unsafe_cons += 1;
                } else {
                    safe_cons += 1;
                }
            }
            if unsafe_cons == 0 && safe_cons == 0 {
                safe_cons = 1;
            }
            for callee in &self.callees {
                if callee.fn_kind == FnKind::Method {
                    data[11] += safe_cons;
                    data[12] += unsafe_cons;
                } else {
                    data[9] += safe_cons;
                    data[10] += unsafe_cons;
                }
            }
        }
    }
}
