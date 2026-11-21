use crate::util::fn_info::*;
use rustc_hir::{Safety, def_id::DefId};
use rustc_middle::mir::Local;
use std::collections::HashSet;

#[derive(Debug, Clone)]
pub struct SafetyFlowUnit {
    pub caller: FnInfo,
    pub callees: HashSet<FnInfo>,
    pub raw_ptrs: HashSet<Local>,
    pub static_muts: HashSet<DefId>,
    pub caller_cons: HashSet<FnInfo>,
    pub mut_methods: HashSet<DefId>,
}

/// Counts of different unit categories collected across all SafetyFlow units.
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
    pub fn total(&self) -> u32 {
        self.unsafe_fn_or_method_no_callees
            + self.safe_fn_call_unsafe_fn
            + self.safe_fn_call_unsafe_method
            + self.unsafe_fn_call_unsafe_fn
            + self.unsafe_fn_call_unsafe_method
            + self.unsafe_method_safe_cons_call_unsafe_fn
            + self.unsafe_method_unsafe_cons_call_unsafe_fn
            + self.unsafe_method_safe_cons_call_unsafe_method
            + self.unsafe_method_unsafe_cons_call_unsafe_method
            + self.safe_method_safe_cons_call_unsafe_fn
            + self.safe_method_unsafe_cons_call_unsafe_fn
            + self.safe_method_safe_cons_call_unsafe_method
            + self.safe_method_unsafe_cons_call_unsafe_method
    }
}

impl SafetyFlowUnit {
    pub fn new(
        caller: FnInfo,
        callees: HashSet<FnInfo>,
        raw_ptrs: HashSet<Local>,
        static_muts: HashSet<DefId>,
        caller_cons: HashSet<FnInfo>,
        mut_methods: HashSet<DefId>,
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

    pub fn count_basic_units(&self, c: &mut BasicUnitCounts) {
        if self.caller.fn_safety == Safety::Unsafe && self.callees.is_empty() {
            c.unsafe_fn_or_method_no_callees += 1;
        }
        if self.caller.fn_safety == Safety::Safe && self.caller.fn_kind != FnKind::Method {
            for callee in &self.callees {
                if callee.fn_kind == FnKind::Method {
                    c.safe_fn_call_unsafe_method += 1;
                } else {
                    c.safe_fn_call_unsafe_fn += 1;
                }
            }
        }
        if self.caller.fn_safety == Safety::Unsafe && self.caller.fn_kind != FnKind::Method {
            for callee in &self.callees {
                if callee.fn_kind == FnKind::Method {
                    c.unsafe_fn_call_unsafe_method += 1;
                } else {
                    c.unsafe_fn_call_unsafe_fn += 1;
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
                    c.unsafe_method_safe_cons_call_unsafe_method += safe_cons;
                    c.unsafe_method_unsafe_cons_call_unsafe_method += unsafe_cons;
                } else {
                    c.unsafe_method_safe_cons_call_unsafe_fn += safe_cons;
                    c.unsafe_method_unsafe_cons_call_unsafe_fn += unsafe_cons;
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
                    c.safe_method_safe_cons_call_unsafe_method += safe_cons;
                    c.safe_method_unsafe_cons_call_unsafe_method += unsafe_cons;
                } else {
                    c.safe_method_safe_cons_call_unsafe_fn += safe_cons;
                    c.safe_method_unsafe_cons_call_unsafe_fn += unsafe_cons;
                }
            }
        }
    }
}
