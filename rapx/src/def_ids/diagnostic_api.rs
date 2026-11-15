//! Standard-library API identities registered as rustc diagnostic items.

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use rustc_span::Symbol;

/// Whether `did` is `mem::size_of` or `mem::align_of`.
pub fn is_mem_size_or_align_of(tcx: TyCtxt<'_>, did: DefId) -> bool {
    tcx.is_diagnostic_item(Symbol::intern("mem_size_of"), did)
        || tcx.is_diagnostic_item(Symbol::intern("mem_align_of"), did)
}

pub fn is_ptr_read(tcx: TyCtxt<'_>, did: DefId) -> bool {
    tcx.get_diagnostic_name(did).is_some_and(|name| {
        matches!(name.as_str(), "ptr_read" | "ptr_read_unaligned" | "ptr_read_volatile")
    })
}

pub fn is_ptr_write(tcx: TyCtxt<'_>, did: DefId) -> bool {
    tcx.get_diagnostic_name(did).is_some_and(|name| {
        matches!(name.as_str(), "ptr_write" | "ptr_write_unaligned" | "ptr_write_volatile" | "ptr_write_bytes")
    })
}

pub fn is_ptr_write_to_uninit(tcx: TyCtxt<'_>, did: DefId) -> bool {
    tcx.get_diagnostic_name(did)
        .is_some_and(|name| matches!(name.as_str(), "ptr_write" | "ptr_write_bytes"))
}

pub fn is_ptr_copy(tcx: TyCtxt<'_>, did: DefId) -> bool {
    tcx.get_diagnostic_name(did)
        .is_some_and(|name| matches!(name.as_str(), "ptr_copy" | "ptr_copy_nonoverlapping"))
}

pub fn is_drop(tcx: TyCtxt<'_>, did: DefId) -> bool {
    tcx.is_diagnostic_item(Symbol::intern("mem_drop"), did)
}

pub fn is_drop_in_place(tcx: TyCtxt<'_>, did: DefId) -> bool {
    tcx.is_diagnostic_item(Symbol::intern("ptr_drop_in_place"), did)
}
