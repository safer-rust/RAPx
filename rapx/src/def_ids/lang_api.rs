//! Identity checks for compiler lang items used by the verifier.

#[cfg(rapx_has_attr_ir)]
pub(crate) use rustc_attr_ir::LangItem;
#[cfg(all(not(rapx_has_attr_ir), not(rapx_ge_100)))]
pub(crate) use rustc_hir::LangItem;
#[cfg(all(not(rapx_has_attr_ir), rapx_ge_100))]
pub(crate) use rustc_hir::attrs::lang_items::LangItem;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

/// Match a compiler-provided lang item by its `DefId`.
pub(crate) fn matches(tcx: TyCtxt<'_>, def_id: DefId, item: LangItem) -> bool {
    tcx.is_lang_item(def_id, item)
}

/// Whether this is one of the three callable traits.
pub(crate) fn is_fn_trait(tcx: TyCtxt<'_>, trait_id: DefId) -> bool {
    matches(tcx, trait_id, LangItem::Fn)
        || matches(tcx, trait_id, LangItem::FnMut)
        || matches(tcx, trait_id, LangItem::FnOnce)
}

fn is_trait_method(tcx: TyCtxt<'_>, did: DefId, trait_item: LangItem, name: &str) -> bool {
    tcx.opt_associated_item(did)
        .and_then(|item| item.trait_container(tcx))
        .is_some_and(|trait_id| matches(tcx, trait_id, trait_item))
        && tcx.item_name(did).as_str() == name
}

pub(crate) fn is_call_mut(tcx: TyCtxt<'_>, did: DefId) -> bool {
    is_trait_method(tcx, did, LangItem::FnMut, "call_mut")
}

pub(crate) fn is_clone(tcx: TyCtxt<'_>, did: DefId) -> bool {
    is_trait_method(tcx, did, LangItem::Clone, "clone")
}

/// The plain `panic!` entry point, which only consumes a static message.
pub(crate) fn is_panic_exit(tcx: TyCtxt<'_>, callee: DefId) -> bool {
    matches(tcx, callee, LangItem::Panic)
}

/// Panic lang items used as diverging exits in MIR.
pub(crate) fn is_panic_family(tcx: TyCtxt<'_>, callee: DefId) -> bool {
    is_panic_exit(tcx, callee)
        || matches(tcx, callee, LangItem::PanicNounwind)
        || matches(tcx, callee, LangItem::PanicFmt)
        || matches(tcx, callee, LangItem::PanicDisplay)
        || matches(tcx, callee, LangItem::ConstPanicFmt)
        || matches(tcx, callee, LangItem::PanicBoundsCheck)
        || matches(tcx, callee, LangItem::PanicMisalignedPointerDereference)
}
