//! Compiler lang-item identities used across RAPx.
//!
//! # Agent Rules
//!
//! Keep this module limited to identifying rustc lang items and their trait
//! methods by `DefId`. Do not depend on other RAPx modules.

pub(crate) use rustc_attr_ir::LangItem;
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

/// Whether `did` is the `FnMut::call_mut` trait method.
pub(crate) fn is_call_mut(tcx: TyCtxt<'_>, did: DefId) -> bool {
    tcx.opt_associated_item(did)
        .and_then(|item| item.trait_container(tcx))
        .is_some_and(|trait_id| matches(tcx, trait_id, LangItem::FnMut))
        && tcx.item_name(did).as_str() == "call_mut"
}

/// Whether `did` is a method of the `Clone` trait.
pub(crate) fn is_clone(tcx: TyCtxt<'_>, did: DefId) -> bool {
    tcx.opt_associated_item(did)
        .and_then(|item| item.trait_container(tcx))
        .is_some_and(|trait_id| matches(tcx, trait_id, LangItem::Clone))
}

/// Whether `did` is the `FromResidual::from_residual` trait or impl method.
pub(crate) fn is_from_residual(tcx: TyCtxt<'_>, did: DefId) -> bool {
    matches(tcx, did, LangItem::TryTraitFromResidual)
        || tcx.opt_associated_item(did)
            .and_then(|item| item.trait_item_def_id())
            .is_some_and(|trait_method| matches(tcx, trait_method, LangItem::TryTraitFromResidual))
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
