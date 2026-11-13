//! Identity of compiler intrinsics by `DefId`.

use std::collections::HashMap;
use std::sync::OnceLock;

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use rustc_public::{CrateDef, rustc_internal};
use rustc_span::Symbol;

static IDS: OnceLock<HashMap<DefId, Symbol>> = OnceLock::new();

pub fn init(tcx: TyCtxt<'_>) {
    IDS.get_or_init(|| {
        let mut ids = HashMap::new();
        for krate in std::iter::once(rustc_public::local_crate())
            .chain(rustc_public::external_crates())
            .filter(|krate| matches!(krate.name.as_str(), "core" | "std" | "alloc"))
        {
            for function in krate.fn_defs() {
                let id = rustc_internal::internal(tcx, function.def_id());
                if let Some(intrinsic) = tcx.intrinsic(id) {
                    ids.insert(id, intrinsic.name);
                }
            }
        }
        ids
    });
}

pub(crate) fn intrinsic_name(callee: Option<DefId>) -> Option<Symbol> {
    IDS.get()
        .expect("Intrinsic IDs have not been initialized")
        .get(&callee?)
        .copied()
}

pub fn is_intrinsic(tcx: TyCtxt<'_>, callee: DefId) -> bool {
    tcx.intrinsic(callee).is_some()
}
