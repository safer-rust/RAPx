//! Known API and type identities.
//!
//! # Agent Rules
//!
//! Keep this module limited to identity submodules and shared identity helpers.
//! Do not depend on other RAPx modules.

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

pub(crate) mod diagnostic_api;
pub(crate) mod intrinsic_api;
pub(crate) mod lang_api;
pub(crate) mod nomir_api;
pub(crate) mod other_api;
pub(crate) mod type_ids;

fn is_std_api(tcx: TyCtxt<'_>, did: DefId) -> bool {
    matches!(tcx.crate_name(did.krate).as_str(), "core" | "alloc" | "std")
}
