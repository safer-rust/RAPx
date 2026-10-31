//! Known API and type `DefId`s, plus MIR availability.

pub(crate) mod intrinsic_api;
pub(crate) mod lang_api;
pub(crate) mod nomir_api;
pub(crate) mod nomir_ffi;
pub(crate) mod other_api;
pub(crate) mod type_ids;

use rustc_middle::ty::TyCtxt;

pub(crate) fn init(tcx: TyCtxt<'_>) {
    type_ids::init(tcx);
    other_api::init(tcx);
    intrinsic_api::init(tcx);
    nomir_api::init(tcx);
    nomir_ffi::init(tcx);
}
