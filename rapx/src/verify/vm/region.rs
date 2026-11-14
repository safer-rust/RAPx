//! Region (lifetime) helpers shared by the VM and the property checker.

use rustc_data_structures::{fx::FxHashSet, smallvec::SmallVec};
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_infer::infer::outlives::env::OutlivesEnvironment;
use rustc_middle::ty::{
    EarlyParamRegion, GenericParamDefKind, Region, RegionKind, Ty, TyCtxt, TyKind,
    outlives::{Component, push_outlives_components},
};

use crate::verify::contract::is_static_lifetime_ident;

/// Resolve a lifetime name from a contract (e.g. `"a"`, `"static"`) to a
/// concrete `Region`. `name` is the raw ident, without the leading `'`.
pub(crate) fn resolve_region_name<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    name: &str,
) -> Option<Region<'tcx>> {
    if is_static_lifetime_ident(name) {
        return Some(tcx.lifetimes.re_static);
    }
    let ticked = format!("'{name}");
    let generics = tcx.generics_of(def_id);
    for param in &generics.own_params {
        if matches!(param.kind, GenericParamDefKind::Lifetime)
            && param.name.as_str() == ticked.as_str()
        {
            return Some(Region::new_early_param(
                tcx,
                EarlyParamRegion {
                    index: param.index,
                    name: param.name,
                },
            ));
        }
    }
    None
}

/// Whether `src` outlives `ret` (`src: ret`).
///
/// `'static` and reflexivity are handled structurally; declared where-clauses
/// (`'a: 'b`) are resolved via rustc's `FreeRegionMap` (which also computes the
/// transitive closure). Anything else is treated as *not* outlives.
pub(crate) fn region_outlives<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    src: Region<'tcx>,
    ret: Region<'tcx>,
) -> bool {
    match (src.kind(), ret.kind()) {
        (RegionKind::ReStatic, _) => true,
        (_, RegionKind::ReStatic) => false,
        _ => {
            if src == ret {
                return true;
            }
            if !src.is_free() || !ret.is_free() {
                return false;
            }
            free_region_outlives(tcx, def_id, src, ret)
        }
    }
}

/// Consult the function's declared outlives constraints (where-clauses) via
/// rustc's `FreeRegionMap`, which records `'a: 'b` bounds and their transitive
/// closure. `sub_free_regions(r_a, r_b)` tests `r_a <= r_b` (i.e. `r_b: r_a`),
/// so `src: ret` is `sub_free_regions(ret, src)`.
fn free_region_outlives<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    src: Region<'tcx>,
    ret: Region<'tcx>,
) -> bool {
    let param_env = tcx.param_env(def_id);
    let env = OutlivesEnvironment::from_normalized_bounds(
        param_env,
        Vec::new(),
        std::iter::empty(),
        FxHashSet::default(),
    );
    env.free_region_map().sub_free_regions(tcx, ret, src)
}

/// Whether `src_region` provably outlives `demand` via the well-formedness of a
/// reference parameter `&'r Self<'a>`: the reference requires its pointee's
/// regions to outlive `'r` (`'a: 'r`), which the where-clause-only
/// [`region_outlives`] cannot see.  This holds when `demand` is exactly the
/// reference's own region `'r` and `src_region` is one of the pointee's outlives
/// components.
pub(crate) fn region_outlives_implied<'tcx>(
    tcx: TyCtxt<'tcx>,
    src_region: Region<'tcx>,
    self_ty: Ty<'tcx>,
    demand: Region<'tcx>,
) -> bool {
    let TyKind::Ref(ref_region, pointee, _) = self_ty.kind() else {
        return false;
    };
    if *ref_region != demand {
        return false;
    }
    let mut out: SmallVec<[Component<TyCtxt<'tcx>>; 4]> = SmallVec::new();
    push_outlives_components(tcx, *pointee, &mut out);
    out.iter()
        .any(|c| matches!(c, Component::Region(r) if *r == src_region))
}

/// The function's signature with late-bound regions liberated to free
/// `ReLateParam`s, so reference regions are comparable (MIR erases them to
/// `ReErased`).
fn liberate_fn_sig<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> Option<rustc_middle::ty::FnSig<'tcx>> {
    if !matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn) {
        return None;
    }
    let fn_sig = tcx.fn_sig(def_id).instantiate_identity();
    let fn_sig = fn_sig.skip_norm_wip();
    Some(tcx.liberate_late_bound_regions(def_id, fn_sig))
}

/// The reference region of `def_id`'s return type (`&'r T` → `Some('r)`).
pub(crate) fn fn_return_region<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> Option<Region<'tcx>> {
    match liberate_fn_sig(tcx, def_id)?.output().kind() {
        TyKind::Ref(region, _, _) => Some(*region),
        _ => None,
    }
}

/// The type of `def_id`'s argument at `index`.
pub(crate) fn fn_arg_ty<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, index: usize) -> Option<Ty<'tcx>> {
    liberate_fn_sig(tcx, def_id)?.inputs().get(index).copied()
}
