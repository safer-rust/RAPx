use crate::compat::FxHashMap;
use rustc_hir::{
    Block, BlockCheckMode, Body, BodyId, ExprKind, ImplItemKind, QPath, def_id::DefId, intravisit,
    intravisit::Visitor,
};
use rustc_middle::ty::{self, Ty, TyCtxt};
use std::collections::HashSet;

pub struct ContainsUnsafe<'tcx> {
    tcx: TyCtxt<'tcx>,
    fn_unsafe: bool,
    block_unsafe: bool,
}

impl<'tcx> ContainsUnsafe<'tcx> {
    pub fn contains_unsafe(tcx: TyCtxt<'tcx>, body_id: BodyId) -> (bool, bool) {
        let mut visitor = ContainsUnsafe {
            tcx,
            fn_unsafe: false,
            block_unsafe: false,
        };

        let body = visitor.tcx.hir_body(body_id);
        visitor.fn_unsafety(body);
        visitor.visit_body(body);

        (visitor.fn_unsafe, visitor.block_unsafe)
    }

    /*
     * Check if the body corresponds to a function;
     * If yes, check the function safety declaration based on its signature.
     */
    fn fn_unsafety(&mut self, body: &'tcx Body<'tcx>) {
        let did = body.value.hir_id.owner.to_def_id();
        if self.tcx.def_kind(did) == rustc_hir::def::DefKind::Fn
            || self.tcx.def_kind(did) == rustc_hir::def::DefKind::AssocFn
        {
            let sig = self.tcx.fn_sig(did);
            if let rustc_hir::Safety::Unsafe = sig.skip_binder().safety() {
                self.fn_unsafe = true;
            }
        }
    }
}

/*
 * Check if each block contains unsafe marker.
 */
impl<'tcx> Visitor<'tcx> for ContainsUnsafe<'tcx> {
    fn visit_block(&mut self, block: &'tcx Block<'tcx>) {
        if let BlockCheckMode::UnsafeBlock(_unsafe_source) = block.rules {
            self.block_unsafe = true;
        }
        intravisit::walk_block(self, block);
    }
}

pub struct ContainsLit {
    pub structs_used: HashSet<String>,
}

impl<'tcx> Visitor<'tcx> for ContainsLit {
    fn visit_expr(&mut self, expr: &'tcx rustc_hir::Expr<'tcx>) {
        if let ExprKind::Struct(ref qpath, _, _) = expr.kind
            && let QPath::Resolved(_, path) = qpath
                && let Some(ident) = path.segments.last().map(|segment| segment.ident) {
                    self.structs_used.insert(ident.to_string());
                }
        intravisit::walk_expr(self, expr);
    }
}

/// (`DefId` of ADT) => Vec<(HirId of relevant impl block, impl_self_ty)>
/// We use this map to quickly access associated impl blocks per ADT.
/// `impl_self_ty` in the return value may differ from `tcx.type_of(ADT.DefID)`,
/// as different instantiations of the same ADT are distinct `Ty`s.
/// (e.g. Foo<i32, i64>, Foo<String, i32>)
pub type AdtImplMap<'tcx> = FxHashMap<DefId, Vec<(DefId, Ty<'tcx>)>>;

/// Create & initialize `AdtImplMap`.
/// `AdtImplMap` is initialized before analysis of each crate,
/// avoiding quadratic complexity of scanning all impl blocks for each ADT.
pub fn create_adt_impl_map(tcx: TyCtxt<'_>) -> AdtImplMap<'_> {
    let mut map = FxHashMap::default();
    for impl_item_id in tcx.hir_crate_items(()).impl_items() {
        let impl_item = tcx.hir_impl_item(impl_item_id);
        if let ImplItemKind::Type(ty) = impl_item.kind {
            let impl_self_ty = tcx.type_of(ty.hir_id.owner).skip_binder();
            if let ty::Adt(impl_self_adt_def, _impl_substs) = impl_self_ty.kind() {
                map.entry(impl_self_adt_def.did())
                    .or_insert_with(Vec::new)
                    .push((impl_item_id.owner_id.to_def_id(), impl_self_ty));
            }
        }
    }
    map
}
