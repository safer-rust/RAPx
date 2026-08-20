use crate::compat::FxHashMap;
use rustc_hir::{BodyId, HirId, Impl, ItemKind, TraitItemKind, intravisit::Visitor};
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

/// Maps `HirId` of a type to `BodyId` of related impls.
pub type FnMap = FxHashMap<Option<HirId>, Vec<(BodyId, Span)>>;

///This structs is used to collect all functions and implementations of structs and traits.
pub struct FnCollector<'tcx> {
    tcx: TyCtxt<'tcx>,
    fnmap: FnMap,
}

impl<'tcx> FnCollector<'tcx> {
    pub fn collect(tcx: TyCtxt<'tcx>) -> FnMap {
        let mut collector = FnCollector {
            tcx,
            fnmap: FnMap::default(),
        };
        tcx.hir_visit_all_item_likes_in_crate(&mut collector);
        collector.fnmap
    }
}

impl<'tcx> Visitor<'tcx> for FnCollector<'tcx> {
    fn visit_item(&mut self, item: &'tcx rustc_hir::Item<'tcx>) {
        match &item.kind {
            ItemKind::Impl(Impl {
                generics: _generics,
                self_ty,
                items: impl_items,
                ..
            }) => {
                let key = Some(self_ty.hir_id);
                let entry = self.fnmap.entry(key).or_default();
                entry.extend(impl_items.iter().filter_map(|impl_item_id| {
                    self.tcx
                        .hir_maybe_body_owned_by(impl_item_id.owner_id.def_id)
                        .map(|body| (body.id(), self.tcx.hir_impl_item(*impl_item_id).span))
                }));
            }
            #[cfg(not(rapx_ge_99))]
            ItemKind::Trait(
                _,
                _is_auto,
                _safety,
                _ident,
                _generics,
                _generic_bounds,
                trait_item_ids,
            ) => {
                let key = None;
                let entry = self.fnmap.entry(key).or_default();
                entry.extend(trait_item_ids.iter().filter_map(|trait_item_id| {
                    let trait_item = self.tcx.hir_trait_item(*trait_item_id);
                    if let TraitItemKind::Fn(_, _) = trait_item.kind {
                        self.tcx
                            .hir_maybe_body_owned_by(trait_item.owner_id.def_id)
                            .map(|body| (body.id(), trait_item.span))
                    } else {
                        None
                    }
                }));
            }
            #[cfg(rapx_ge_99)]
            ItemKind::Trait {
                is_auto: _is_auto,
                safety: _safety,
                ident: _ident,
                generics: _generics,
                bounds: _generic_bounds,
                items: trait_item_ids,
                impl_restriction: _,
                constness: _,
            } => {
                let key = None;
                let entry = self.fnmap.entry(key).or_default();
                entry.extend(trait_item_ids.iter().filter_map(|trait_item_id| {
                    let trait_item = self.tcx.hir_trait_item(*trait_item_id);
                    if let TraitItemKind::Fn(_, _) = trait_item.kind {
                        self.tcx
                            .hir_maybe_body_owned_by(trait_item.owner_id.def_id)
                            .map(|body| (body.id(), trait_item.span))
                    } else {
                        None
                    }
                }));
            }
            ItemKind::Fn {
                sig: _,
                generics: _,
                body: body_id,
                has_body: _,
                ident: _,
            } => {
                let key = Some(body_id.hir_id);
                let entry = self.fnmap.entry(key).or_default();
                entry.push((*body_id, item.span));
            }
            _ => (),
        }
    }

    fn visit_trait_item(&mut self, _trait_item: &'tcx rustc_hir::TraitItem<'tcx>) {
        // We don't process items inside trait blocks
    }

    fn visit_impl_item(&mut self, _impl_item: &'tcx rustc_hir::ImplItem<'tcx>) {
        // We don't process items inside impl blocks
    }

    fn visit_foreign_item(&mut self, _foreign_item: &'tcx rustc_hir::ForeignItem<'tcx>) {
        // We don't process foreign items
    }
}
