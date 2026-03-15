use super::statistic::Statistics;
use crate::{rap_debug, rap_info, rap_trace};
use rustc_hir::{
    BodyId, BodyOwnerKind, FnDecl,
    def_id::{DefId, LocalDefId},
    intravisit::{FnKind, Visitor, walk_block, walk_fn},
};
use rustc_middle::{
    hir::nested_filter,
    ty::{self, FnSig, ParamEnv, Ty, TyCtxt, TyKind},
};
use rustc_span::Span;
use std::io::Write;

pub struct FnVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    stats: Statistics<'tcx>,
}

fn is_api_public(fn_def_id: impl Into<DefId>, tcx: TyCtxt<'_>) -> bool {
    let fn_def_id: DefId = fn_def_id.into();
    let local_id = fn_def_id.expect_local();
    rap_trace!(
        "vis: {:?} (path: {}) => {:?}",
        fn_def_id,
        tcx.def_path_str(fn_def_id),
        tcx.effective_visibilities(()).effective_vis(local_id)
    );
    tcx.effective_visibilities(()).is_directly_public(local_id)
        || tcx.effective_visibilities(()).is_exported(local_id)
}

impl<'tcx> FnVisitor<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> FnVisitor<'tcx> {
        FnVisitor {
            tcx,
            stats: Statistics::default(),
        }
    }
    pub fn statistic(self) -> Statistics<'tcx> {
        self.stats
    }
    fn work_at_fn<'v>(
        &mut self,
        fk: FnKind<'v>,
        fd: &'v FnDecl<'v>,
        b: BodyId,
        span: Span,
        id: LocalDefId,
    ) {
        let fn_did = id.to_def_id();
        rap_debug!("API path: {}", self.tcx.def_path_str(fn_did));
        rap_debug!(
            "fn_sig: {}",
            self.tcx.type_of(fn_did).instantiate_identity()
        );
        rap_debug!(
            "visibility: {:?}",
            self.tcx
                .effective_visibilities(())
                .effective_vis(fn_did.as_local().unwrap())
                .unwrap()
        );

        if !is_api_public(fn_did, self.tcx) {
            rap_debug!("skip for not public API");
            return;
        }

        let is_generic = self
            .tcx
            .generics_of(fn_did)
            .requires_monomorphization(self.tcx);
        let fn_sig = self.tcx.fn_sig(fn_did);
        rap_debug!("fn_sig: {}", fn_sig.instantiate_identity());
        for input in fn_sig.instantiate_identity().inputs_and_output().iter() {
            rap_debug!("param: {:?}", input);
            let input_ty = input.skip_binder();
            if let TyKind::Ref(r, ty, _) = input.skip_binder().kind() {
                rap_debug!("region kind: {:?} {:?}", r.type_flags(), r.kind());
                match r.kind() {
                    ty::ReEarlyParam(re) => {
                        rap_debug!("ReEarlyParam: {:?}", re);
                    }
                    ty::ReBound(idx, bound) => {
                        rap_debug!("ReBound: {:?} {:?}", idx, bound);
                    }
                    _ => {}
                }
            }
        }

        rap_debug!("type(debug): {:?}", self.tcx.type_of(fn_did));
        rap_debug!("fn_sig(debug): {:?}", fn_sig);
        let late_fn_sig = self
            .tcx
            .liberate_late_bound_regions(fn_did, fn_sig.instantiate_identity());
        rap_debug!("late_fn_sig: {:?}", late_fn_sig);

        if is_generic {
            self.stats.pub_generic_api.insert(fn_did);
        } else {
            self.stats.pub_non_generic_api.insert(fn_did);
        }

        if fk.header().map_or(false, |header| header.is_unsafe()) {
            self.stats.pub_unsafe_api.insert(fn_did);
        }
    }
}

impl<'tcx> Visitor<'tcx> for FnVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_fn(
        &mut self,
        fk: FnKind<'tcx>,
        fd: &'tcx FnDecl<'tcx>,
        b: BodyId,
        span: Span,
        id: LocalDefId,
    ) -> Self::Result {
        self.work_at_fn(fk, fd, b, span, id);
        walk_fn(self, fk, fd, b, id);
    }

    fn visit_block(&mut self, b: &'tcx rustc_hir::Block<'tcx>) -> Self::Result {
        let r = b.rules;
        if matches!(r, rustc_hir::BlockCheckMode::UnsafeBlock(_)) {
            self.stats.unsafe_block.push(*b)
        }
        walk_block(self, b);
    }
}
