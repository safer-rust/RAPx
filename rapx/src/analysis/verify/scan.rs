use crate::{rap_info, analysis::Analysis};
use rustc_hir::{
    BodyId, FnDecl,
    def_id::{DefId, LocalDefId},
    intravisit::{FnKind, Visitor, walk_fn},
};
use rustc_middle::{
    hir::nested_filter,
    ty::TyCtxt,
};
use rustc_span::Span;

/// Visitor that collects all functions annotated with `#[rapx::verify]`.
pub struct VerifyAttrVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    pub verify_fns: Vec<DefId>,
}

impl<'tcx> VerifyAttrVisitor<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        VerifyAttrVisitor {
            tcx,
            verify_fns: Vec::new(),
        }
    }

    fn has_rapx_verify_attr(&self, def_id: LocalDefId) -> bool {
        let attrs = self.tcx.get_attrs_unchecked(def_id.to_def_id());
        for attr in attrs {
            if let Some(ident) = attr.ident() {
                // handle flat #[rapx::verify] represented as a single path
            }
            // Check for path-style attribute: #[rapx::verify]
            if attr.is_doc_comment() {
                continue;
            }
            let segments = attr.path_matches(&[rustc_span::sym::dummy; 0][..]);
            // Use the meta path directly
            let path = attr.get_normal_item();
            let segs: Vec<&str> = path.path.segments.iter()
                .map(|s| s.ident.as_str())
                .collect();
            if segs == ["rapx", "verify"] {
                return true;
            }
        }
        false
    }
}

impl<'tcx> Visitor<'tcx> for VerifyAttrVisitor<'tcx> {
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
        if self.has_rapx_verify_attr(id) {
            let def_id = id.to_def_id();
            let path = self.tcx.def_path_str(def_id);
            rap_info!("[rapx::verify] found: {} (DefId: {:?})", path, def_id);
            self.verify_fns.push(def_id);
        }
        walk_fn(self, fk, fd, b, id);
    }
}

/// Scan Analysis - find all functions annotated with #[rapx::verify]
pub struct VerifyScanAnalysis<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> Analysis for VerifyScanAnalysis<'tcx> {
    fn name(&self) -> &'static str {
        "Verify Scan Analysis"
    }

    fn run(&mut self) {
        rap_info!("======== #[rapx::verify] scan ========");
        let mut visitor = VerifyAttrVisitor::new(self.tcx);
        self.tcx.hir_visit_all_item_likes_in_crate(&mut visitor);
        rap_info!("total: {} function(s) annotated with #[rapx::verify]", visitor.verify_fns.len());
        rap_info!("=====================================");
    }

    fn reset(&mut self) {}
}

impl<'tcx> VerifyScanAnalysis<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        VerifyScanAnalysis { tcx }
    }
}
