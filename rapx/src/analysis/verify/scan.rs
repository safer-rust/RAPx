use crate::analysis::Analysis;
use crate::analysis::utils::fn_info::get_unsafe_callees;
use rustc_hir::{
    BodyId, FnDecl,
    def_id::{DefId, LocalDefId},
    intravisit::{FnKind, Visitor, walk_fn},
};
use rustc_middle::{hir::nested_filter, ty::TyCtxt};
use rustc_span::{Span, Symbol};
use std::collections::{HashMap, HashSet};

/// Visitor that collects all functions annotated with `#[rapx::verify]`.
pub struct VerifyAttrVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    pub verify_fns: Vec<DefId>,
    pub verify_unsafe_callees: HashMap<DefId, HashSet<DefId>>,
}

impl<'tcx> VerifyAttrVisitor<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        VerifyAttrVisitor {
            tcx,
            verify_fns: Vec::new(),
            verify_unsafe_callees: HashMap::new(),
        }
    }

    fn has_rapx_verify_attr(&self, def_id: LocalDefId) -> bool {
        let hir_id = self.tcx.local_def_id_to_hir_id(def_id);

        let rapx = Symbol::intern("rapx");
        let verify = Symbol::intern("verify");

        let attrs = self.tcx.hir_attrs(hir_id);

        attrs.iter().any(|attr| {
            if attr.is_doc_comment().is_some() {
                return false;
            }

            let path = attr.path(); // SmallVec<Symbol>

            path.len() == 2 && path[0] == rapx && path[1] == verify
        })
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
        _span: Span,
        id: LocalDefId,
    ) -> Self::Result {
        if self.has_rapx_verify_attr(id) {
            let def_id = id.to_def_id();
            let path = self.tcx.def_path_str(def_id);
            let unsafe_callees = get_unsafe_callees(self.tcx, def_id);
            rap_info!("[rapx::verify] found: {} (DefId: {:?})", path, def_id);
            rap_debug!(
                "[rapx::verify] unsafe callees of {:?}: {:?}",
                def_id,
                unsafe_callees
            );
            self.verify_unsafe_callees.insert(def_id, unsafe_callees);
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
        rap_debug!(
            "[rapx::verify] target -> unsafe_callees: {:?}",
            visitor.verify_unsafe_callees
        );
        rap_info!(
            "total: {} function(s) annotated with #[rapx::verify]",
            visitor.verify_fns.len()
        );
        rap_info!("=====================================");
    }

    fn reset(&mut self) {}
}

impl<'tcx> VerifyScanAnalysis<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        VerifyScanAnalysis { tcx }
    }
}
