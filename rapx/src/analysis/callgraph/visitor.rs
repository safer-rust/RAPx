use super::default::CallGraph;
use crate::helpers::mir_utils::{dep_callee_def_id, instance_def_id, resolve_callee_instance};
use rustc_hir::def_id::DefId;
use rustc_middle::{mir, ty::TyCtxt};

pub struct CallGraphVisitor<'b, 'tcx> {
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    body: &'tcx mir::Body<'tcx>,
    call_graph_info: &'b mut CallGraph<'tcx>,
}

impl<'b, 'tcx> CallGraphVisitor<'b, 'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        body: &'tcx mir::Body<'tcx>,
        call_graph_info: &'b mut CallGraph<'tcx>,
    ) -> Self {
        Self {
            tcx,
            def_id,
            body,
            call_graph_info,
        }
    }

    fn add_fn_call(&mut self, callee_def_id: DefId, terminator: &'tcx mir::Terminator<'tcx>) {
        self.call_graph_info.register_fn(callee_def_id);
        self.call_graph_info.add_function_call(
            self.def_id,
            callee_def_id,
            Some(terminator),
        );
    }

    fn handle_fn_call(
        &mut self,
        callee_def_id: DefId,
        is_virtual: bool,
        terminator: &'tcx mir::Terminator<'tcx>,
    ) {
        if is_virtual {
            // Handle dynamic dispatch for trait objects
            self.handle_virtual_call(callee_def_id, terminator);
        } else {
            self.add_fn_call(callee_def_id, terminator);
        }
    }

    fn handle_virtual_call(
        &mut self,
        stub_def_id: DefId, // Callee is the dynamic call stub, i.e. the fn definition in trait
        terminator: &'tcx mir::Terminator<'tcx>,
    ) {
        // Step 1: Add an edge from caller to the virtual function (stub);
        // If the DefId exists, we assume that stub has been analyzed.
        let visited = !self.call_graph_info.register_fn(stub_def_id);
        self.add_fn_call(stub_def_id, terminator);

        // If this function has already been analyzed, return;
        if visited {
            return;
        }

        // Step 2: Find all impls of the virtual function;
        let candidates = crate::helpers::mir_utils::trait_impl_candidates(self.tcx, stub_def_id);
        rap_debug!(
            "[Callgraph] Implementors of {:?}: {:?}",
            stub_def_id,
            candidates
        );

        // Step 3: For each implementor, add an edge from the stub to it.
        for candidate_def_id in candidates {
            self.add_fn_call(candidate_def_id, terminator);
        }
    }

    pub fn visit(&mut self) {
        self.call_graph_info.register_fn(self.def_id);
        for data in self.body.basic_blocks.iter() {
            let terminator = data.terminator();
            self.visit_terminator(terminator);
        }
    }

    fn visit_terminator(&mut self, terminator: &'tcx mir::Terminator<'tcx>) {
        let mir::TerminatorKind::Call { func, .. } = &terminator.kind else {
            return;
        };
        let Some(callee_def_id) = dep_callee_def_id(func) else {
            return;
        };
        if let Some(instance) = resolve_callee_instance(self.tcx, self.def_id, func) {
            let (instance_def_id, is_virtual) = instance_def_id(self.tcx, instance);
            if let Some(instance_def_id) = instance_def_id {
                self.handle_fn_call(instance_def_id, is_virtual, terminator);
            }
        } else {
            // Fall back to the unresolved def_id.
            self.handle_fn_call(callee_def_id, false, terminator);
        }
    }
}
