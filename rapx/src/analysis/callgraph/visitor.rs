use super::default::CallGraph;
use rustc_hir::def_id::DefId;
use rustc_middle::mir;
use rustc_middle::ty::{FnDef, Instance, InstanceKind, TyCtxt, TypingEnv};
use std::collections::HashSet;

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
            tcx: tcx,
            def_id: def_id,
            body: body,
            call_graph_info: call_graph_info,
        }
    }

    fn add_fn_call(&mut self, callee_def_id: DefId, terminator: &'tcx mir::Terminator<'tcx>) {
        self.call_graph_info.register_fn(callee_def_id);
        self.call_graph_info.add_funciton_call(
            self.def_id.clone(),
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
        let mut candidates: HashSet<DefId> = HashSet::new();
        if let Some(trait_def_id) = self.tcx.trait_of_assoc(stub_def_id) {
            rap_debug!(
                "[Callgraph] Virtual fn {:?} belongs to trait {:?}",
                stub_def_id,
                trait_def_id
            );
            for impl_id in self.tcx.all_impls(trait_def_id) {
                let impl_map = self.tcx.impl_item_implementor_ids(impl_id);
                if let Some(candidate_def_id) = impl_map.get(&stub_def_id) {
                    candidates.insert(*candidate_def_id);
                }
            }
        }
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
        for (_, data) in self.body.basic_blocks.iter().enumerate() {
            let terminator = data.terminator();
            self.visit_terminator(&terminator);
        }
    }

    fn visit_terminator(&mut self, terminator: &'tcx mir::Terminator<'tcx>) {
        if let mir::TerminatorKind::Call { func, .. } = &terminator.kind {
            if let mir::Operand::Constant(constant) = func {
                if let FnDef(callee_def_id, callee_substs) = constant.const_.ty().kind() {
                    let ty_env = TypingEnv::post_analysis(self.tcx, self.def_id);
                    if let Ok(Some(instance)) =
                        Instance::try_resolve(self.tcx, ty_env, *callee_def_id, callee_substs)
                    {
                        let mut is_virtual = false;
                        // Try to analysis the specific type of callee.
                        let instance_def_id = match instance.def {
                            InstanceKind::Item(def_id) => Some(def_id),
                            InstanceKind::Intrinsic(def_id) => Some(def_id),
                            InstanceKind::VTableShim(def_id) => Some(def_id),
                            InstanceKind::ReifyShim(def_id, _) => Some(def_id),
                            InstanceKind::FnPtrShim(def_id, _) => Some(def_id),
                            InstanceKind::Virtual(def_id, _) => {
                                is_virtual = true;
                                Some(def_id)
                            }
                            InstanceKind::ClosureOnceShim { call_once, .. } => Some(call_once),
                            InstanceKind::ConstructCoroutineInClosureShim {
                                coroutine_closure_def_id,
                                ..
                            } => Some(coroutine_closure_def_id),
                            InstanceKind::ThreadLocalShim(def_id) => Some(def_id),
                            InstanceKind::DropGlue(def_id, _) => Some(def_id),
                            InstanceKind::FnPtrAddrShim(def_id, _) => Some(def_id),
                            InstanceKind::AsyncDropGlueCtorShim(def_id, _) => Some(def_id),
                            InstanceKind::CloneShim(def_id, _) => {
                                if !self.tcx.is_closure_like(def_id) {
                                    // Not a closure
                                    Some(def_id)
                                } else {
                                    None
                                }
                            }
                            _ => todo!(),
                        };
                        if let Some(instance_def_id) = instance_def_id {
                            self.handle_fn_call(instance_def_id, is_virtual, terminator);
                        }
                    } else {
                        // Although failing to get specific type, callee is still useful.
                        self.handle_fn_call(*callee_def_id, false, terminator);
                    }
                }
            }
        }
    }
}
