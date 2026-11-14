use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::{
    mir::{Local, Operand, Place, ProjectionElem, Rvalue, StatementKind, TerminatorKind},
    ty::{TyCtxt, TyKind},
};
use z3::ast::Int;

use crate::{compat::FxHashMap, helpers::mir_utils, verify::api_classify};

use super::state::{AllocId, VmState, VmValue};

#[derive(Clone)]
pub(crate) struct MethodSnapshot<'z3, 'tcx> {
    method: DefId,
    caller: DefId,
    receiver_alloc: AllocId,
    receiver_offset: Int<'z3>,
    receiver_slice_len: Option<Int<'z3>>,
    owner: Local,
    fields: FxHashMap<Vec<usize>, FieldSnapshot<'z3, 'tcx>>,
}

#[derive(Clone)]
struct FieldSnapshot<'z3, 'tcx> {
    value: VmValue<'z3, 'tcx>,
    slice_len: Option<Int<'z3>>,
}

/// A stable method result paired with the receiver state at the call site.
#[derive(Clone)]
pub(crate) struct CachedMethodResult<'z3, 'tcx> {
    snapshot: MethodSnapshot<'z3, 'tcx>,
    result: Int<'z3>,
}

impl<'z3, 'tcx> VmState<'z3, 'tcx> {
    pub(crate) fn begin_method_call(
        &self,
        method: DefId,
        receiver: &VmValue<'z3, 'tcx>,
        receiver_local: Option<Local>,
    ) -> Option<MethodSnapshot<'z3, 'tcx>> {
        if !stable_local_query(self.tcx, method) {
            return None;
        }
        let provenance = receiver.provenance.as_ref()?;
        let receiver_alloc = provenance.alloc_id;
        let owner = self.method_owner_local(receiver)?;
        if let Some(local) = receiver_local {
            let paths = self.field_paths(local);
            if !paths.is_empty()
                && (paths.len() != self.field_paths(owner).len()
                    || paths.iter().any(|path| {
                        self.field_value(local, path).map(|value| &value.z3_term)
                            != self.field_value(owner, path).map(|value| &value.z3_term)
                    }))
            {
                return None;
            }
        }
        let fields = self
            .field_paths(owner)
            .into_iter()
            .filter_map(|path| {
                self.field_value(owner, &path)
                    .map(|value| (path, self.snapshot_field(value)))
            })
            .collect::<FxHashMap<_, _>>();
        if fields.is_empty() {
            return None;
        }
        Some(MethodSnapshot {
            method,
            caller: self.current_frame.current_def_id,
            receiver_alloc,
            receiver_offset: provenance.offset.clone(),
            receiver_slice_len: self.alloc(receiver_alloc).slice_len().cloned(),
            owner,
            fields,
        })
    }

    pub(crate) fn finish_method_call(
        &mut self,
        snapshot: Option<MethodSnapshot<'z3, 'tcx>>,
        result: Option<&VmValue<'z3, 'tcx>>,
    ) {
        let (Some(snapshot), Some(result)) = (snapshot, result) else {
            return;
        };
        if self.method_snapshot_matches(&snapshot) {
            self.method_result_cache.push(CachedMethodResult {
                snapshot,
                result: result.z3_term.clone(),
            });
        }
    }

    pub(crate) fn cached_method_result(
        &self,
        method: DefId,
        receiver: &VmValue<'z3, 'tcx>,
    ) -> Option<Int<'z3>> {
        let provenance = receiver.provenance.as_ref()?;
        self.method_result_cache.iter().rev().find_map(|entry| {
            (entry.snapshot.method == method
                && entry.snapshot.caller == self.current_frame.current_def_id
                && entry.snapshot.receiver_alloc == provenance.alloc_id
                && entry.snapshot.receiver_offset == provenance.offset
                && self.method_snapshot_matches(&entry.snapshot))
            .then(|| entry.result.clone())
        })
    }

    fn method_snapshot_matches(&self, snapshot: &MethodSnapshot<'z3, 'tcx>) -> bool {
        if snapshot.caller != self.current_frame.current_def_id {
            return false;
        }
        let Some(owner) = self.local_value(snapshot.owner) else {
            return false;
        };
        if owner.provenance_alloc_id() != Some(snapshot.receiver_alloc) {
            return false;
        }
        if self.alloc(snapshot.receiver_alloc).slice_len() != snapshot.receiver_slice_len.as_ref() {
            return false;
        }
        let paths = self.field_paths(snapshot.owner);
        paths.len() == snapshot.fields.len()
            && paths.iter().all(|path| {
                self.field_value(snapshot.owner, path).and_then(|value| {
                    snapshot
                        .fields
                        .get(path)
                        .map(|old| self.field_matches(value, old))
                }) == Some(true)
            })
    }

    fn snapshot_field(&self, value: &VmValue<'z3, 'tcx>) -> FieldSnapshot<'z3, 'tcx> {
        FieldSnapshot {
            value: value.clone(),
            slice_len: value
                .provenance_alloc_id()
                .and_then(|id| self.alloc(id).slice_len().cloned()),
        }
    }

    fn field_matches(&self, value: &VmValue<'z3, 'tcx>, old: &FieldSnapshot<'z3, 'tcx>) -> bool {
        value.z3_term == old.value.z3_term
            && value.ty == old.value.ty
            && value.provenance_alloc_id() == old.value.provenance_alloc_id()
            && value.provenance.as_ref().map(|p| &p.offset)
                == old.value.provenance.as_ref().map(|p| &p.offset)
            && value
                .provenance_alloc_id()
                .and_then(|id| self.alloc(id).slice_len().cloned())
                == old.slice_len
    }

    fn method_owner_local(&self, receiver: &VmValue<'z3, 'tcx>) -> Option<Local> {
        let alloc = receiver.provenance_alloc_id()?;
        self.current_frame
            .local_alloc
            .keys()
            .copied()
            .filter(|local| {
                self.local_value(*local).is_some_and(|value| {
                    value.provenance_alloc_id() == Some(alloc) && value.ty == receiver.ty
                })
            })
            .max_by_key(|local| {
                (
                    self.field_paths(*local).len(),
                    usize::MAX - local.as_usize(),
                )
            })
    }
}

fn stable_local_query(tcx: TyCtxt<'_>, method: DefId) -> bool {
    if !has_method_body(tcx, method) {
        return false;
    }
    let sig = tcx.fn_sig(method).skip_binder();
    let inputs = sig.inputs().skip_binder();
    if inputs.len() != 1
        || !matches!(inputs[0].kind(), TyKind::Ref(_, pointee, rustc_middle::ty::Mutability::Not) if matches!(pointee.kind(), TyKind::Adt(..)))
        || !matches!(
            sig.output().skip_binder().kind(),
            TyKind::Uint(_) | TyKind::Bool
        )
    {
        return false;
    }
    stable_query_body(tcx, method)
}

pub(super) fn stable_contract_query(tcx: TyCtxt<'_>, method: DefId) -> bool {
    if !has_method_body(tcx, method) {
        return false;
    }
    let sig = tcx.fn_sig(method).skip_binder();
    let inputs = sig.inputs().skip_binder();
    if inputs.is_empty()
        || !matches!(inputs[0].kind(), TyKind::Ref(_, pointee, rustc_middle::ty::Mutability::Not) if matches!(pointee.kind(), TyKind::Adt(..)))
        || inputs[1..].iter().any(|ty| !matches!(ty.kind(), TyKind::Uint(_) | TyKind::Int(_) | TyKind::Bool))
        || !matches!(sig.output().skip_binder().kind(), TyKind::Uint(_) | TyKind::Int(_) | TyKind::Bool)
    {
        return false;
    }
    stable_query_body(tcx, method)
}

fn has_method_body(tcx: TyCtxt<'_>, method: DefId) -> bool {
    method.is_local()
        && matches!(tcx.def_kind(method), DefKind::Fn | DefKind::AssocFn)
        && tcx.is_mir_available(method)
}

fn stable_query_body(tcx: TyCtxt<'_>, method: DefId) -> bool {
    let body = tcx.optimized_mir(method);
    for block in body.basic_blocks.iter() {
        for statement in &block.statements {
            match &statement.kind {
                StatementKind::Assign(assign) => {
                    if !plain_local(&assign.0) || !stable_rvalue(&assign.1) {
                        return false;
                    }
                }
                StatementKind::StorageLive(_)
                | StatementKind::StorageDead(_)
                | StatementKind::Nop
                | StatementKind::FakeRead(..) => {}
                _ => return false,
            }
        }
        match &block.terminator().kind {
            TerminatorKind::Goto { .. } | TerminatorKind::Return | TerminatorKind::Unreachable => {}
            TerminatorKind::SwitchInt { discr, .. } => {
                if !stable_operand(discr) {
                    return false;
                }
            }
            TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } => {
                if !plain_local(destination)
                    || args.iter().any(|arg| !stable_operand(&arg.node))
                    || !mir_utils::dep_callee_def_id(func)
                        .is_some_and(|callee| stable_query(tcx, callee))
                {
                    return false;
                }
            }
            _ => return false,
        }
    }
    true
}

fn plain_local(place: &Place<'_>) -> bool {
    place.projection.is_empty()
}

fn stable_place(place: &Place<'_>) -> bool {
    place.projection.is_empty()
        || (place.local == Local::from_usize(1)
            && place.projection.len() == 2
            && matches!(place.projection[0], ProjectionElem::Deref)
            && matches!(place.projection[1], ProjectionElem::Field(..)))
}

fn stable_operand(operand: &Operand<'_>) -> bool {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => stable_place(place),
        Operand::Constant(_) => true,
        _ => false,
    }
}

fn stable_rvalue(rvalue: &Rvalue<'_>) -> bool {
    match rvalue {
        Rvalue::Use(operand, ..) | Rvalue::UnaryOp(_, operand) => stable_operand(operand),
        Rvalue::BinaryOp(_, operands) => stable_operand(&operands.0) && stable_operand(&operands.1),
        Rvalue::Cast(_, operand, _, ..) => stable_operand(operand),
        _ => false,
    }
}

fn stable_query(tcx: TyCtxt<'_>, callee: DefId) -> bool {
    let id = Some(callee);
    if api_classify::is_layout_constant(tcx, id)
        || api_classify::is_benign_origin_use(tcx, id)
        || api_classify::is_intrinsic_ptr_offset_from(tcx, id)
    {
        return true;
    }
    if tcx
        .intrinsic(callee)
        .is_some_and(|intrinsic| intrinsic.name.as_str() == "transmute")
    {
        return true;
    }
    tcx.crate_name(callee.krate).as_str() == "core"
        && tcx
            .opt_associated_item(callee)
            .is_some_and(|item| item.name().as_str() == "offset_from_unsigned")
        && tcx
            .fn_sig(callee)
            .skip_binder()
            .inputs()
            .skip_binder()
            .first()
            .is_some_and(|ty| matches!(ty.kind(), TyKind::RawPtr(..)))
}
