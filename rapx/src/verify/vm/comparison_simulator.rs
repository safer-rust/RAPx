//! Exact comparison models for supported trait calls.
//!
//! A model must describe the returned boolean on both branches. In particular,
//! equality never writes its operands or makes a fact true unconditionally.

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{BinOp, Local, Operand, Rvalue, StatementKind},
    ty::{TyCtxt, TyKind},
};
use z3::ast::{Ast, Bool, Int};

use super::state::{AllocKind, ValueSource, VmState, VmValue};
use crate::def_ids::lang_api::{self, LangItem};
use crate::helpers::mir_utils;

#[derive(Clone, Copy)]
enum ComparisonMethod {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

impl ComparisonMethod {
    fn from_callee(tcx: TyCtxt<'_>, callee: DefId) -> Option<Self> {
        let assoc = tcx.opt_associated_item(callee)?;
        let trait_id = assoc.trait_container(tcx)?;
        let symbol = assoc.name();
        let name = symbol.as_str();
        if lang_api::matches(tcx, trait_id, LangItem::PartialEq) {
            return match name {
                "eq" => Some(Self::Eq),
                "ne" => Some(Self::Ne),
                _ => None,
            };
        }
        if lang_api::matches(tcx, trait_id, LangItem::PartialOrd) {
            return match name {
                "lt" => Some(Self::Lt),
                "le" => Some(Self::Le),
                "gt" => Some(Self::Gt),
                "ge" => Some(Self::Ge),
                _ => None,
            };
        }
        None
    }

    fn mir_op(self) -> BinOp {
        match self {
            Self::Eq => BinOp::Eq,
            Self::Ne => BinOp::Ne,
            Self::Lt => BinOp::Lt,
            Self::Le => BinOp::Le,
            Self::Gt => BinOp::Gt,
            Self::Ge => BinOp::Ge,
        }
    }

    fn compare<'z3>(self, left: &Int<'z3>, right: &Int<'z3>) -> Bool<'z3> {
        match self {
            Self::Eq => left._eq(right),
            Self::Ne => left._eq(right).not(),
            Self::Lt => left.lt(right),
            Self::Le => left.le(right),
            Self::Gt => left.gt(right),
            Self::Ge => left.ge(right),
        }
    }
}

impl<'z3, 'tcx> VmState<'z3, 'tcx> {
    pub(crate) fn try_simulate_comparison(
        &mut self,
        callee: Option<DefId>,
        args: &[VmValue<'z3, 'tcx>],
        destination: Local,
    ) -> bool {
        let Some(method) = callee.and_then(|id| ComparisonMethod::from_callee(self.tcx, id)) else {
            return false;
        };
        if args.len() != 2
            || !matches!(self.body().local_decls[destination].ty.kind(), TyKind::Bool)
        {
            return false;
        }

        let Some(condition) = self
            .scalar_comparison(method, &args[0], &args[1])
            .or_else(|| match method {
                ComparisonMethod::Eq => self.byte_slice_eq(&args[0], &args[1]),
                ComparisonMethod::Ne => self.byte_slice_eq(&args[0], &args[1]).map(|eq| eq.not()),
                _ => None,
            })
        else {
            return false;
        };
        let one = Int::from_u64(self.z3_ctx, 1);
        let zero = Int::from_u64(self.z3_ctx, 0);
        let mut result = VmValue::new(condition.ite(&one, &zero), self.tcx.types.bool);
        result.source = ValueSource::Comparison {
            lhs: None,
            rhs: None,
            op: method.mir_op(),
            cond: condition,
        };
        self.set_local(destination, result);
        true
    }

    /// A reference to a primitive scalar compares its stored value, not its
    /// address. Floats are excluded because this integer model cannot express NaN.
    fn scalar_comparison(
        &self,
        method: ComparisonMethod,
        left: &VmValue<'z3, 'tcx>,
        right: &VmValue<'z3, 'tcx>,
    ) -> Option<Bool<'z3>> {
        let left_prov = left.provenance.as_ref()?;
        let right_prov = right.provenance.as_ref()?;
        if left_prov.offset.simplify().as_u64() != Some(0)
            || right_prov.offset.simplify().as_u64() != Some(0)
        {
            return None;
        }
        let ty = self.alloc(left_prov.alloc_id).element_ty.as_ty()?;
        if ty != self.alloc(right_prov.alloc_id).element_ty.as_ty()?
            || !matches!(
                ty.kind(),
                TyKind::Uint(_) | TyKind::Int(_) | TyKind::Bool | TyKind::Char
            )
        {
            return None;
        }
        let left_value = self.load_value(left_prov.alloc_id, ty, &[])?;
        let right_value = self.load_value(right_prov.alloc_id, ty, &[])?;
        if !matches!(left_value.source, ValueSource::SharedScalarReferent)
            || !matches!(right_value.source, ValueSource::SharedScalarReferent)
        {
            return None;
        }
        Some(method.compare(&left_value.z3_term, &right_value.z3_term))
    }

    /// Compare a tracked `[u8]` view with a fully materialized constant byte
    /// array. The result is `len == N && bytes[0..N] == constant`.
    fn byte_slice_eq(
        &self,
        left: &VmValue<'z3, 'tcx>,
        right: &VmValue<'z3, 'tcx>,
    ) -> Option<Bool<'z3>> {
        self.byte_slice_const_eq(left, right)
            .or_else(|| self.byte_slice_const_eq(right, left))
    }

    fn byte_slice_const_eq(
        &self,
        slice: &VmValue<'z3, 'tcx>,
        constant: &VmValue<'z3, 'tcx>,
    ) -> Option<Bool<'z3>> {
        let slice_id = slice.provenance_alloc_id()?;
        let slice_alloc = self.alloc(slice_id);
        if slice_alloc.element_ty.as_ty() != Some(self.tcx.types.u8)
            || !matches!(slice_alloc.kind, AllocKind::Slice { .. } | AllocKind::ExternalSlice { .. })
            || slice.provenance.as_ref()?.offset.simplify().as_u64() != Some(0)
        {
            return None;
        }
        let bytes = self.constant_bytes(constant)?;
        let byte_len = bytes.len();
        let len = self.slice_len_of_alloc(slice_id)?;
        let mut conditions = vec![len._eq(&Int::from_u64(self.z3_ctx, byte_len as u64))];
        for (offset, byte) in bytes.iter().enumerate() {
            if !self.is_byte_init(slice_id, offset) {
                return None;
            }
            let index = Int::from_u64(self.z3_ctx, offset as u64);
            conditions.push(
                self.byte_read(slice_id, &index)
                    ._eq(&Int::from_u64(self.z3_ctx, *byte as u64)),
            );
        }
        Some(Bool::and(
            self.z3_ctx,
            &conditions.iter().collect::<Vec<_>>(),
        ))
    }

    fn constant_bytes(&self, value: &VmValue<'z3, 'tcx>) -> Option<Vec<u8>> {
        if let ValueSource::ConstBytes(bytes) = &value.source {
            return Some(bytes.clone());
        }
        // Sliced paths can bind a promoted constant as a symbolic call
        // argument, bypassing the `Use` transfer that carries ConstBytes.
        // Recover it only by matching that exact symbolic constant to its MIR
        // operand in a live caller frame.
        let bodies = std::iter::once(self.root_body()).chain(
            self.caller_frames
                .iter()
                .map(|saved| &saved.frame)
                .chain(std::iter::once(&self.current_frame))
                .filter_map(|frame| {
                    frame.body.or_else(|| {
                        self.tcx
                            .is_mir_available(frame.current_def_id)
                            .then(|| self.tcx.optimized_mir(frame.current_def_id))
                    })
                }),
        );
        for body in bodies {
            for block in body.basic_blocks.iter() {
                for statement in &block.statements {
                    let StatementKind::Assign(assign) = &statement.kind else {
                        continue;
                    };
                    let Rvalue::Use(Operand::Constant(constant), ..) = &assign.1 else {
                        continue;
                    };
                    if self.symbolic_const_term(&constant.const_) == value.z3_term
                        && let Some(bytes) = mir_utils::const_operand_bytes(
                            self.tcx,
                            &Operand::Constant(constant.clone()),
                        )
                    {
                        return Some(bytes);
                    }
                }
            }
        }
        None
    }
}
