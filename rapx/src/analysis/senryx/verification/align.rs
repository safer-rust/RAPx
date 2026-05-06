//! Alignment contract checker for Senryx.
//!
//! This file owns all APIs related to `Align(ptr, T)` and path-sensitive
//! alignment refinement. The checker can currently prove these alignment cases:
//!
//! 1. **Caller-provided contract facts**: the checked graph node already has a
//!    contract fact such as `Align(ptr, T)`.
//! 2. **Direct pointer/object compatibility**: the pointer's operational trace
//!    state (OTS) is known aligned and the modeled pointee object has an ABI
//!    alignment that is at least as strong as the contract-required type.
//! 3. **Pointer arithmetic preservation**: the pointer was produced by a
//!    recognized offset operation (`ptr.add`, `ptr.sub`, `ptr.offset`,
//!    byte-level variants, or MIR `Offset`) and the Z3 model proves that every
//!    modeled offset keeps the resulting address aligned for the required type.
//! 4. **Runtime alignment guards**: branch refinement from calls such as
//!    `ptr.is_aligned()` marks the checked pointer, and its traced source when
//!    available, as aligned or unaligned on the corresponding path.
//!
//! The algorithm checks cheap local facts first: contract facts, then graph/OTS
//! facts. It falls back to Z3 only when the graph records symbolic pointer
//! arithmetic. Generic types are handled by enumerating the finite layout set
//! discovered by `GenericChecker`; if that set is empty, the checker uses a
//! conservative alignment/stride candidate set.

use crate::{
    analysis::{
        senryx::{
            contract::{AlignState, PropertyContract},
            symbolic_analysis::{AnaOperand, SymbolicDef, verify_with_z3},
            visitor::{BodyVisitor, PlaceTy},
        },
        utils::fn_info::{get_pointee, is_ptr, is_ref},
    },
    rap_debug,
};
use rustc_middle::{mir::BinOp, ty::Ty};
use z3::ast::{Ast, BV};

impl<'tcx> BodyVisitor<'tcx> {
    /// Prove that `arg` satisfies the contract `Align(arg, contract_required_ty)`.
    ///
    /// The proof order is contract facts, then symbolic offset proof, then direct
    /// graph/OTS alignment. The offset proof is tried before the direct check
    /// because derived pointers normally carry their key alignment evidence in
    /// `offset_from` rather than in the immediate pointee type alone.
    pub fn check_align(&self, arg: usize, contract_required_ty: Ty<'tcx>) -> bool {
        let required_ty_layout = self.visit_ty_and_get_layout(contract_required_ty);
        if self.check_align_from_facts(arg, &required_ty_layout) {
            return true;
        }

        if let Some((op, base_local, offset_op, stride_layout)) = self.get_ptr_offset_info(arg) {
            return self.check_offset_align_with_z3(
                op,
                base_local,
                offset_op,
                stride_layout,
                contract_required_ty,
            );
        }

        self.check_align_directly(arg, required_ty_layout)
    }

    /// Check alignment facts that came directly from caller annotations.
    fn check_align_from_facts(&self, arg: usize, required_layout: &PlaceTy<'tcx>) -> bool {
        if let Some(var) = self.chains.get_var_node(arg) {
            for fact in &var.facts.contracts {
                if let PropertyContract::Align(fact_ty) = fact {
                    let fact_layout = self.visit_ty_and_get_layout(*fact_ty);
                    if Self::two_types_cast_check(fact_layout, required_layout.clone()) {
                        return true;
                    }
                }
            }
        }
        false
    }

    /// Check alignment from the current graph state and pointed object type.
    fn check_align_directly(&self, pointer_id: usize, required_ty: PlaceTy<'tcx>) -> bool {
        if let Some(pointee) = self.chains.get_obj_ty_through_chain(pointer_id) {
            let pointee_ty = self.visit_ty_and_get_layout(pointee);
            let pointer = self.chains.get_var_node(pointer_id).unwrap();

            if let AlignState::Aligned(_) = pointer.ots.align {
                return Self::two_types_cast_check(pointee_ty, required_ty);
            }
        }
        false
    }

    /// Use Z3 to prove that pointer arithmetic preserves required alignment.
    ///
    /// The formula models `result = base +/- index * stride` and proves that
    /// whenever the base address is aligned for each possible base alignment,
    /// the result address is aligned for every required alignment.
    fn check_offset_align_with_z3(
        &self,
        op: BinOp,
        base_local: usize,
        offset_op: AnaOperand,
        stride_layout: PlaceTy<'tcx>,
        contract_required_ty: Ty<'tcx>,
    ) -> bool {
        let req_layout = self.visit_ty_and_get_layout(contract_required_ty);
        let mut req_aligns = req_layout.possible_aligns();

        if let PlaceTy::GenericTy(..) = req_layout {
            if req_aligns.is_empty() {
                req_aligns.extend([1, 2, 4, 8, 16, 32, 64]);
            }
        }

        if req_aligns.len() == 1 && req_aligns.contains(&1) {
            return true;
        }

        let base_node = if let Some(node) = self.chains.get_var_node(base_local) {
            node
        } else {
            return false;
        };

        let base_pointee_ty = if let Some(ty) = base_node.ty {
            get_pointee(ty)
        } else {
            return false;
        };

        let base_layout = self.visit_ty_and_get_layout(base_pointee_ty);
        let mut base_aligns = base_layout.possible_aligns();

        if let PlaceTy::GenericTy(..) = base_layout {
            if base_aligns.is_empty() {
                base_aligns.extend([1, 2, 4, 8, 16, 32, 64]);
            }
        }

        rap_debug!(
            "Z3 Align Check: base_{} {:?} (aligns {:?}) {:?} offset (stride {:?}) => req_aligns {:?}",
            base_local,
            op,
            base_aligns,
            op,
            stride_layout,
            req_aligns
        );

        verify_with_z3(
            self.value_domains.clone(),
            self.path_constraints.clone(),
            |ctx, vars| {
                let bv_zero = BV::from_u64(ctx, 0, 64);

                let bv_base = if let Some(b) = vars.get(&base_local) {
                    b.clone()
                } else {
                    return z3::ast::Bool::from_bool(ctx, false);
                };

                let bv_index = match &offset_op {
                    AnaOperand::Local(idx) => {
                        if let Some(v) = vars.get(idx) {
                            v.clone()
                        } else {
                            BV::from_u64(ctx, 0, 64)
                        }
                    }
                    AnaOperand::Const(val) => BV::from_u64(ctx, *val as u64, 64),
                };

                let possible_strides: Vec<u64> = match &stride_layout {
                    PlaceTy::Ty(_, size) => vec![*size as u64],
                    PlaceTy::GenericTy(_, _, layout_set) => {
                        if layout_set.is_empty() {
                            vec![1, 2, 4, 8, 16, 32, 64]
                        } else {
                            layout_set.iter().map(|(_, size)| *size as u64).collect()
                        }
                    }
                    PlaceTy::Unknown => vec![1],
                };

                let mut constraints = Vec::new();
                let is_same_generic = match (&req_layout, &base_layout) {
                    (PlaceTy::GenericTy(n1, _, _), PlaceTy::GenericTy(n2, _, _)) => n1 == n2,
                    _ => false,
                };

                for stride in possible_strides {
                    let bv_stride = BV::from_u64(ctx, stride, 64);
                    let bv_byte_offset = bv_index.bvmul(&bv_stride);
                    let result_ptr = match op {
                        BinOp::Add => bv_base.bvadd(&bv_byte_offset),
                        BinOp::Sub => bv_base.bvsub(&bv_byte_offset),
                        _ => bv_base.bvadd(&bv_byte_offset),
                    };

                    if is_same_generic {
                        for align in &req_aligns {
                            let bv_align = BV::from_u64(ctx, *align as u64, 64);
                            let base_is_aligned = bv_base.bvurem(&bv_align)._eq(&bv_zero);
                            let result_aligned = result_ptr.bvurem(&bv_align)._eq(&bv_zero);
                            constraints.push(base_is_aligned.implies(&result_aligned));
                        }
                    } else {
                        for b_align in &base_aligns {
                            for r_align in &req_aligns {
                                let bv_base_align = BV::from_u64(ctx, *b_align as u64, 64);
                                let bv_req_align = BV::from_u64(ctx, *r_align as u64, 64);
                                let base_is_aligned = bv_base.bvurem(&bv_base_align)._eq(&bv_zero);
                                let result_aligned = result_ptr.bvurem(&bv_req_align)._eq(&bv_zero);
                                constraints.push(base_is_aligned.implies(&result_aligned));
                            }
                        }
                    }
                }

                if constraints.is_empty() {
                    return z3::ast::Bool::from_bool(ctx, false);
                }

                let constraints_refs: Vec<&z3::ast::Bool> = constraints.iter().collect();
                z3::ast::Bool::and(ctx, &constraints_refs)
            },
        )
    }

    /// Return the pointer-offset summary attached to a graph node, if present.
    fn get_ptr_offset_info(&self, arg: usize) -> Option<(BinOp, usize, AnaOperand, PlaceTy<'tcx>)> {
        if let Some(domain) = self.chains.get_var_node(arg) {
            if let Some(SymbolicDef::PtrOffset(op, base, off, place_ty)) = &domain.offset_from {
                return Some((*op, *base, off.clone(), place_ty.clone()));
            }
        }
        None
    }

    /// Refine the alignment state after a branch such as `ptr.is_aligned()`.
    ///
    /// `is_aligned == true` records an `Aligned(pointee_ty)` fact; `false`
    /// records `Unaligned(pointee_ty)`. The visitor calls this on both the
    /// condition operand and, when traceable, the source pointer.
    pub fn update_align_state(&mut self, ptr_local: usize, is_aligned: bool) {
        let ptr_ty_opt = self.chains.get_var_node(ptr_local).and_then(|n| n.ty);

        if let Some(ptr_ty) = ptr_ty_opt {
            if is_ptr(ptr_ty) || is_ref(ptr_ty) {
                let pointee_ty = get_pointee(ptr_ty);

                if let Some(ptr_node) = self.chains.get_var_node_mut(ptr_local) {
                    if is_aligned {
                        ptr_node.ots.align = AlignState::Aligned(pointee_ty);
                        rap_debug!(
                            "Refine State: _{} (source) marked as Aligned({:?}) via condition (True).",
                            ptr_local,
                            pointee_ty
                        );
                    } else {
                        ptr_node.ots.align = AlignState::Unaligned(pointee_ty);
                        rap_debug!(
                            "Refine State: _{} (source) marked as Unaligned({:?}) via condition (False).",
                            ptr_local,
                            pointee_ty
                        );
                    }
                }
            }
        }
    }

    /// Check a previously computed alignment state without re-running offset proof.
    pub fn check_align_by_pre_computed_state(
        &self,
        arg: usize,
        contract_required_ty: Ty<'tcx>,
    ) -> bool {
        if let Some(var) = self.chains.get_var_node(arg) {
            if let AlignState::Aligned(state_ty) = var.ots.align {
                let state_layout = self.visit_ty_and_get_layout(state_ty);
                let req_layout = self.visit_ty_and_get_layout(contract_required_ty);

                rap_debug!(
                    "Check Align: arg_{} StateTy: {:?} vs ReqTy: {:?}",
                    arg,
                    state_layout,
                    req_layout
                );

                return Self::two_types_cast_check(state_layout, req_layout);
            } else {
                rap_debug!("Check Align: arg_{} is Unaligned or Unknown", arg);
            }
        } else {
            rap_debug!("Check Align: arg_{} node not found", arg);
        }
        false
    }

    /// Return true when every possible source alignment implies the destination alignment.
    fn two_types_cast_check(src: PlaceTy<'tcx>, dest: PlaceTy<'tcx>) -> bool {
        let src_aligns = src.possible_aligns();
        let dest_aligns = dest.possible_aligns();
        if dest_aligns.len() == 0 && src != dest {
            return false;
        }

        for &d_align in &dest_aligns {
            if d_align != 1 && src_aligns.len() == 0 {
                return false;
            }
            for &s_align in &src_aligns {
                if s_align < d_align {
                    return false;
                }
            }
        }
        true
    }

    /// Try to strengthen a base pointer's alignment with numeric constraints.
    fn _try_refine_alignment(&self, base_local: usize, current_align: u64) -> u64 {
        for candidate in [64, 32, 16, 8, 4] {
            if candidate <= current_align {
                break;
            }

            let is_proven = verify_with_z3(
                self.value_domains.clone(),
                self.path_constraints.clone(),
                |ctx, vars| {
                    if let Some(bv_base) = vars.get(&base_local) {
                        let bv_cand = BV::from_u64(ctx, candidate, 64);
                        let bv_zero = BV::from_u64(ctx, 0, 64);
                        bv_base.bvurem(&bv_cand)._eq(&bv_zero)
                    } else {
                        z3::ast::Bool::from_bool(ctx, false)
                    }
                },
            );

            if is_proven {
                rap_debug!(
                    "Refine Align: Successfully refined base_{} to align {}",
                    base_local,
                    candidate
                );
                return candidate;
            }
        }
        current_align
    }

    /// Prove that a symbolic offset is a multiple of `align`.
    fn _check_offset_is_aligned(&self, offset: &AnaOperand, align: u64) -> bool {
        verify_with_z3(
            self.value_domains.clone(),
            self.path_constraints.clone(),
            |ctx, vars| {
                let bv_align = BV::from_u64(ctx, align, 64);
                let bv_zero = BV::from_u64(ctx, 0, 64);

                let bv_offset = match offset {
                    AnaOperand::Local(idx) => {
                        if let Some(v) = vars.get(idx) {
                            v.clone()
                        } else {
                            BV::from_u64(ctx, 0, 64)
                        }
                    }
                    AnaOperand::Const(val) => BV::from_u64(ctx, *val as u64, 64),
                };

                bv_offset.bvurem(&bv_align)._eq(&bv_zero)
            },
        )
    }

    /// Prove that an accumulated symbolic offset plus one current operand is aligned.
    fn _check_cumulative_offset_aligned(
        &self,
        acc_def: &SymbolicDef<'tcx>,
        curr_op: &AnaOperand,
        align: u64,
    ) -> bool {
        verify_with_z3(
            self.value_domains.clone(),
            self.path_constraints.clone(),
            |ctx, vars| {
                let bv_align = BV::from_u64(ctx, align, 64);
                let bv_zero = BV::from_u64(ctx, 0, 64);
                let bv_acc = self.symbolic_def_to_bv(ctx, vars, acc_def);
                let bv_curr = match curr_op {
                    AnaOperand::Local(idx) => {
                        if let Some(v) = vars.get(idx) {
                            v.clone()
                        } else {
                            BV::from_u64(ctx, 0, 64)
                        }
                    }
                    AnaOperand::Const(val) => BV::from_u64(ctx, *val as u64, 64),
                };
                let total = bv_acc.bvadd(&bv_curr);
                total.bvurem(&bv_align)._eq(&bv_zero)
            },
        )
    }

    /// Convert a local symbolic definition to a Z3 bit-vector expression.
    fn symbolic_def_to_bv<'a>(
        &self,
        ctx: &'a z3::Context,
        vars: &std::collections::HashMap<usize, BV<'a>>,
        def: &SymbolicDef<'tcx>,
    ) -> BV<'a> {
        match def {
            SymbolicDef::Constant(c) => BV::from_u64(ctx, *c as u64, 64),
            SymbolicDef::Use(l) => vars.get(l).cloned().unwrap_or(BV::from_u64(ctx, 0, 64)),
            SymbolicDef::Binary(op, lhs, rhs) => {
                let lhs_bv = vars.get(lhs).cloned().unwrap_or(BV::from_u64(ctx, 0, 64));
                let rhs_bv = match rhs {
                    AnaOperand::Local(l) => {
                        vars.get(l).cloned().unwrap_or(BV::from_u64(ctx, 0, 64))
                    }
                    AnaOperand::Const(c) => BV::from_u64(ctx, *c as u64, 64),
                };
                match op {
                    BinOp::Add => lhs_bv.bvadd(&rhs_bv),
                    _ => BV::from_u64(ctx, 0, 64),
                }
            }
            _ => BV::from_u64(ctx, 0, 64),
        }
    }
}
