//! Symbolic value domain and Z3 proof adapter for Senryx.
//!
//! The path visitor records lightweight symbolic definitions for MIR locals.
//! Property checkers translate those definitions plus path constraints into Z3
//! bit-vector formulas and prove obligations by checking that the negation is
//! unsatisfiable.

use rustc_middle::mir::{BinOp, UnOp};
use std::collections::HashMap;

use z3::ast::{Ast, BV, Bool};
use z3::{Config, Context, SatResult, Solver};

use crate::analysis::senryx::visitor::PlaceTy;

/// Symbolic definition tracked for one MIR local.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SymbolicDef<'tcx> {
    Param(usize),
    Constant(u128),
    Use(usize),
    Cast(usize, String),
    Binary(BinOp, usize, AnaOperand),
    UnOp(UnOp),
    Call(String, Vec<AnaOperand>),
    Ref(usize),
    /// Pointer offset operation
    PtrOffset(BinOp, usize, AnaOperand, PlaceTy<'tcx>),
}

/// Operand used inside symbolic definitions.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AnaOperand {
    Local(usize),
    Const(u128),
}

/// Current symbolic value information for one MIR local.
#[derive(Clone, Debug, Default)]
pub struct ValueDomain<'tcx> {
    pub def: Option<SymbolicDef<'tcx>>,
    pub value_constraint: Option<u128>,
}

impl<'tcx> ValueDomain<'tcx> {
    /// Return a concrete value when the domain has one.
    pub fn get_constant(&self) -> Option<u128> {
        if let Some(SymbolicDef::Constant(c)) = self.def {
            Some(c)
        } else {
            self.value_constraint
        }
    }
}

/// Verifies a target property using Z3 SMT solver given variable domains and path constraints.
/// Returns true if the property holds (UNSAT for negation), false otherwise.
pub fn verify_with_z3<'tcx, F>(
    values: HashMap<usize, ValueDomain<'tcx>>,
    path_constraints: Vec<SymbolicDef<'tcx>>,
    target_verifier: F,
) -> bool
where
    F: for<'ctx> FnOnce(&'ctx Context, &HashMap<usize, BV<'ctx>>) -> Bool<'ctx>,
{
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);

    let mut z3_vars: HashMap<usize, BV> = HashMap::new();

    // Debug Header
    rap_debug!("\n=== Z3 Constraint Generation Start ===");

    // Create symbolic bitvector variables for all locals
    for local_index in values.keys() {
        let name = format!("loc_{}", local_index);
        z3_vars.insert(*local_index, BV::new_const(&ctx, name, 64));
    }

    // Encode variable definitions (assignments, operations) as solver constraints
    for (local_idx, domain) in &values {
        let current_var = match z3_vars.get(local_idx) {
            Some(v) => v,
            None => continue,
        };

        if let Some(ref def) = domain.def {
            match def {
                SymbolicDef::Cast(src_idx, _ty) => {
                    if let Some(src_var) = z3_vars.get(src_idx) {
                        rap_debug!("  [Def] _{} == _{} (Cast)", local_idx, src_idx);
                        solver.assert(&current_var._eq(src_var));
                    }
                }
                SymbolicDef::Binary(op, lhs_idx, rhs_op) => {
                    if let (Some(lhs), Some(rhs)) =
                        (z3_vars.get(lhs_idx), get_operand_bv(&ctx, rhs_op, &z3_vars))
                    {
                        let op_str = binop_to_str(op);
                        let rhs_str = operand_to_str(rhs_op);
                        rap_debug!(
                            "  [Def] _{} == _{} {} {}",
                            local_idx,
                            lhs_idx,
                            op_str,
                            rhs_str
                        );

                        let result_expr = match op {
                            BinOp::Rem => lhs.bvurem(&rhs),
                            BinOp::Eq => lhs
                                ._eq(&rhs)
                                .ite(&BV::from_u64(&ctx, 1, 64), &BV::from_u64(&ctx, 0, 64)),
                            BinOp::Ne => lhs
                                ._eq(&rhs)
                                .not()
                                .ite(&BV::from_u64(&ctx, 1, 64), &BV::from_u64(&ctx, 0, 64)),
                            BinOp::Add => lhs.bvadd(&rhs),
                            BinOp::Sub => lhs.bvsub(&rhs),
                            BinOp::Mul => lhs.bvmul(&rhs),
                            BinOp::Div => lhs.bvudiv(&rhs),
                            BinOp::BitAnd => lhs.bvand(&rhs),
                            BinOp::BitOr => lhs.bvor(&rhs),
                            BinOp::BitXor => lhs.bvxor(&rhs),
                            BinOp::Shl => lhs.bvshl(&rhs),
                            BinOp::Shr => lhs.bvlshr(&rhs),
                            BinOp::Le => lhs
                                .bvule(&rhs)
                                .ite(&BV::from_u64(&ctx, 1, 64), &BV::from_u64(&ctx, 0, 64)),
                            BinOp::Lt => lhs
                                .bvult(&rhs)
                                .ite(&BV::from_u64(&ctx, 1, 64), &BV::from_u64(&ctx, 0, 64)),
                            BinOp::Gt => lhs
                                .bvugt(&rhs)
                                .ite(&BV::from_u64(&ctx, 1, 64), &BV::from_u64(&ctx, 0, 64)),
                            BinOp::Ge => lhs
                                .bvuge(&rhs)
                                .ite(&BV::from_u64(&ctx, 1, 64), &BV::from_u64(&ctx, 0, 64)),
                            _ => {
                                rap_debug!("    [Warning] Z3: Unsupported Binary Op: {:?}", op);
                                continue;
                            }
                        };
                        solver.assert(&current_var._eq(&result_expr));
                    }
                }
                SymbolicDef::Use(src_idx) => {
                    if let Some(src_var) = z3_vars.get(src_idx) {
                        rap_debug!("  [Def] _{} == _{}", local_idx, src_idx);
                        solver.assert(&current_var._eq(src_var));
                    }
                }
                SymbolicDef::PtrOffset(op, base, idx, stride) => {
                    // Try to translate PtrOffset if stride is concrete
                    if let PlaceTy::Ty(_, size) = stride {
                        if let (Some(base_var), Some(idx_var)) =
                            (z3_vars.get(base), get_operand_bv(&ctx, idx, &z3_vars))
                        {
                            let stride_bv = BV::from_u64(&ctx, *size as u64, 64);
                            let byte_offset = idx_var.bvmul(&stride_bv);

                            let op_str = match op {
                                BinOp::Add | BinOp::Offset => "+",
                                BinOp::Sub => "-",
                                _ => "?",
                            };
                            let idx_str = operand_to_str(idx);

                            rap_debug!(
                                "  [Def] _{} == _{} {} ({} * {} bytes)",
                                local_idx,
                                base,
                                op_str,
                                idx_str,
                                size
                            );

                            let res = match op {
                                BinOp::Add => base_var.bvadd(&byte_offset),
                                BinOp::Sub => base_var.bvsub(&byte_offset),
                                _ => base_var.bvadd(&byte_offset),
                            };
                            solver.assert(&current_var._eq(&res));
                        }
                    } else {
                        rap_debug!(
                            "  [Def] _{} := PtrOffset(...) (Skipped: Generic/Unknown Stride)",
                            local_idx
                        );
                    }
                }
                _ => {}
            }
        }
        if let Some(val) = domain.value_constraint {
            rap_debug!("  [Val] _{} == {}", local_idx, val);
            let z3_val = BV::from_u64(&ctx, val as u64, 64);
            solver.assert(&current_var._eq(&z3_val));
        }
    }

    // Apply path constraints (e.g., branch conditions)
    for constraint in path_constraints {
        match constraint {
            SymbolicDef::Binary(op, lhs_idx, rhs_op) => {
                if let (Some(lhs), Some(rhs)) = (
                    z3_vars.get(&lhs_idx),
                    get_operand_bv(&ctx, &rhs_op, &z3_vars),
                ) {
                    let op_str = binop_to_str(&op);
                    let rhs_str = operand_to_str(&rhs_op);
                    rap_debug!("  [Path] _{} {} {}", lhs_idx, op_str, rhs_str);

                    match op {
                        BinOp::Eq => solver.assert(&lhs._eq(&rhs)),
                        BinOp::Ne => solver.assert(&lhs._eq(&rhs).not()),
                        BinOp::Lt => solver.assert(&lhs.bvult(&rhs)),
                        BinOp::Le => solver.assert(&lhs.bvule(&rhs)),
                        BinOp::Gt => solver.assert(&rhs.bvult(&lhs)),
                        BinOp::Ge => solver.assert(&rhs.bvule(&lhs)),
                        _ => {}
                    }
                }
            }
            _ => {}
        }
    }

    // Assert negation of the target property
    rap_debug!("  [Target] Asserting negation of target property...");
    let target_prop = target_verifier(&ctx, &z3_vars);
    solver.assert(&target_prop.not());

    // Check satisfiability
    let result = solver.check();

    rap_debug!("=== Z3 Verify Finished ===");
    debug_z3_solver_state(&solver, result, &z3_vars);

    // UNSAT means no counter-example exists -> property holds
    match result {
        SatResult::Unsat => true,
        _ => false,
    }
}

// Helper function to handle Z3 solver debug outputs
fn debug_z3_solver_state<'ctx>(
    solver: &Solver<'ctx>,
    result: SatResult,
    z3_vars: &HashMap<usize, BV<'ctx>>,
) {
    match result {
        SatResult::Unsat => {
            rap_debug!("[Z3 Result] UNSAT (Verification Passed)");
        }
        SatResult::Sat => {
            rap_debug!("[Z3 Result] SAT (Verification Failed) - Counter-example found:");

            if let Some(model) = solver.get_model() {
                // Extract and log specific values for variables in the model
                let mut sorted_vars: Vec<_> = z3_vars.iter().collect();
                sorted_vars.sort_by_key(|k| k.0);

                rap_debug!("  --- Counter-example Values ---");
                for (idx, bv) in sorted_vars {
                    if let Some(interp) = model.eval(bv, true) {
                        let val_str = interp
                            .as_u64()
                            .map(|v| v.to_string())
                            .unwrap_or_else(|| interp.to_string());
                        rap_debug!("  _{}: {}", idx, val_str);
                    }
                }
                rap_debug!("  ------------------------------");
            }
        }
        SatResult::Unknown => {
            let reason = solver
                .get_reason_unknown()
                .unwrap_or_else(|| "Unknown".to_string());
            rap_debug!("[Z3 Result] UNKNOWN. Reason: {}", reason);
        }
    }
}

fn get_operand_bv<'a>(
    ctx: &'a Context,
    op: &'a AnaOperand,
    z3_vars: &'a HashMap<usize, BV>,
) -> Option<BV<'a>> {
    match op {
        AnaOperand::Local(idx) => z3_vars.get(idx).cloned(),
        AnaOperand::Const(val) => Some(BV::from_u64(ctx, *val as u64, 64)),
    }
}

// Helper to format operands for debug
fn operand_to_str(op: &AnaOperand) -> String {
    match op {
        AnaOperand::Local(id) => format!("_{}", id),
        AnaOperand::Const(val) => format!("{}", val),
    }
}

// Helper to format BinOp to string
fn binop_to_str(op: &BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::Rem => "%",
        BinOp::BitXor => "^",
        BinOp::BitAnd => "&",
        BinOp::BitOr => "|",
        BinOp::Shl => "<<",
        BinOp::Shr => ">>",
        BinOp::Eq => "==",
        BinOp::Ne => "!=",
        BinOp::Lt => "<",
        BinOp::Le => "<=",
        BinOp::Gt => ">",
        BinOp::Ge => ">=",
        BinOp::Offset => "offset",
        _ => "?",
    }
}
