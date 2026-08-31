//! ValidCStr property checking for the symbolic VM.

use rustc_middle::mir::{Body, Local, Operand, Rvalue, StatementKind, TerminatorKind};
use z3::{
    Solver,
    ast::{Ast, Int},
};

use crate::compat::FxHashMap;
use crate::helpers::mir_scan::Checkpoint;
use crate::helpers::mir_utils::dep_callee_def_id;
use crate::verify::api_classify::is_as_ptr;
use crate::verify::vm::state::{AllocId, VmState};
use crate::verify::{
    contract::{ContractExpr, Property, PropertyArg},
    report::CheckResult,
};

use super::PropertyChecker;

/// Build a `local -> source` map for `Use`/`Cast`/`Ref`/`RawPtr`/`CopyForDeref`
/// assignments and `as_ptr` calls.
fn body_parents(body: &Body<'_>) -> FxHashMap<Local, Local> {
    let mut parents: FxHashMap<Local, Local> = Default::default();
    for data in body.basic_blocks.iter() {
        for statement in &data.statements {
            let StatementKind::Assign(assign) = &statement.kind else {
                continue;
            };
            let (target, rvalue) = assign.as_ref();
            let source = match rvalue {
                Rvalue::Use(Operand::Copy(place) | Operand::Move(place), ..)
                | Rvalue::Cast(_, Operand::Copy(place) | Operand::Move(place), _)
                | Rvalue::Ref(_, _, place)
                | Rvalue::RawPtr(_, place)
                | Rvalue::CopyForDeref(place) => Some(place.local),
                _ => None,
            };
            if let Some(source) = source {
                parents.entry(target.local).or_insert(source);
            }
        }
        let Some(terminator) = &data.terminator else {
            continue;
        };
        let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &terminator.kind
        else {
            continue;
        };
        if !is_as_ptr(dep_callee_def_id(func)) {
            continue;
        }
        let Some(source) = args.first().and_then(|arg| match &arg.node {
            Operand::Copy(place) | Operand::Move(place) => Some(place.local),
            _ => None,
        }) else {
            continue;
        };
        parents.entry(destination.local).or_insert(source);
    }
    parents
}

impl PropertyChecker {
    // ── check_valid_cstr ───────────────────────────────────────

    pub(super) fn check_valid_cstr<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
        solver: &Solver<'ctx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        let value = self
            .target_value(vm_state, checkpoint, property)
            .or_else(|| {
                checkpoint
                    .destination
                    .and_then(|d| vm_state.local_value(d).cloned())
            });
        let Some(value) = value else {
            return CheckResult::Unknown;
        };

        // If we have provenace, check liveness and byte-level tracking
        if let Some(alloc_id) = value.provenance_alloc_id() {
            if vm_state.alloc(alloc_id).dead {
                return CheckResult::Failed;
            }

            // The allocation was asserted to be a null-terminated C string via
            // a `ValidCStr` contract fact / struct invariant. Any sub-slice of
            // it is therefore nul-terminated (it ends at the same nul byte),
            // so the property holds without further byte-level reasoning.
            // Follow `parent` so a `from_raw_parts` / slice-index
            // sub-allocation rooted in a nul-terminated buffer also passes.
            let mut root_id = alloc_id;
            while let Some(parent_id) = vm_state.alloc(root_id).parent {
                root_id = parent_id;
            }
            if vm_state.alloc(alloc_id).nul_terminated || vm_state.alloc(root_id).nul_terminated {
                return CheckResult::Proved;
            }

            let alloc_size = vm_state.allocation_size(alloc_id).cloned();

            // The `ValidCStr(p, n)` length argument is the exact byte length of
            // the nul-terminated buffer.  Prefer it over the allocation size
            // (which may be larger, e.g. a `Vec` with spare capacity).  A
            // `Const` length is the `1` placeholder used for raw pointers
            // (`from_ptr`), whose true length is `strlen(ptr) + 1` and is not
            // expressible in the contract, so it is ignored.
            let n_term = property.args().get(1).and_then(|a| match a {
                PropertyArg::Expr(ContractExpr::Const(_)) => None,
                a => self.resolve_arg_term(vm_state, checkpoint, a),
            });
            let buffer_size = n_term.or(alloc_size);

            // Starting offset within the allocation (for pointer arithmetic like .add(2))
            let start_offset = value
                .provenance
                .as_ref()
                .and_then(|p| p.offset.as_u64())
                .map(|v| v as usize)
                .unwrap_or(0);

            // 1. Try fast-path: concrete byte-level check from known_nul / known_non_nul
            if let Some(r) = self.check_valid_cstr_from_known_nul(vm_state, alloc_id, start_offset)
            {
                return r;
            }

            // 2. Try byte_value-based symbolic check via SMT
            if let Some(size) = buffer_size {
                if let Some(r) =
                    self.check_valid_cstr_from_byte_values(vm_state, solver, alloc_id, &size)
                {
                    return r;
                }
            }
        }

        // 3. MIR-level fallback: scan the body for constant byte assignments
        //    (mirrors the legacy checker's approach for promoted constants)
        if let Some(r) = self.check_valid_cstr_from_mir_constants(vm_state, checkpoint, property) {
            return r;
        }

        // 4. Fallback: if the constructor requires strict NUL-termination
        //    (from_bytes_with_nul_unchecked, from_vec_with_nul_unchecked)
        //    and we can't verify all bytes, return Unknown.
        let is_strict =
            crate::verify::api_classify::is_cstr_unchecked_constructor(checkpoint.callee);
        if is_strict {
            CheckResult::Unknown
        } else {
            CheckResult::Proved
        }
    }

    /// Fast-path: check NUL termination using per-byte NUL/non-NUL knowledge.
    /// This handles constant byte strings like `b"hello\0"` and aggregate initializers
    /// where all element operands are constants.
    /// `start_offset` is the byte offset within the allocation where the C string begins
    /// (non-zero when pointer arithmetic like `.add(n)` is used).
    fn check_valid_cstr_from_known_nul<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
        alloc_id: AllocId,
        start_offset: usize,
    ) -> Option<CheckResult> {
        // Collect all concrete offsets where we know what the byte is
        let known_offsets: Vec<usize> = vm_state
            .alloc_nul_offsets(alloc_id)
            .into_iter()
            .chain(vm_state.alloc_non_nul_offsets(alloc_id))
            .collect();

        if known_offsets.is_empty() {
            return None; // no byte-level info
        }

        let max_known = known_offsets.iter().max().copied().unwrap_or(0);

        // Find the NUL byte at or after start_offset
        let nul_offsets: Vec<usize> = vm_state
            .alloc_nul_offsets(alloc_id)
            .into_iter()
            .filter(|off| *off >= start_offset && *off <= max_known)
            .collect();

        if nul_offsets.is_empty() {
            // No NUL in tracked range — might be in untracked region.
            if let Some(size) = vm_state.allocation_size(alloc_id) {
                if let Some(size_val) = size.as_u64() {
                    if max_known + 1 < size_val as usize {
                        return None;
                    }
                }
            }
            return Some(CheckResult::Failed);
        }

        // Check if there's exactly one NUL at the end of the known range
        let min_nul = nul_offsets.iter().min().copied().unwrap_or(0);

        // All offsets between start_offset and min_nul must be known non-NUL
        for off in start_offset..min_nul {
            if vm_state.is_byte_nul(alloc_id, off) {
                // Interior NUL found before the first NUL after start_offset
                return Some(CheckResult::Failed);
            }
            if !vm_state.is_byte_non_nul(alloc_id, off) {
                // Unknown byte — can't prove valid
                return None;
            }
        }

        // If multiple NUL offsets exist and the first NUL is not at the last
        // tracked position, there is an interior NUL → invalid C string.
        if nul_offsets.len() > 1 && min_nul < max_known {
            return Some(CheckResult::Failed);
        }

        // All bytes between start_offset and the first NUL are known non-NUL,
        // and the NUL itself is known. This is a valid C string for the tracked range.
        Some(CheckResult::Proved)
    }

    /// Check NUL termination using per-byte symbolic values tracked in `bytes`.
    /// Uses the SMT solver to verify that a NUL-terminated byte sequence is possible.
    fn check_valid_cstr_from_byte_values<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
        solver: &Solver<'ctx>,
        alloc_id: AllocId,
        alloc_size: &Int<'ctx>,
    ) -> Option<CheckResult> {
        let byte_pairs = vm_state.alloc_byte_values(alloc_id);
        if byte_pairs.is_empty() {
            return None;
        }

        let zero = Int::from_u64(vm_state.ctx, 0);
        let size_u64 = alloc_size.as_u64();

        if size_u64.is_none() {
            return None; // symbolic-size allocations need different handling
        }

        for &(nul_off, nul_term) in &byte_pairs {
            solver.push();
            solver.assert(&nul_term._eq(&zero));

            for &(off, term) in &byte_pairs {
                if off < nul_off {
                    solver.assert(&term._eq(&zero).not());
                }
            }

            let r = solver.check();
            solver.pop(1);

            if r == z3::SatResult::Sat {
                let mut interior_safe = true;
                for &(off, term) in &byte_pairs {
                    if off < nul_off {
                        solver.push();
                        solver.assert(&term._eq(&zero));
                        let inner = solver.check();
                        solver.pop(1);
                        if inner != z3::SatResult::Unsat {
                            interior_safe = false;
                            break;
                        }
                    }
                }
                if interior_safe {
                    return Some(CheckResult::Proved);
                }
            }
        }

        // If no valid NUL position found, check if the last byte is tracked
        // and no NUL exists among tracked bytes
        let has_nul_in_tracked = byte_pairs.iter().any(|&(_, term)| {
            solver.push();
            solver.assert(&term._eq(&zero));
            let r = solver.check();
            solver.pop(1);
            r == z3::SatResult::Sat
        });

        if !has_nul_in_tracked {
            let last_off = byte_pairs.last().map(|(off, _)| *off).unwrap_or(0);
            if let Some(size) = size_u64 {
                if last_off + 1 >= size as usize {
                    return Some(CheckResult::Failed);
                }
            }
        }

        None
    }

    /// Scan MIR blocks for a single `0_u8` store into the target buffer.
    /// When exactly one nul-store exists among all constant stores, we
    /// can prove ValidCStr even without VM-level byte tracking.  This
    /// mirrors the legacy `nul_store_before_checkpoint` logic.
    fn check_valid_cstr_nul_store<'tcx>(
        vm_state: &VmState<'_, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
    ) -> Option<CheckResult> {
        let target_local = checkpoint.args.get(0).and_then(|op| match op {
            Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => Some(p.local),
            _ => None,
        })?;
        let body = vm_state.body;

        // Build parent map (same as legacy)
        let parents = body_parents(body);
        let root = crate::helpers::mir_utils::resolve_through_casts(
            body,
            crate::helpers::mir_utils::follow_parents(&parents, target_local),
        );

        let mut buffer_locals: rustc_hash::FxHashSet<Local> = rustc_hash::FxHashSet::default();
        let mut seen = rustc_hash::FxHashSet::default();
        let mut work = vec![root];
        while let Some(local) = work.pop() {
            if !seen.insert(local) {
                continue;
            }
            for data in body.basic_blocks.iter() {
                for stmt in &data.statements {
                    let StatementKind::Assign(assign) = &stmt.kind else {
                        continue;
                    };
                    let (target, rvalue) = &**assign;
                    if target.local != local || !target.projection.is_empty() {
                        continue;
                    }
                    if let Rvalue::Ref(_, _, place) = rvalue {
                        buffer_locals.insert(place.local);
                    }
                    #[cfg(rapx_rvalue_use_with_retag)]
                    if let Rvalue::Use(Operand::Copy(p) | Operand::Move(p), _) = rvalue {
                        work.push(p.local);
                    }
                    #[cfg(not(rapx_rvalue_use_with_retag))]
                    if let Rvalue::Use(Operand::Copy(p) | Operand::Move(p)) = rvalue {
                        work.push(p.local);
                    }
                    if let Rvalue::Cast(_, Operand::Copy(p) | Operand::Move(p), _) = rvalue {
                        if p.projection.is_empty() {
                            work.push(p.local);
                        }
                    }
                }
            }
        }

        let mut nul_store_count = 0u32;
        for data in body.basic_blocks.iter() {
            for stmt in &data.statements {
                let StatementKind::Assign(assign) = &stmt.kind else {
                    continue;
                };
                let (target, rvalue) = &**assign;
                let target_root = crate::helpers::mir_utils::follow_parents(&parents, target.local);
                if target_root != root && !buffer_locals.contains(&target_root) {
                    continue;
                }
                if target.projection.is_empty() {
                    continue;
                }
                #[cfg(rapx_rvalue_use_with_retag)]
                let Rvalue::Use(Operand::Constant(c), _) = rvalue else {
                    continue;
                };
                #[cfg(not(rapx_rvalue_use_with_retag))]
                let Rvalue::Use(Operand::Constant(c)) = rvalue else {
                    continue;
                };
                if c.const_
                    .try_to_scalar_int()
                    .map_or(false, |s| s.to_uint(s.size()) == 0)
                {
                    nul_store_count += 1;
                }
            }
        }

        if nul_store_count == 1 {
            Some(CheckResult::Proved)
        } else if nul_store_count > 1 {
            Some(CheckResult::Failed)
        } else {
            None
        }
    }

    /// Fallback: scan the MIR body for constant byte assignments to the target
    /// pointer's root local. Uses worklist-based analysis (handles as_ptr chains
    /// and branches), falling back to simple local chain for Aggregate cases.
    fn check_valid_cstr_from_mir_constants<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        _property: &Property<'tcx>,
    ) -> Option<CheckResult> {
        let target_local = checkpoint.args.get(0).and_then(|op| match op {
            Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => Some(p.local),
            _ => None,
        })?;

        let body = vm_state.body;
        let tcx = vm_state.tcx;

        // 1. Use worklist-based analysis for as_ptr() chains and branch cases
        let all_bytes =
            crate::helpers::mir_utils::collect_all_const_bytes_worklist(tcx, body, target_local);
        if !all_bytes.is_empty() {
            let any_invalid = all_bytes.iter().any(|bytes| {
                !(bytes.last() == Some(&0) && !bytes[..bytes.len().saturating_sub(1)].contains(&0))
            });
            if any_invalid {
                return Some(CheckResult::Failed);
            }
            let all_valid = all_bytes.iter().all(|bytes| {
                bytes.last() == Some(&0) && !bytes[..bytes.len().saturating_sub(1)].contains(&0)
            });
            if all_valid {
                return Some(CheckResult::Proved);
            }
        }

        // 2. Fallback: simple constant byte chain for Aggregate locals
        if let Some(bytes) =
            crate::helpers::mir_utils::const_bytes_for_local(tcx, body, target_local)
        {
            let valid =
                bytes.last() == Some(&0) && !bytes[..bytes.len().saturating_sub(1)].contains(&0);
            return if valid {
                Some(CheckResult::Proved)
            } else {
                Some(CheckResult::Failed)
            };
        }

        // 3. Scan MIR for a single 0_u8 store into the target buffer
        //    (mirrors legacy nul_store_before_checkpoint logic)
        if let Some(r) = Self::check_valid_cstr_nul_store(vm_state, checkpoint) {
            return Some(r);
        }

        None
    }
}
