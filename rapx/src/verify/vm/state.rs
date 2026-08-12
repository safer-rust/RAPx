//! Symbolic VM state types.
//!
//! Core data structures that represent the symbolic execution state:
//! `VmValue` (symbolic value with invariants), `Allocation` (memory object),
//! and `VmState` (the full execution state at a program point).

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{BasicBlock, Body, Local, Operand, Place, ProjectionElem},
    ty::{Ty, TyCtxt, TypingEnv},
};
use z3::{
    Context,
    ast::{Ast, Bool, Int},
};

use crate::compat::{FxHashMap, FxHashSet};
use crate::verify::{
    def_use::PlaceKey,
    path_extractor::Path,
};

/// Unique identifier for a heap or stack allocation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct AllocId(pub usize);

/// Pointer provenance: which allocation and at what byte offset.
#[derive(Clone, Debug)]
pub struct Provenance<'ctx> {
    /// The allocation this pointer derives from.
    pub alloc_id: AllocId,
    /// Byte offset from the allocation base. A freshly created
    /// pointer to the base of an allocation has `offset = 0`.
    pub offset: Int<'ctx>,
}

/// Known invariants about a symbolic value.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ValueInvariants {
    pub non_null: bool,
    pub aligned: bool,
    pub init: bool,
    pub in_bounds: bool,
    /// If Some(n), the value's term is known to satisfy `term % n == 0`.
    /// Set by alignment guards, Mul by power-of-two, and type alignment.
    pub align_n: Option<u64>,
}

/// A symbolic value tracked by the VM.
///
/// # Semantics of `term`
///
/// - For pointer/reference types (`&T`, `*const T`, `*mut T`, `Box<T>`, etc.):
///   `term` represents the **address** in the VM's logical address space.
/// - For scalar types (integers, `bool`, `char`): `term` represents the **value**.
/// - For aggregate types (struct, tuple, enum): `term` is the base address of
///   the stack allocation backing the aggregate.
///
/// When `provenance` is `Some`, the following relationship holds and is
/// asserted into the solver at check time:
///   `term == alloc[provenance.alloc_id].base + provenance.offset`
#[derive(Clone, Debug)]
pub struct VmValue<'ctx, 'tcx> {
    /// The Z3 integer term (address or scalar value, see struct docs).
    pub term: Int<'ctx>,
    /// Rust type, for layout queries.
    pub ty: Ty<'tcx>,
    /// Which allocation this pointer derives from and at what offset.
    pub provenance: Option<Provenance<'ctx>>,
    /// Known constraints on this value.
    pub invariants: ValueInvariants,
}

impl<'ctx, 'tcx> VmValue<'ctx, 'tcx> {
    pub fn new(term: Int<'ctx>, ty: Ty<'tcx>) -> Self {
        VmValue { term, ty, provenance: None, invariants: ValueInvariants::default() }
    }

    pub fn new_prov(term: Int<'ctx>, ty: Ty<'tcx>, provenance: Provenance<'ctx>) -> Self {
        VmValue { term, ty, provenance: Some(provenance), invariants: ValueInvariants::default() }
    }

    /// Convenience: extract the `AllocId` from provenance, if any.
    pub fn provenance_alloc_id(&self) -> Option<AllocId> {
        self.provenance.as_ref().map(|p| p.alloc_id)
    }
}

/// A memory allocation (stack or heap).
#[derive(Clone, Debug)]
pub struct Allocation<'ctx, 'tcx> {
    /// Unique identifier.
    pub id: AllocId,

    /// Base address (fresh Z3 constant).
    pub base: Int<'ctx>,

    /// Size in bytes (Z3 term, may be symbolic).
    pub size: Int<'ctx>,

    /// Alignment in bytes.
    pub align: u64,

    /// Element type for bounds checking.
    pub element_ty: Option<Ty<'tcx>>,

    /// True if this allocation models an external raw-pointer parameter
    /// whose exact size and nullability are unknown.
    pub is_external: bool,
}

/// Reason an MIR construct could not be executed symbolically.
#[derive(Clone, Debug)]
pub struct UnsupportedReason {
    pub message: String,
    pub block: Option<BasicBlock>,
    pub statement_index: Option<usize>,
}

/// A value definition at a specific program point.
#[derive(Clone, Debug)]
pub struct ValueDefinition<'ctx, 'tcx> {
    pub place: PlaceKey,
    pub value: VmValue<'ctx, 'tcx>,
    pub block: BasicBlock,
    pub statement_index: Option<usize>,
}

/// The full symbolic execution state at a program point.
///
/// Accumulates locals, allocations, path conditions, and definitions
/// as the VM steps through retained MIR items. The Z3 context is
/// borrowed so a single context can be reused across property checks.
pub struct VmState<'ctx, 'tcx> {
    /// Shared Z3 context.
    pub(crate) ctx: &'ctx Context,

    /// Compiler type context.
    pub(crate) tcx: TyCtxt<'tcx>,

    /// The DefId of the function whose body we are executing.
    pub(crate) caller_def_id: DefId,

    /// The MIR body being executed.
    pub(crate) body: &'ctx Body<'tcx>,

    /// Current value bound to each MIR local.
    pub(crate) locals: FxHashMap<Local, VmValue<'ctx, 'tcx>>,

    /// Known address for each stack-allocated local.
    pub(crate) local_addresses: FxHashMap<Local, Int<'ctx>>,

    /// Allocation ID for each stack-allocated local.
    pub(crate) local_alloc_ids: FxHashMap<Local, AllocId>,

    /// All known allocations.
    pub(crate) allocations: Vec<Allocation<'ctx, 'tcx>>,

    /// Accumulated path conditions (SwitchInt branches, Assert).
    pub(crate) path_conditions: Vec<Bool<'ctx>>,

    /// Value definition history (for diagnostic replay).
    pub(crate) definitions: Vec<ValueDefinition<'ctx, 'tcx>>,

    /// The next allocation ID.
    pub(crate) next_alloc_id: usize,

    /// The current basic block (for diagnostics).
    pub(crate) current_block: Option<BasicBlock>,

    /// The current statement index (for diagnostics).
    pub(crate) current_statement_index: Option<usize>,

    /// Track block occurrence counts for loop-carried value indexing.
    pub(crate) block_occurrences: FxHashMap<BasicBlock, usize>,

    /// Allocations that have been freed (StorageDead, Drop).
    pub(crate) dead_allocations: FxHashSet<AllocId>,

    /// Parent allocation for sub-allocations created by split_at / from_raw_parts.
    /// When resolve_origin cannot find a matching local for a sub-allocation,
    /// the chain is followed to the root allocation for provenance tracing.
    pub(crate) sub_alloc_parent: FxHashMap<AllocId, AllocId>,

    /// Block where each dead allocation was killed (for per-block liveness tracking).
    pub(crate) dead_alloc_blocks: FxHashMap<AllocId, BasicBlock>,

    /// Locals that have been dropped (for Alive checks).
    pub(crate) dropped_locals: FxHashSet<Local>,

    /// Binary op sources for guard inference: destination → (lhs, rhs) place keys.
    pub(crate) binary_op_sources: FxHashMap<PlaceKey, (Option<PlaceKey>, Option<PlaceKey>)>,

    /// Non-binary-op sources (select_unpredictable, etc.): destination → (lhs, rhs)
    /// place keys.  Kept separately from `binary_op_sources` so guard inference
    /// (infer_guard_non_null) does not treat these as pointer comparisons.
    pub(crate) other_op_sources: FxHashMap<PlaceKey, (Option<PlaceKey>, Option<PlaceKey>)>,

    /// Allocations that have been written to (initialized via write/MaybeUninit).
    pub(crate) init_allocations: FxHashSet<AllocId>,

    /// Allocations assumed alive via contract (e.g. #[rapx::requires(Alive(ptr))]).
    pub(crate) alive_assumed: FxHashSet<AllocId>,

    /// Whether a SplitTransmute contract was asserted by the caller.
    pub(crate) split_transmute_asserted: bool,

    /// Slice data allocations: maps a &[T] reference's stack AllocId to the
    /// symbolic data allocation created for the slice contents.
    pub(crate) slice_data_allocations: FxHashMap<AllocId, AllocId>,

    /// Field-level value tracking for aggregates: (local, field_indices) → value.
    /// Example: `(local_3, [0])` is `local_3.0`, `(local_3, [0, 1])` is `local_3.0.1`.
    pub(crate) field_values: FxHashMap<(Local, Vec<usize>), VmValue<'ctx, 'tcx>>,

    /// Locals set by `iterpreter_iter_is_empty` for Iter/IterMut,
    /// along with the field-based len expression. When a switchint
    /// on such local takes the false (!is_empty) branch, we inject
    /// `len >= 1` as a path condition to help Z3.
    pub(crate) is_empty_len: FxHashMap<Local, Int<'ctx>>,

    /// Cumulative ptr offset for Iter/IterMut field [0] (ptr).
    /// Key: (struct_local). When post_inc_start advances the ptr by
    /// `n` elements, we increment this offset instead of nesting
    /// symbolic additions. This keeps Z3 expressions compact.
    pub(crate) iter_ptr_offset: FxHashMap<Local, Int<'ctx>>,

    /// Fields that have been explicitly initialized (written to).
    pub(crate) field_init: FxHashSet<(Local, Vec<usize>)>,

    /// Byte offsets within an allocation that are known to be NUL (0x00).
    pub(crate) known_nul_offsets: FxHashSet<(AllocId, usize)>,

    /// Byte offsets within an allocation that are known to be non-NUL (!= 0x00).
    pub(crate) known_non_nul_offsets: FxHashSet<(AllocId, usize)>,

    /// Per-byte symbolic values: (alloc_id, concrete_byte_offset) → Z3 term.
    /// Populated by Aggregate initialisation, pointer stores, and write call effects.
    /// Enables byte-level reasoning for properties like ValidCStr.
    pub(crate) byte_values: FxHashMap<(AllocId, usize), Int<'ctx>>,

    /// Bytes known to have been explicitly written (initialized at byte level).
    pub(crate) byte_init: FxHashSet<(AllocId, usize)>,

    /// Records calls that performed index bounds & disjointness validation.
    /// Each entry is (indices_array_alloc_id, len_value_term).
    /// The property checker uses this to automatically pass InBound checks
    /// that were already validated by a prior call.
    pub(crate) checked_bounds_disjoint: Vec<(AllocId, Int<'ctx>)>,
    /// Whether a ChecksIndexBoundsDisjoint call was processed in any
    /// checkpoint of this function (accumulated across checkpoints).
    pub(crate) has_checked_bounds: bool,

    /// Notes from unsupported operations.
    pub(crate) notes: Vec<String>,

    /// The path being executed (for branch target resolution).
    pub(crate) path: Option<Path>,

    /// Name of the most recent call (for context-aware effects like Vec push).
    pub(crate) last_call_name: String,

    /// Stack of nested function contexts for cross-function inline.
    /// Top of stack is the currently executing function.
    /// Each entry is (body, def_id).
    pub(crate) body_stack: Vec<(&'ctx Body<'tcx>, DefId)>,

    /// Saved caller locals during callee inline (CalleeEntry/CalleeExit).
    pub(crate) saved_caller_locals: Option<FxHashMap<Local, VmValue<'ctx, 'tcx>>>,

    /// Terms that are the result of a bitwise `Not` (two's-complement mask).
    /// Used to recognize `x & !(align-1)` alignment patterns in BitAnd so we
    /// can derive `align = -mask` and emit linear bounds for the result.
    pub(crate) not_mask_terms: FxHashSet<Int<'ctx>>,
}

impl<'ctx, 'tcx> VmState<'ctx, 'tcx> {
    /// Create a fresh VM state for executing a path.
    pub fn new(
        ctx: &'ctx Context,
        tcx: TyCtxt<'tcx>,
        body: &'ctx Body<'tcx>,
        caller_def_id: DefId,
    ) -> Self {
        Self {
            ctx,
            tcx,
            body,
            caller_def_id,
            locals: FxHashMap::default(),
            local_addresses: FxHashMap::default(),
            local_alloc_ids: FxHashMap::default(),
            allocations: Vec::new(),
            path_conditions: Vec::new(),
            definitions: Vec::new(),
            next_alloc_id: 0,
            current_block: None,
            current_statement_index: None,
            block_occurrences: FxHashMap::default(),
            dead_allocations: FxHashSet::default(),
            dead_alloc_blocks: FxHashMap::default(),
            sub_alloc_parent: FxHashMap::default(),
            dropped_locals: FxHashSet::default(),
            binary_op_sources: FxHashMap::default(),
            other_op_sources: FxHashMap::default(),
            init_allocations: FxHashSet::default(),
            alive_assumed: FxHashSet::default(),
            split_transmute_asserted: false,
            slice_data_allocations: FxHashMap::default(),
            field_values: FxHashMap::default(),
            is_empty_len: FxHashMap::default(),
            iter_ptr_offset: FxHashMap::default(),
            field_init: FxHashSet::default(),
            known_nul_offsets: FxHashSet::default(),
            known_non_nul_offsets: FxHashSet::default(),
            byte_values: FxHashMap::default(),
            byte_init: FxHashSet::default(),
            checked_bounds_disjoint: Vec::new(),
            has_checked_bounds: false,
            notes: Vec::new(),
            path: None,
            last_call_name: String::new(),
            body_stack: Vec::new(),
            saved_caller_locals: None,
            not_mask_terms: FxHashSet::default(),
        }
    }

    /// Look up the value bound to a MIR local.
    pub fn local_value(&self, local: Local) -> Option<&VmValue<'ctx, 'tcx>> {
        self.locals.get(&local)
    }

    /// Bind a value to a MIR local.
    pub fn set_local(&mut self, local: Local, value: VmValue<'ctx, 'tcx>) {
        self.locals.insert(local, value);
    }

    /// Get or create the symbolic address of a MIR local.
    pub fn local_address(&mut self, local: Local) -> Int<'ctx> {
        if let Some(addr) = self.local_addresses.get(&local) {
            return addr.clone();
        }
        let name = format!("addr__{}", local.as_usize());
        let addr = Int::new_const(self.ctx, name.as_str());
        self.local_addresses.insert(local, addr.clone());
        addr
    }

    /// Allocate a fresh symbolic object and return its ID and base address.
    pub fn allocate(
        &mut self,
        size: Int<'ctx>,
        align: u64,
        element_ty: Option<Ty<'tcx>>,
    ) -> (AllocId, Int<'ctx>) {
        let id = AllocId(self.next_alloc_id);
        self.next_alloc_id += 1;
        let base = {
            let name = format!("heap_{}", id.0);
            Int::new_const(self.ctx, name.as_str())
        };
        let alloc = Allocation {
            id,
            base: base.clone(),
            size,
            align,
            element_ty,
            is_external: false,
        };
        self.allocations.push(alloc);
        (id, base)
    }

    /// Allocate a fresh external allocation (for raw-pointer parameters).
    /// External allocations may be null and have unlimited size.
    pub fn allocate_external(
        &mut self,
        size: Int<'ctx>,
        align: u64,
        element_ty: Option<Ty<'tcx>>,
    ) -> (AllocId, Int<'ctx>) {
        let id = AllocId(self.next_alloc_id);
        self.next_alloc_id += 1;
        let base = {
            let name = format!("ext_{}", id.0);
            Int::new_const(self.ctx, name.as_str())
        };
        let alloc = Allocation {
            id,
            base: base.clone(),
            size,
            align,
            element_ty,
            is_external: true,
        };
        self.allocations.push(alloc);
        (id, base)
    }

    /// Create a symbolic Z3 int constant.
    pub fn fresh_int(&self, prefix: &str) -> Int<'ctx> {
        let name = format!("{}_{}", prefix, self.definitions.len());
        Int::new_const(self.ctx, name.as_str())
    }

    /// Record a value definition for diagnostics.
    pub fn record_definition(
        &mut self,
        place: PlaceKey,
        value: &VmValue<'ctx, 'tcx>,
    ) {
        self.definitions.push(ValueDefinition {
            place,
            value: value.clone(),
            block: self.current_block.unwrap_or(BasicBlock::from_usize(0)),
            statement_index: self.current_statement_index,
        });
    }

    /// Find the most recent value definition for a place key.
    pub fn find_definition(&self, pk: &PlaceKey) -> Option<&ValueDefinition<'ctx, 'tcx>> {
        self.definitions.iter().rev().find(|d| d.place.base == pk.base && d.place.fields == pk.fields)
    }

    /// Get the value of a specific field within an aggregate local.
    pub fn field_value(&self, local: Local, path: &[usize]) -> Option<&VmValue<'ctx, 'tcx>> {
        self.field_values.get(&(local, path.to_vec()))
    }

    /// Set the value of a specific field within an aggregate local.
    pub fn set_field_value(&mut self, local: Local, path: Vec<usize>, value: VmValue<'ctx, 'tcx>) {
        self.field_values.insert((local, path), value);
    }

    /// Mark a field path as initialized.
    pub fn mark_field_init(&mut self, local: Local, path: Vec<usize>) {
        self.field_init.insert((local, path));
    }

    /// Check if a field path is initialized.
    pub fn is_field_init(&self, local: Local, path: &[usize]) -> bool {
        self.field_init.contains(&(local, path.to_vec()))
    }

    /// Record a per-byte symbolic value at a concrete offset in an allocation.
    pub fn record_byte_value(&mut self, alloc_id: AllocId, offset: usize, term: Int<'ctx>) {
        self.byte_values.insert((alloc_id, offset), term);
        self.byte_init.insert((alloc_id, offset));
    }

    /// Record a range of byte values from a `[u8; N]` array literal or byte slice.
    /// `start_offset` is the byte offset within the allocation where the range begins.
    pub fn record_byte_range(
        &mut self,
        alloc_id: AllocId,
        start_offset: usize,
        values: &[Int<'ctx>],
    ) {
        for (i, term) in values.iter().enumerate() {
            let off = start_offset + i;
            self.byte_values.insert((alloc_id, off), term.clone());
            self.byte_init.insert((alloc_id, off));
        }
    }

    /// Look up a per-byte Z3 term for a concrete offset in an allocation.
    pub fn get_byte_value(&self, alloc_id: AllocId, offset: usize) -> Option<&Int<'ctx>> {
        self.byte_values.get(&(alloc_id, offset))
    }

    /// Check whether a byte at a concrete offset is known to be initialized.
    pub fn is_byte_init(&self, alloc_id: AllocId, offset: usize) -> bool {
        self.byte_init.contains(&(alloc_id, offset))
    }

    /// Return all known (offset, term) pairs for an allocation, sorted by offset.
    pub fn alloc_byte_values(&self, alloc_id: AllocId) -> Vec<(usize, &Int<'ctx>)> {
        let mut pairs: Vec<_> = self
            .byte_values
            .iter()
            .filter_map(|((aid, off), term)| if *aid == alloc_id { Some((*off, term)) } else { None })
            .collect();
        pairs.sort_by_key(|(off, _)| *off);
        pairs
    }

    /// Check if a concrete byte offset within an allocation is explicitly known NUL.
    pub fn is_known_nul(&self, alloc_id: AllocId, offset: usize) -> bool {
        self.known_nul_offsets.contains(&(alloc_id, offset))
    }

    /// Check if a concrete byte offset within an allocation is explicitly known non-NUL.
    pub fn is_known_non_nul(&self, alloc_id: AllocId, offset: usize) -> bool {
        self.known_non_nul_offsets.contains(&(alloc_id, offset))
    }

    /// Get the maximum `size_of` for a generic type parameter by
    /// enumerating all implementors of its trait bounds.
    pub fn size_of_generic_param(&self, ty: Ty<'tcx>) -> u64 {
        match ty.kind() {
            rustc_middle::ty::TyKind::Param(_) => {}
            _ => return 0,
        };
        let param_env = self.tcx.param_env(self.caller_def_id);
        let typing_env = rustc_middle::ty::TypingEnv::post_analysis(self.tcx, self.caller_def_id);
        for clause in param_env.caller_bounds() {
            let Some(trait_clause) = clause.as_trait_clause() else { continue };
            let self_ty = trait_clause.self_ty().skip_binder();
            if self_ty != ty {
                continue;
            }
            let trait_def_id = trait_clause.def_id();
            let mut max_size: u64 = 0;
            for impl_def_id in self.tcx.all_impls(trait_def_id) {
                let impl_ty = self.tcx.type_of(impl_def_id).skip_binder();
                if crate::helpers::mir_utils::ty_has_param_const(impl_ty) {
                    continue;
                }
                let layout = match crate::helpers::mir_utils::catch_panic(|| {
                    self.tcx.layout_of(
                        rustc_middle::ty::PseudoCanonicalInput {
                            typing_env,
                            value: impl_ty,
                        }
                    )
                }) {
                    Ok(Ok(l)) => l,
                    _ => continue,
                };
                max_size = max_size.max(layout.size.bytes());
            }
            return max_size;
        }
        0
    }

    /// Get the minimum `align_of` for a generic type parameter by
    /// enumerating all implementors of its trait bounds.
    pub fn min_align_of_generic_param(&self, ty: Ty<'tcx>) -> u64 {
        match ty.kind() {
            rustc_middle::ty::TyKind::Param(_) => {}
            _ => return 0,
        };
        let param_env = self.tcx.param_env(self.caller_def_id);
        let typing_env = rustc_middle::ty::TypingEnv::post_analysis(self.tcx, self.caller_def_id);
        for clause in param_env.caller_bounds() {
            let Some(trait_clause) = clause.as_trait_clause() else { continue };
            let self_ty = trait_clause.self_ty().skip_binder();
            if self_ty != ty {
                continue;
            }
            let trait_def_id = trait_clause.def_id();
            let mut min_align: u64 = u64::MAX;
            for impl_def_id in self.tcx.all_impls(trait_def_id) {
                let impl_ty = self.tcx.type_of(impl_def_id).skip_binder();
                if crate::helpers::mir_utils::ty_has_param_const(impl_ty) {
                    continue;
                }
                let layout = match crate::helpers::mir_utils::catch_panic(|| {
                    self.tcx.layout_of(
                        rustc_middle::ty::PseudoCanonicalInput {
                            typing_env,
                            value: impl_ty,
                        }
                    )
                }) {
                    Ok(Ok(l)) => l,
                    _ => continue,
                };
                min_align = min_align.min(layout.align.abi.bytes());
            }
            return if min_align == u64::MAX { 0 } else { min_align };
        }
        0
    }

    /// Assert path conditions and invariant constraints into a solver.
    pub fn assert_all(&self, solver: &z3::Solver<'ctx>) {
        for cond in &self.path_conditions {
            solver.assert(cond);
        }
        let zero = Int::from_u64(self.ctx, 0);
        for alloc in &self.allocations {
            if !alloc.is_external {
                solver.assert(&alloc.base._eq(&zero).not());
            }
            solver.assert(&alloc.size.ge(&zero));
            if alloc.align > 1 {
                let align_term = Int::from_u64(self.ctx, alloc.align);
                solver.assert(&alloc.base.rem(&align_term)._eq(&zero));
            }
        }

        for (_local, value) in self.locals.iter() {
            if value.invariants.non_null {
                solver.assert(&value.term._eq(&zero).not());
            }
            if let Some(ref prov) = value.provenance {
                if let Some(alloc) = self.allocations.iter().find(|a| a.id == prov.alloc_id) {
                    let expected = Int::add(self.ctx, &[&alloc.base, &prov.offset]);
                    solver.assert(&value.term._eq(&expected));
                }
            }
            if matches!(value.ty.kind(),
                rustc_middle::ty::TyKind::Uint(_)
                | rustc_middle::ty::TyKind::Bool
                | rustc_middle::ty::TyKind::Char
            ) {
                solver.assert(&value.term.ge(&zero));
            }
            if matches!(value.ty.kind(), rustc_middle::ty::TyKind::Bool) {
                let one = Int::from_u64(self.ctx, 1);
                solver.assert(&value.term.le(&one));
            }
            if matches!(value.ty.kind(), rustc_middle::ty::TyKind::Char) {
                let max = Int::from_u64(self.ctx, 0x10FFFF);
                solver.assert(&value.term.le(&max));
            }
        }
        for value in self.field_values.values() {
            if value.invariants.non_null {
                solver.assert(&value.term._eq(&zero).not());
            }
            if let Some(ref prov) = value.provenance {
                if let Some(alloc) = self.allocations.iter().find(|a| a.id == prov.alloc_id) {
                    let expected = Int::add(self.ctx, &[&alloc.base, &prov.offset]);
                    solver.assert(&value.term._eq(&expected));
                }
            }
            if matches!(value.ty.kind(),
                rustc_middle::ty::TyKind::Uint(_)
                | rustc_middle::ty::TyKind::Bool
                | rustc_middle::ty::TyKind::Char
            ) {
                solver.assert(&value.term.ge(&zero));
            }
            if matches!(value.ty.kind(), rustc_middle::ty::TyKind::Bool) {
                let one = Int::from_u64(self.ctx, 1);
                solver.assert(&value.term.le(&one));
            }
            if matches!(value.ty.kind(), rustc_middle::ty::TyKind::Char) {
                let max = Int::from_u64(self.ctx, 0x10FFFF);
                solver.assert(&value.term.le(&max));
            }
        }
    }
}

impl std::fmt::Debug for VmState<'_, '_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("VmState")
            .field("locals_count", &self.locals.len())
            .field("allocations_count", &self.allocations.len())
            .field("path_conditions", &self.path_conditions.len())
            .field("definitions", &self.definitions.len())
            .field("notes", &self.notes)
            .finish()
    }
}

// ── Shared value extraction ──────────────────────────────────────

impl<'ctx, 'tcx> VmState<'ctx, 'tcx> {
    /// Extract a VmValue from a MIR operand.
    pub(crate) fn value_of_operand(&self, operand: &Operand<'tcx>) -> VmValue<'ctx, 'tcx> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                self.value_of_place(place)
                    .unwrap_or_else(|| self.unknown_value_for_place(place))
            }
            Operand::Constant(constant) => {
                let text = format!("{:?}", constant.const_);
                let int_val = const_int_from_debug(&text);
                let term = if let Some(v) = int_val {
                    Int::from_u64(self.ctx, v)
                } else {
                    // Create a deterministic name for const generics so
                    // multiple uses of the same parameter share one term.
                    let name = format!("const_{}", text.replace([':', '#', ' '], "_"));
                    Int::new_const(self.ctx, name.as_str())
                };
                let ty = constant.const_.ty();
                VmValue {
                    term,
                    ty,
                    provenance: None,
                    invariants: ValueInvariants::default(),
                }
            }
            #[cfg(rapx_rustc_ge_196)]
            Operand::RuntimeChecks(_) => {
                VmValue::new(self.fresh_int("runtime_checks"), self.body.local_decls[Local::from_usize(0)].ty)
            }
        }
    }

    /// Look up the value stored at a MIR place.
    pub(crate) fn value_of_place(&self, place: &Place<'tcx>) -> Option<VmValue<'ctx, 'tcx>> {
        if place.projection.is_empty() {
            return self.locals.get(&place.local).cloned();
        }

        // Collect field indices from projections
        let field_path: Vec<usize> = place.projection.iter()
            .filter_map(|proj| match proj.kind() {
                ProjectionElem::Field(field_idx, _) => Some(field_idx.as_usize()),
                _ => None,
            })
            .collect();

        // If we have a pure field path (only Field projections), look up
        // in the per-field value map first.
        if !field_path.is_empty() && field_path.len() == place.projection.len() {
            if let Some(val) = self.field_values.get(&(place.local, field_path)).cloned() {
                return Some(val);
            }
            // Fallback: when the base local has provenance, propagate it
            // to field accesses. This handles pointer-wrapper types (Box,
            // Unique, NonNull) where accessing inner pointer fields yields
            // the same provenance as the container.
            if let Some(base_val) = self.locals.get(&place.local) {
                if let Some(ref prov) = base_val.provenance {
                    return Some(VmValue {
                        term: base_val.term.clone(),
                        ty: place.ty(self.body, self.tcx).ty,
                        provenance: Some(prov.clone()),
                        invariants: base_val.invariants,
                    });
                }
            }
            return None;
        }

        // For Deref+Field chains (e.g. (*self).ptr), strip the leading Deref
        // projection(s) and look up field_values with the remaining field path.
        if !field_path.is_empty() && field_path.len() < place.projection.len()
            && place.projection.iter().any(|p| matches!(p.kind(), ProjectionElem::Deref))
        {
            // Only Deref and Field projections — all non-Field must be Deref.
            let non_field_deref = place.projection.iter()
                .all(|p| matches!(p.kind(), ProjectionElem::Field(..) | ProjectionElem::Deref));
            if non_field_deref {
                // Recompute field_path since the original was moved.
                let fp: Vec<usize> = place.projection.iter()
                    .filter_map(|proj| match proj.kind() {
                        ProjectionElem::Field(field_idx, _) => Some(field_idx.as_usize()),
                        _ => None,
                    })
                    .collect();
                if let Some(val) = self.field_values.get(&(place.local, fp)).cloned() {
                    return Some(val);
                }
            }
        }

        // Handle Deref + Field projections: follow the dereference chain to
        // get the pointee base, then apply field offsets.
        // E.g. `(*self).ptr` → Deref then Field(0).
        let mut base = self.locals.get(&place.local)?.clone();
        for proj in place.projection.iter() {
            match proj.kind() {
                ProjectionElem::Deref => {
                    let _ = &base.provenance; // prov reference not yet used for value_of_place
                    base.ty = place.ty(self.body, self.tcx).ty;
                }
                ProjectionElem::Field(_field_idx, _) => {
                    // Try to get the field value from the VM's field tracking
                    let field_indices: Vec<usize> = place.projection.iter()
                        .filter_map(|p| match p.kind() {
                            ProjectionElem::Field(fi, _) => Some(fi.as_usize()),
                            _ => None,
                        })
                        .collect();
                    if !field_indices.is_empty() {
                        if let Some(val) = self.field_values.get(&(place.local, field_indices)).cloned() {
                            return Some(val);
                        }
                    }
                    // Fallback: return the base with updated type info
                    base.ty = place.ty(self.body, self.tcx).ty;
                }
                _ => {}
            }
        }

        // Fall back to type-level resolution with single-element projections
        if place.projection.len() == 1 {
            if let Some(proj) = place.projection.first() {
                match proj {
                    ProjectionElem::Index(local) => {
                        if let Some(ref prov) = base.provenance {
                            let alloc_id = prov.alloc_id;
                            let byte_vals: Vec<_> = self.alloc_byte_values(alloc_id);
                            if !byte_vals.is_empty() {
                                let inner_ty = match base.ty.kind() {
                                    rustc_middle::ty::TyKind::Array(inner, _) => *inner,
                                    _ => return Some(base.clone()),
                                };
                                let elem_sz = self.size_of_ty(inner_ty) as usize;
                                let step = elem_sz.max(1);
                                if let Some(index_val) = self.locals.get(local) {
                                    if let Some(concrete_idx) = index_val.term.as_u64() {
                                        let offset = concrete_idx as usize * step;
                                        let term = self
                                            .get_byte_value(alloc_id, offset)
                                            .cloned()
                                            .unwrap_or_else(|| self.fresh_int("arr_elem"));
                                        return Some(VmValue {
                                            term,
                                            ty: place.ty(self.body, self.tcx).ty,
                                            provenance: None,
                                            invariants: ValueInvariants::default(),
                                        });
                                    } else {
                                        let mut chain = self.fresh_int("arr_elem");
                                        for (offset, term) in byte_vals.iter().rev() {
                                            let vidx = offset / step;
                                            let idx_term = Int::from_u64(self.ctx, vidx as u64);
                                            let cond = index_val.term._eq(&idx_term);
                                            chain = Bool::ite(&cond, term, &chain);
                                        }
                                        return Some(VmValue {
                                            term: chain,
                                            ty: place.ty(self.body, self.tcx).ty,
                                            provenance: None,
                                            invariants: ValueInvariants::default(),
                                        });
                                    }
                                }
                            }
                        }
                        return Some(base.clone());
                    }
                    _ => {}
                }
                match proj.kind() {
                    ProjectionElem::Deref => {
                        let mut val = base.clone();
                        val.ty = place.ty(self.body, self.tcx).ty;
                        return Some(val);
                    }
                    ProjectionElem::Field(_field_idx, _field_ty) => {
                        let val = base.clone();
                        return Some(val);
                    }
                _ => {
                    // Downcast or other unsupported projection: still return
                    // the base with updated type so provenance propagates.
                    let mut val = base.clone();
                    val.ty = place.ty(self.body, self.tcx).ty;
                    return Some(val);
                }
                }
            }
        }

        // For multi-element projections with Deref+Field or Downcast, return
        // the base value since we already traced through Deref above.
        if place.projection.len() > 1
            && place.projection.iter().any(|p| matches!(
                p.kind(), ProjectionElem::Deref | ProjectionElem::Downcast(..)
            ))
        {
            let mut val = base;
            val.ty = place.ty(self.body, self.tcx).ty;
            return Some(val);
        }

        None
    }

    /// Create an unknown value for a place.
    pub(crate) fn unknown_value_for_place(&self, place: &Place<'tcx>) -> VmValue<'ctx, 'tcx> {
        let ty = place.ty(self.body, self.tcx).ty;
        let is_raw_ptr = matches!(ty.kind(), rustc_middle::ty::TyKind::RawPtr(..));
        VmValue {
            term: self.fresh_int("unknown"),
            ty,
            provenance: None,
            invariants: ValueInvariants {
                non_null: is_raw_ptr,
                ..Default::default()
            },
        }
    }
}

/// Parse a const integer from debug output.
pub(crate) fn const_int_from_debug(text: &str) -> Option<u64> {
    if let Ok(v) = text.parse::<u64>() {
        return Some(v);
    }
    if let Some(start) = text.find("0x") {
        let hex_part = &text[start..];
        let end = hex_part
            .find(|c: char| !c.is_ascii_hexdigit() && c != 'x')
            .unwrap_or(hex_part.len());
        u64::from_str_radix(&hex_part[2..end], 16).ok()
    } else if let Some(start) = text.find("Value(") {
        let inner = &text[start + 6..];
        if let Some(end) = inner.find(')') {
            inner[..end].parse::<u64>().ok()
        } else {
            None
        }
    } else {
        None
    }
}

// ── Constant byte-string extraction ───────────────────────────

/// Try to extract raw bytes from a MIR constant operand that is a reference
/// to a byte array/slice (e.g. `b"hello\0"`). Returns the byte values.
/// Used by the VM to populate byte-level tracking for constant C strings.
pub(crate) fn extract_const_bytes_from_operand<'tcx>(
    tcx: TyCtxt<'tcx>,
    operand: &Operand<'tcx>,
) -> Option<Vec<u8>> {
    let constant = match operand {
        Operand::Constant(c) => c,
        _ => return None,
    };
    let ty = constant.const_.ty();
    let (inner_ty, _is_ref) = match ty.kind() {
        rustc_middle::ty::TyKind::Ref(_, inner, _) => (*inner, true),
        _ => return None,
    };
    // Peel through nested references (e.g. &&[u8])
    let inner_ty = if let rustc_middle::ty::TyKind::Ref(_, innermost, _) = inner_ty.kind() {
        *innermost
    } else {
        inner_ty
    };
    let _elem_ty = match inner_ty.kind() {
        rustc_middle::ty::TyKind::Array(elem, _) | rustc_middle::ty::TyKind::Slice(elem) => *elem,
        _ => return None,
    };

    // Evaluate the MIR constant to get a ConstValue
    let typing_env = TypingEnv::fully_monomorphized();
    let value = constant
        .const_
        .eval(tcx, typing_env, rustc_span::DUMMY_SP)
        .ok()?;

    crate::helpers::mir_utils::const_value_bytes(tcx, value, 0)
}
