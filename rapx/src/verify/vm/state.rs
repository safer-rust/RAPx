//! Symbolic VM state types.
//!
//! Core data structures that represent the symbolic execution state:
//! `VmValue` (symbolic value with invariants), `Allocation` (memory object),
//! and `VmState` (the full execution state at a program point).

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{BasicBlock, Body, Local, Operand, Place, ProjectionElem},
    ty::{Ty, TyCtxt},
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
    /// Whether `offset` is a compile-time field offset (`offset_of!`).  Such an
    /// offset always satisfies `0 <= offset` and `offset + size_of(field) <=
    /// size_of(container)`, which the verifier uses to discharge in-bounds
    /// checks for patterns like `Option::as_slice`.
    pub is_field_offset: bool,
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
    /// Whether this scalar value is a compile-time field offset (`offset_of!`).
    /// Propagated to a pointer's provenance when used as an `add`/`byte_add`
    /// offset.
    pub is_field_offset: bool,
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

    /// Convenience: extract the `AllocId` from provenance, if any.
    pub fn provenance_alloc_id(&self) -> Option<AllocId> {
        self.provenance.as_ref().map(|p| p.alloc_id)
    }
}

/// A memory allocation (stack or heap).
///
/// The allocation is stored in `VmState::allocations` at index `AllocId.0`
/// (an `AllocId` is a monotonic counter that doubles as the vector index).
#[derive(Clone, Debug)]
pub struct Allocation<'ctx, 'tcx> {
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

    /// Allocations that have been freed (StorageDead, Drop).
    pub dead: bool,

    /// Allocations that have been written to (initialized via write/MaybeUninit).
    pub initialized: bool,

    /// Allocations assumed alive via contract (e.g. `#[rapx::requires(Alive(ptr))]`).
    pub alive_assumed: bool,

    /// Allocations known to be a null-terminated byte buffer (a valid C
    /// string), asserted via a `ValidCStr` contract fact or struct invariant.
    pub nul_terminated: bool,

    /// Parent allocation for sub-allocations created by split_at / from_raw_parts.
    pub parent: Option<AllocId>,

    /// Slice data allocation: for a `&[T]` reference's stack allocation, the
    /// symbolic data allocation created for the slice contents.
    pub slice_data: Option<AllocId>,
}

/// One-shot execution/contract flags accumulated while stepping a path.
#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct ContractFlags {
    /// Whether a SplitTransmute contract was asserted by the caller.
    pub split_transmute_asserted: bool,
    /// Whether an `Alias` hazard was accepted via the caller's contract.
    pub alias_hazard_accepted: bool,
    /// Whether a ChecksIndexBoundsDisjoint call was processed in any
    /// checkpoint of this function (accumulated across checkpoints).
    pub has_checked_bounds: bool,
    /// Set once the path evaluated an `Iterator::next` discriminant whose
    /// variant was known symbolically.
    pub saw_next_discriminant: bool,
}

/// Per-byte symbolic state at a concrete offset in an allocation.
#[derive(Clone, Debug, Default)]
pub(crate) struct ByteInfo<'ctx> {
    /// Symbolic value, if tracked.
    pub value: Option<Int<'ctx>>,
    /// Whether the byte has been explicitly written.
    pub init: bool,
    /// NUL knowledge: `Some(true)` known NUL, `Some(false)` known non-NUL.
    pub nul: Option<bool>,
}

/// A saved caller context pushed when entering an inlined callee during path
/// execution.
pub(crate) struct InlineFrame<'ctx, 'tcx> {
    pub body: &'ctx Body<'tcx>,
    pub def_id: DefId,
    pub saved_locals: FxHashMap<Local, VmValue<'ctx, 'tcx>>,
    pub saved_field_values: FxHashMap<(Local, Vec<usize>), VmValue<'ctx, 'tcx>>,
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

    /// Monotonic counter used to uniquify fresh symbolic constant names.
    pub(crate) definition_count: usize,

    /// The next allocation ID.
    pub(crate) next_alloc_id: usize,

    /// Track block occurrence counts for loop-carried value indexing.
    pub(crate) block_occurrences: FxHashMap<BasicBlock, usize>,

    /// Binary op sources for guard inference: destination → (lhs, rhs) place keys.
    pub(crate) binary_op_sources: FxHashMap<PlaceKey, (Option<PlaceKey>, Option<PlaceKey>)>,

    /// Direct boolean condition for a comparison result place (Le/Lt/Ge/Gt/Eq/Ne),
    /// used to record precise switch-guard path conditions.
    pub(crate) comparison_conds: FxHashMap<PlaceKey, Bool<'ctx>>,

    /// Enum discriminant term for a local holding an `Option`-like value whose
    /// variant is known symbolically (e.g. `Iterator::next` returns
    /// `Some(x) iff !is_empty`). Used by `Rvalue::Discriminant` so `switchInt`
    /// branches stay tied to the actual emptiness condition.
    pub(crate) discriminant_terms: FxHashMap<Local, Int<'ctx>>,

    /// Non-binary-op sources (select_unpredictable, etc.): destination → (lhs, rhs)
    /// place keys.  Kept separately from `binary_op_sources` so guard inference
    /// (infer_guard_non_null) does not treat these as pointer comparisons.
    pub(crate) other_op_sources: FxHashMap<PlaceKey, (Option<PlaceKey>, Option<PlaceKey>)>,

    /// One-shot execution/contract flags accumulated while stepping a path.
    pub(crate) contract_flags: ContractFlags,

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

    /// Per-byte symbolic state: (alloc_id, concrete_byte_offset) → ByteInfo.
    /// Populated by aggregate initialisation, pointer stores, and write call
    /// effects. Enables byte-level reasoning for properties like ValidCStr.
    pub(crate) bytes: FxHashMap<(AllocId, usize), ByteInfo<'ctx>>,

    /// Notes from unsupported operations.
    pub(crate) notes: Vec<String>,

    /// The path being executed (for branch target resolution).
    pub(crate) path: Option<Path>,

    /// Name of the most recent call (for context-aware effects like Vec push).
    pub(crate) last_call_name: String,

    /// Current depth of the recursive `exec_inline_call` stack.  `exec_call`
    /// re-enters inline execution with `depth = 0` on every nested call, so a
    /// separate counter (instead of the `depth` argument) is needed to actually
    /// bound nested inlining and avoid unbounded recursion / stack overflow.
    pub(crate) inline_depth: usize,

    /// Stack of saved caller contexts for inlined-callee path execution.
    pub(crate) inline_frames: Vec<InlineFrame<'ctx, 'tcx>>,

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
            definition_count: 0,
            next_alloc_id: 0,
            block_occurrences: FxHashMap::default(),
            binary_op_sources: FxHashMap::default(),
            comparison_conds: FxHashMap::default(),
            discriminant_terms: FxHashMap::default(),
            other_op_sources: FxHashMap::default(),
            contract_flags: ContractFlags::default(),
            field_values: FxHashMap::default(),
            is_empty_len: FxHashMap::default(),
            iter_ptr_offset: FxHashMap::default(),
            bytes: FxHashMap::default(),
            notes: Vec::new(),
            path: None,
            last_call_name: String::new(),
            inline_depth: 0,
            inline_frames: Vec::new(),
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
            base: base.clone(),
            size,
            align,
            element_ty,
            is_external: false,
            dead: false,
            initialized: false,
            alive_assumed: false,
            nul_terminated: false,
            parent: None,
            slice_data: None,
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
            base: base.clone(),
            size,
            align,
            element_ty,
            is_external: true,
            dead: false,
            initialized: false,
            alive_assumed: false,
            nul_terminated: false,
            parent: None,
            slice_data: None,
        };
        self.allocations.push(alloc);
        (id, base)
    }

    /// Indexed access to an allocation by its `AllocId` (the id is the index).
    pub(crate) fn alloc(&self, id: AllocId) -> &Allocation<'ctx, 'tcx> {
        &self.allocations[id.0]
    }

    /// Mutable indexed access to an allocation by its `AllocId`.
    pub(crate) fn alloc_mut(&mut self, id: AllocId) -> &mut Allocation<'ctx, 'tcx> {
        &mut self.allocations[id.0]
    }

    /// Create a symbolic Z3 int constant.
    pub fn fresh_int(&self, prefix: &str) -> Int<'ctx> {
        let name = format!("{}_{}", prefix, self.definition_count);
        Int::new_const(self.ctx, name.as_str())
    }

    /// Bump the symbolic-name uniquifier (called once per executed assignment).
    pub fn record_definition(&mut self) {
        self.definition_count += 1;
    }

    /// Get the value of a specific field within an aggregate local.
    pub fn field_value(&self, local: Local, path: &[usize]) -> Option<&VmValue<'ctx, 'tcx>> {
        self.field_values.get(&(local, path.to_vec()))
    }

    /// Set the value of a specific field within an aggregate local.
    pub fn set_field_value(&mut self, local: Local, path: Vec<usize>, value: VmValue<'ctx, 'tcx>) {
        self.field_values.insert((local, path), value);
    }

    /// Record a per-byte symbolic value at a concrete offset in an allocation.
    pub fn record_byte_value(&mut self, alloc_id: AllocId, offset: usize, term: Int<'ctx>) {
        let byte = self.bytes.entry((alloc_id, offset)).or_default();
        byte.value = Some(term);
        byte.init = true;
    }

    /// Mark a byte as initialized without changing its value.
    pub fn mark_byte_init(&mut self, alloc_id: AllocId, offset: usize) {
        self.bytes.entry((alloc_id, offset)).or_default().init = true;
    }

    /// Mark a byte as known NUL (0x00).
    pub fn mark_byte_nul(&mut self, alloc_id: AllocId, offset: usize) {
        self.bytes.entry((alloc_id, offset)).or_default().nul = Some(true);
    }

    /// Mark a byte as known non-NUL (!= 0x00).
    pub fn mark_byte_non_nul(&mut self, alloc_id: AllocId, offset: usize) {
        self.bytes.entry((alloc_id, offset)).or_default().nul = Some(false);
    }

    /// Look up a per-byte Z3 term for a concrete offset in an allocation.
    pub fn get_byte_value(&self, alloc_id: AllocId, offset: usize) -> Option<&Int<'ctx>> {
        self.bytes.get(&(alloc_id, offset)).and_then(|b| b.value.as_ref())
    }

    /// Check whether a byte at a concrete offset is known to be initialized.
    pub fn is_byte_init(&self, alloc_id: AllocId, offset: usize) -> bool {
        self.bytes.get(&(alloc_id, offset)).is_some_and(|b| b.init)
    }

    /// Check whether a byte at a concrete offset is known to be NUL.
    pub fn is_byte_nul(&self, alloc_id: AllocId, offset: usize) -> bool {
        self.bytes.get(&(alloc_id, offset)).is_some_and(|b| b.nul == Some(true))
    }

    /// Check whether a byte at a concrete offset is known to be non-NUL.
    pub fn is_byte_non_nul(&self, alloc_id: AllocId, offset: usize) -> bool {
        self.bytes.get(&(alloc_id, offset)).is_some_and(|b| b.nul == Some(false))
    }

    /// Return all known (offset, term) pairs for an allocation, sorted by offset.
    pub fn alloc_byte_values(&self, alloc_id: AllocId) -> Vec<(usize, &Int<'ctx>)> {
        let mut pairs: Vec<_> = self
            .bytes
            .iter()
            .filter_map(|((aid, off), byte)| {
                if *aid == alloc_id { byte.value.as_ref().map(|term| (*off, term)) } else { None }
            })
            .collect();
        pairs.sort_by_key(|(off, _)| *off);
        pairs
    }

    /// Collect all offsets known to be NUL in an allocation.
    pub fn alloc_nul_offsets(&self, alloc_id: AllocId) -> Vec<usize> {
        self.bytes.iter()
            .filter_map(|((aid, off), byte)| {
                if *aid == alloc_id && byte.nul == Some(true) { Some(*off) } else { None }
            })
            .collect()
    }

    /// Collect all offsets known to be non-NUL in an allocation.
    pub fn alloc_non_nul_offsets(&self, alloc_id: AllocId) -> Vec<usize> {
        self.bytes.iter()
            .filter_map(|((aid, off), byte)| {
                if *aid == alloc_id && byte.nul == Some(false) { Some(*off) } else { None }
            })
            .collect()
    }

    /// Copy all per-byte tracking (value, init, NUL knowledge) from one
    /// allocation to another.
    pub(crate) fn copy_byte_tracking(&mut self, src: AllocId, dst: AllocId) {
        let infos: Vec<(usize, ByteInfo<'ctx>)> = self.bytes.iter()
            .filter(|((aid, _), _)| *aid == src)
            .map(|((_, off), byte)| (*off, byte.clone()))
            .collect();
        for (off, byte) in infos {
            self.bytes.insert((dst, off), byte);
        }
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
                let alloc = self.alloc(prov.alloc_id);
                let expected = Int::add(self.ctx, &[&alloc.base, &prov.offset]);
                solver.assert(&value.term._eq(&expected));
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
                let alloc = self.alloc(prov.alloc_id);
                let expected = Int::add(self.ctx, &[&alloc.base, &prov.offset]);
                solver.assert(&value.term._eq(&expected));
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
            .field("definitions", &self.definition_count)
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
                let int_val = crate::helpers::mir_utils::const_scalar_int(self.tcx, &constant.const_, &text);
                let is_field_offset = int_val.is_none()
                    && crate::helpers::mir_utils::offset_of_container(self.tcx, &constant.const_)
                        .is_some();
                let term = if let Some(v) = int_val {
                    if v < 0 {
                        Int::from_i64(self.ctx, v as i64)
                    } else {
                        Int::from_u64(self.ctx, v as u64)
                    }
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
                    invariants: ValueInvariants {
                        is_field_offset,
                        ..ValueInvariants::default()
                    },
                }
            }
            #[cfg(rapx_ge_99)]
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

