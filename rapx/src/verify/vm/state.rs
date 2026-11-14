//! Symbolic VM state types.
//!
//! The data structures that represent the symbolic execution state: symbolic
//! values and their invariants, memory allocations, and the full execution
//! state at a program point.

use crate::helpers::mir_utils;
use rustc_abi::VariantIdx;
use rustc_hir::def_id::DefId;
#[cfg(rapx_const_ext)]
use rustc_middle::ty::consts::ConstExt;
use rustc_middle::{
    mir::{Body, ConstValue, Local, Operand, Place, ProjectionElem},
    ty::{Region, Ty, TyCtxt, TyKind, TypingEnv},
};
use rustc_span::Span;
use std::cell::RefCell;
use z3::{
    Context, SatResult, Solver,
    ast::{Array, Ast, Bool, Dynamic, Int},
};

use crate::compat::{FxHashMap, FxHashSet};
use super::{
    diagnostics::Diagnostics,
    method_cache::{CachedMethodResult, MethodSnapshot},
};
use crate::helpers::def_use::PlaceKey;

pub(crate) const REPEATED_ARRAY_ELEMENT: usize = usize::MAX;

/// Unique identifier for a heap or stack allocation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct AllocId(pub usize);

/// Memory events consumed by SafeDrop; normal drops locate later violations.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SafeDropEventKind {
    Drop,
    DoubleFree,
    UseAfterFree,
    DanglingPointer,
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct SafeDropEvent {
    pub alloc_id: AllocId,
    pub kind: SafeDropEventKind,
    pub block: Option<usize>,
    pub local: usize,
    pub span: Span,
}
/// The structure of a pointer's byte offset, when it has one.
///
/// Each variant lets the verifier use a cheaper, more precise proof: `Field`
/// carries the "field in-bounds" guarantee (`offset + size_of(field) <=
/// size_of(container)`, e.g. `Option::as_slice`), and `Element(k)` tracks the
/// element index so `InBound` checks `k + count <= slice_len` linearly instead
/// of the non-linear byte form `(k+count)·S <= len·S` (undecidable in Z3 NIA
/// for a generic `S`).
#[derive(Clone, Debug)]
pub(crate) enum OffsetKind<'z3> {
    /// Compile-time field offset (`offset_of!`), including a first field at 0.
    Field,
    /// Element index and byte stride from pointer arithmetic. The byte offset
    /// is `index · stride`.
    Element { index: Int<'z3>, stride: Int<'z3> },
    /// A byte-strided or otherwise unclassifiable offset (`byte_add`).
    Byte,
}

/// Pointer provenance: which allocation, at what byte offset, and (when known)
/// what structure that offset has.
#[derive(Clone, Debug)]
pub(crate) struct Provenance<'z3> {
    /// The allocation this pointer derives from.
    pub alloc_id: AllocId,
    /// Byte offset from the allocation base; zero for a base pointer.
    pub offset: Int<'z3>,
    /// Known structure of the offset; `None` denotes an unclassified base offset.
    pub offset_kind: Option<OffsetKind<'z3>>,
}

/// Value-level facts about a single symbolic value (nullness, alignment,
/// bounds, and whether it has been written).  These travel *with* the value — a
/// [`VmValue`] leaves its allocation when passed as an operand or stashed in
/// `InlineCtx::deferred_field_writes` — so they live on the value, not the
/// allocation.  The allocation-level counterpart to `init` is
/// [`ContentFacts::initialized`], kept in sync by [`VmState::mark_initialized`].
///
/// `PartialEq`/`Eq` are deliberately *not* derived: `align_n` is a Z3 AST
/// whose equality is structural (`Z3_is_eq_ast`), not semantic, so comparing
/// two `ValueFacts` would silently report semantically-equal values as
/// unequal.
#[derive(Clone, Debug, Default)]
pub(crate) struct ValueFacts<'z3> {
    pub non_null: bool,
    pub dangling: bool,
    pub init: bool,
    pub in_bounds: bool,
    /// Known divisor `n` for which `z3_term % n == 0`, possibly symbolic.
    pub align_n: Option<Int<'z3>>,
    /// Identity of an ownership transfer carried by this pointer and its copies.
    pub ownership_transfer: Option<usize>,
}

/// A symbolic value tracked by the VM.
///
/// # Semantics of `z3_term`
///
/// - For pointer/reference types (`&T`, `*const T`, `*mut T`, `Box<T>`, etc.):
///   `z3_term` represents the **address** in the VM's logical address space.
/// - For scalar types (integers, `bool`, `char`): `z3_term` represents the **value**.
/// - For aggregate types (struct, tuple, enum): `z3_term` is the base address of
///   the stack allocation backing the aggregate.
///
/// When `provenance` is `Some`, the following relationship holds and is
/// asserted into the solver at check time:
///   `z3_term == alloc[provenance.alloc_id].base + provenance.offset`
#[derive(Clone, Debug)]
pub(crate) struct VmValue<'z3, 'tcx> {
    /// Symbolic address or scalar value, according to `ty`.
    pub z3_term: Int<'z3>,
    pub ty: Ty<'tcx>,
    /// Allocation origin and offset, when this is a pointer.
    pub provenance: Option<Provenance<'z3>>,
    pub facts: ValueFacts<'z3>,
    /// Semantic origin used by guard and arithmetic reasoning.
    pub source: ValueSource<'z3>,
}

impl<'z3, 'tcx> VmValue<'z3, 'tcx> {
    pub(crate) fn new(term: Int<'z3>, ty: Ty<'tcx>) -> Self {
        VmValue {
            z3_term: term,
            ty,
            provenance: None,
            facts: ValueFacts::default(),
            source: ValueSource::None,
        }
    }

    /// Convenience: extract the `AllocId` from provenance, if any.
    pub(crate) fn provenance_alloc_id(&self) -> Option<AllocId> {
        self.provenance.as_ref().map(|p| p.alloc_id)
    }

    /// Symbolic enum discriminant, if known.
    pub(crate) fn discriminant(&self) -> Option<&Int<'z3>> {
        match &self.source {
            ValueSource::KnownDiscriminant(d) => Some(d),
            _ => None,
        }
    }

    /// Direct boolean condition of a comparison result, if any.
    pub(crate) fn bool_cond(&self) -> Option<&Bool<'z3>> {
        match &self.source {
            ValueSource::Comparison { cond, .. } => Some(cond),
            _ => None,
        }
    }

    /// Whether this scalar is a compile-time `offset_of!` field offset.
    pub(crate) fn is_field_offset(&self) -> bool {
        matches!(self.source, ValueSource::FieldOffset)
    }

    /// Whether this value is a pointer (carries provenance).
    pub(crate) fn is_pointer(&self) -> bool {
        self.provenance.is_some()
    }
}

/// The shape of an allocation: a single object, a slice/array buffer, or an
/// external raw-pointer parameter.  `element_ty` (typed vs untyped) and the
/// `parent` sub-view edge stay separate fields.
#[derive(Clone, Debug)]
pub(crate) enum AllocKind<'z3> {
    /// A single object: a `Box<T>` heap object, a struct, a scalar, or an
    /// untyped raw buffer.
    Object,
    /// A slice/array buffer with a known element count.
    Slice {
        len: Int<'z3>,
    },
    /// An external raw-pointer parameter. `size` is an unconstrained symbolic
    /// term (the caller may pass any allocation); nullability is *not* stored
    /// here — it is tracked via the pointer term (`term == 0`) path conditions.
    External,
    ExternalSlice {
        len: Int<'z3>,
    },
}

/// The element type of an allocation's contents, either a concrete [`Ty`] or
/// symbolic (`Generic`).
///
/// `Typed` carries a concrete `Ty` — the element type of a slice, the object
/// type of a `Box<T>`/struct, or `u8` for a raw byte buffer — while `Generic`
/// marks a symbolic element type whose concrete `Ty` cannot be determined
/// (e.g. `from_raw_parts::<T>`; its `size` uses the shared symbolic `sizeof_T`
/// and its length must be materialized via `set_slice_len`).
#[derive(Clone, Debug)]
pub(crate) enum ElementTy<'tcx> {
    Typed(Ty<'tcx>),
    Generic,
}

impl<'tcx> ElementTy<'tcx> {
    /// The concrete type, if known.
    pub(crate) fn as_ty(&self) -> Option<Ty<'tcx>> {
        match self {
            ElementTy::Typed(t) => Some(*t),
            ElementTy::Generic => None,
        }
    }

    /// Whether the element type is symbolic/unknown (no concrete `Ty`).
    pub(crate) fn is_generic(&self) -> bool {
        matches!(self, ElementTy::Generic)
    }
}

impl<'tcx> From<Option<Ty<'tcx>>> for ElementTy<'tcx> {
    fn from(o: Option<Ty<'tcx>>) -> Self {
        match o {
            Some(t) => ElementTy::Typed(t),
            None => ElementTy::Generic,
        }
    }
}

/// Uniform facts about the *pointer elements* of a container, established by
/// `x.iter()` for_each invariants.
///
/// Each fact is a property every element pointer satisfies. The facts are
/// anchored to the container allocation, separate from its storage layout.
#[derive(Clone, Debug, Default)]
pub(crate) struct ForEachFacts<'z3, 'tcx> {
    /// `Typed(iter(), T)`: every element pointer points at a valid `T`.
    pub target_ty: Option<Ty<'tcx>>,
    /// `Align(iter(), T)`: every element pointer is aligned to `align_of(T)`.
    pub aligned_ty: Option<Ty<'tcx>>,
    /// `Allocated(iter(), T, n)`: every element pointer backs `>= n` `T`
    /// elements (`n` may be symbolic).
    pub allocated: Option<(Ty<'tcx>, Int<'z3>)>,
    /// `Owning(iter())` is trusted; alias validation is handled separately.
    pub owning: bool,
}

/// Per-allocation *lifecycle* facts (`dead`/`liveness`/`for_each`), kept apart
/// from the allocation's shape metadata and `parent` edge so identity/layout
/// and facts are separated at the type level.  The *content* facts
/// (readability, C-string/UTF-8 trust) live on [`ContentFacts`] instead.
#[derive(Clone, Debug, Default)]
pub(crate) struct AllocFacts<'z3, 'tcx> {
    /// Whether the allocation has been freed (StorageDead / Drop).
    pub dead: bool,
    /// Whether an opaque callback may have freed this allocation.
    pub callback_may_drop: bool,
    /// A destructor may have freed this allocation.
    pub drop_may_free: bool,
    /// Pointer term licensed by an `Owning` precondition.
    pub owning: Option<Int<'z3>>,
    /// Whether this allocation was created in the analyzed function.
    pub locally_allocated: bool,
    /// Assumed live region for external allocations; `None` grants no lifetime.
    pub liveness: Option<Region<'tcx>>,
    /// Facts shared by all pointer elements of this allocation.
    pub for_each: ForEachFacts<'z3, 'tcx>,
    /// `(address, type)` spans licensed by `InBound` contracts.
    pub bounded_spans: Vec<(Int<'z3>, Ty<'tcx>)>,
    /// Byte ranges established by explicit allocation/bounds contracts.
    /// Each entry is (start address, byte count), not a whole-allocation extent.
    pub bounded_ranges: Vec<(Int<'z3>, Int<'z3>)>,
}

/// Per-allocation *content* facts: whether the allocation's contents are
/// readable (initialized), whether they were asserted to be a valid C string /
/// UTF-8, and whether they were licensed for `SplitTransmute` re-interpretation.
/// These describe the stored bytes/values, so they live on [`MemoryContent`]
/// next to that data, rather than on [`AllocFacts`] (lifecycle).
#[derive(Clone, Debug, Default)]
pub(crate) struct ContentFacts<'tcx> {
    /// Whether the allocation contains a readable value.
    pub initialized: bool,
    /// Whether some explored branch may leave this allocation uninitialized.
    pub may_be_uninit: bool,
    /// Whether the inner `T` is still uninitialized after `MaybeUninit::uninit`.
    pub inner_uninit: bool,
    /// Type of a complete initialized write at offset zero; cleared by invalidating writes.
    pub written_pointee_ty: Option<Ty<'tcx>>,
    /// Trusted `ValidCStr` contract or invariant evidence.
    pub cstr_trusted: bool,
    /// Trusted `ValidString` contract evidence.
    pub utf8_trusted: bool,
    /// Destination element type licensed by `SplitTransmute`; `None` grants none.
    pub split_transmute_to: Option<Ty<'tcx>>,
}

/// A memory allocation: a stack local, a heap object (`Box`/`Vec`), or an
/// external raw-pointer placeholder.
///
/// The allocation is stored in a [`MemoryUnit`] at index `AllocId.0` (an
/// `AllocId` is a monotonic counter that doubles as the vector index).
#[derive(Clone, Debug)]
pub(crate) struct Allocation<'z3, 'tcx> {
    /// Symbolic base address.
    pub base: Int<'z3>,
    /// Size in bytes, possibly symbolic.
    pub size: Int<'z3>,
    /// Alignment in bytes, possibly symbolic for a generic type.
    pub align: Int<'z3>,
    /// Element type of the stored object or slice.
    pub element_ty: ElementTy<'tcx>,
    /// Object, slice, or external allocation shape.
    pub kind: AllocKind<'z3>,
    /// Allocation lifecycle and ownership facts.
    pub facts: AllocFacts<'z3, 'tcx>,
    /// Source allocation of a view; followed to find its aliasing root.
    pub parent: Option<AllocId>,
}

impl<'z3, 'tcx> Allocation<'z3, 'tcx> {
    /// Construct a fresh allocation with all live/dead/invariant flags in
    /// their initial state.
    pub(crate) fn new(
        base: Int<'z3>,
        size: Int<'z3>,
        align: Int<'z3>,
        element_ty: Option<Ty<'tcx>>,
        kind: AllocKind<'z3>,
    ) -> Self {
        Allocation {
            base,
            size,
            align,
            element_ty: element_ty.into(),
            kind,
            facts: AllocFacts::default(),
            parent: None,
        }
    }

    /// Whether this allocation models an external raw-pointer parameter.
    pub(crate) fn is_external(&self) -> bool {
        matches!(
            self.kind,
            AllocKind::External | AllocKind::ExternalSlice { .. }
        )
    }

    /// Legacy external-allocation placeholder, not evidence of a byte extent.
    pub(crate) fn has_unbounded_size(&self) -> bool {
        self.is_external() && self.size.simplify().as_u64() == Some(i64::MAX as u64)
    }

    /// The slice/array element count, if this allocation is slice data.
    ///
    /// Invariant: `size == len * sizeof(element_ty)` is maintained by the
    /// callers that call [`Self::set_slice_len`] (they compute `size` from the
    /// same `len` and push the equality as a path condition); it is *not*
    /// enforced here. `slice_len_from_value` falls back to `size / elem_size`
    /// when the length was never materialized.
    pub(crate) fn slice_len(&self) -> Option<&Int<'z3>> {
        match &self.kind {
            AllocKind::Slice { len } | AllocKind::ExternalSlice { len } => Some(len),
            _ => None,
        }
    }

    /// Mark this allocation as slice data with the given element count.
    /// Callers must keep `size == len * sizeof(element_ty)` consistent.
    pub(crate) fn set_slice_len(&mut self, len: Int<'z3>) {
        self.kind = if self.is_external() {
            AllocKind::ExternalSlice { len }
        } else {
            AllocKind::Slice { len }
        };
    }
}

/// Scratch state shared by recursive inlining and path replay.
/// Recursive inlining saves caller bindings on the Rust call stack; path replay
/// saves them with the caller frame in [`SavedCallerFrame`].
///
/// # Deferring `&mut` writes across the inline frame
///
/// While the callee runs, the caller's `local_alloc` (the name → allocation
/// binding) is parked in the saved [`FrameState`], so a write through a `&mut`
/// argument cannot resolve the caller referent local by address and land in its
/// field values immediately.  `arg_referents` pre-resolves (before `enter_frame`)
/// which caller local each `&mut` argument points at, and `deferred_field_writes`
/// collects the writes to replay once the caller is restored:
///
/// ```text
/// struct Foo { field: i32 }
/// fn bar(foo: &mut Foo) { foo.field = 1; }   // inlined callee
/// fn main() {
///     let mut x = Foo { field: 0 };
///     bar(&mut x);                            // inline `bar`
/// }
/// ```
///
/// 1. Enter `bar`: `enter_frame` parks `main`'s local_alloc; `arg_referents[0] = x`.
/// 2. Run `bar`: `foo.field = 1` (`(*foo).field`) can no longer resolve `x` by
///    address (the caller's address map is gone), so it pushes `(x, [0], 1)`.
/// 3. Exit `bar`: `restore_frame` brings `main`'s local_alloc back, then the deferred
///    write is replayed, giving `x.field == 1`.
#[derive(Default, Clone)]
pub(crate) struct InlineCtx<'z3, 'tcx> {
    /// Recursive inlining depth, bounded by `MAX_INLINE_DEPTH`.
    pub inline_depth: usize,
    pub symbolic_generic_const_inline: bool,
    /// Terms from depth-limited calls; dependent checks become `Unknown`.
    pub inline_truncated_terms: FxHashSet<Int<'z3>>,
    pub inline_branch_terms: FxHashSet<Int<'z3>>,
    pub pending_states: Vec<Box<VmState<'z3, 'tcx>>>,
    pub opaque_intrinsic_terms: FxHashSet<Int<'z3>>,
    /// Caller referent local for each inlined callee argument.
    pub arg_referents: Vec<Option<Local>>,
    /// `(caller local, field path, value)` writes replayed after frame restoration.
    pub deferred_field_writes: Vec<(Local, Vec<usize>, VmValue<'z3, 'tcx>)>,
}

/// The extra semantics attached to a value, beyond its term/type/provenance.
///
/// A single value carries at most one of these: it is either a plain value, an
/// `offset_of!` field offset, a symbolic enum discriminant, a comparison
/// result, or a non-comparison binary-op result.  The operands/operator are
/// used for guard inference (tracing a switch/assert guard back to the pointer
/// it null-checks/alignment-checks) and division-axiom injection (following
/// dataflow edges to reach `Div`/`Rem` results).
#[derive(Clone, Debug)]
pub(crate) enum ValueSource<'z3> {
    /// No extra semantics.
    None,
    /// A literal bound to an inlined callee parameter at this call site.
    CallsiteConst,
    /// The stored scalar value of a shared primitive reference parameter.
    SharedScalarReferent,
    /// Bytes carried by a constant byte-array reference through generic calls.
    ConstBytes(Vec<u8>),
    /// Length metadata carried by a slice pointer or reference.
    SliceLen(Int<'z3>),
    /// A compile-time `offset_of!` field offset.
    FieldOffset,
    FieldBorrow {
        base: Local,
        fields: Vec<usize>,
    },
    /// A known enum discriminant.
    KnownDiscriminant(Int<'z3>),
    /// A comparison result (`Eq`/`Ne`/`Le`/`Lt`/`Ge`/`Gt`): the operands and
    /// the direct boolean condition (`offset <= len`) carried alongside the
    /// ite-encoded term.
    Comparison {
        lhs: Option<PlaceKey>,
        rhs: Option<PlaceKey>,
        op: rustc_middle::mir::BinOp,
        cond: Bool<'z3>,
    },
    /// A non-comparison binary-op result (`Add`/`Sub`/…/`Div`/`Rem`): the
    /// operands and operator.
    BinaryOp {
        lhs: Option<PlaceKey>,
        rhs: Option<PlaceKey>,
        op: rustc_middle::mir::BinOp,
    },
}

impl<'z3> ValueSource<'z3> {
    /// The `(lhs, rhs, op)` of a binary-op/comparison result, if this value is
    /// one.
    pub(crate) fn operands(
        &self,
    ) -> Option<(
        &Option<PlaceKey>,
        &Option<PlaceKey>,
        rustc_middle::mir::BinOp,
    )> {
        match self {
            ValueSource::Comparison { lhs, rhs, op, .. } => Some((lhs, rhs, *op)),
            ValueSource::BinaryOp { lhs, rhs, op } => Some((lhs, rhs, *op)),
            _ => None,
        }
    }

    /// Just the field-offset part of this source: `FieldOffset` if it is one,
    /// otherwise `None`.
    pub(crate) fn field_offset_only(&self) -> ValueSource<'z3> {
        match self {
            ValueSource::FieldOffset => ValueSource::FieldOffset,
            _ => ValueSource::None,
        }
    }
}

/// A single allocation: its shape metadata ([`Allocation`]) plus its contents
/// ([`MemoryContent`]).  Splitting the two keeps the identity/layout facts apart
/// from the mutable memory the values live in, while colocating them in one
/// unit so no parallel table can drift out of sync.  Facts live in three
/// anchored layers — lifecycle ([`AllocFacts`]), content ([`ContentFacts`]),
/// and value ([`ValueFacts`] on each [`VmValue`]) — see each type's doc.
#[derive(Clone)]
pub(crate) struct MemoryUnit<'z3, 'tcx> {
    pub(crate) allocation: Allocation<'z3, 'tcx>,
    pub(crate) content: MemoryContent<'z3, 'tcx>,
}

/// The per-allocation byte and typed-value layers. Typed values use a view type
/// so fields from different casts do not collide. Unwritten bytes read as the
/// `UNINIT` sentinel.
#[derive(Default, Clone)]
pub(crate) struct MemoryContent<'z3, 'tcx> {
    /// Symbolic byte array; absent until the first byte write.
    pub(crate) byte_array: Option<Array<'z3>>,
    /// Concrete written byte offsets; symbolic writes update only `byte_array`.
    pub(crate) byte_written: FxHashSet<usize>,
    /// Typed values keyed by view type and field path; `[]` is the whole value.
    pub(crate) values: FxHashMap<(Ty<'tcx>, Vec<usize>), VmValue<'z3, 'tcx>>,
    /// `(address, type)` facts established by `Typed` contracts.
    pub(crate) typed_facts: FxHashSet<(Int<'z3>, Ty<'tcx>)>,
    pub(crate) indexed_elements: Vec<(Int<'z3>, VmValue<'z3, 'tcx>)>,
    pub(crate) indexed_elements_modified: bool,
    pub(crate) copied_prefix: Option<(Ty<'tcx>, Int<'z3>)>,
    pub(crate) facts: ContentFacts<'tcx>,
}

impl MemoryContent<'_, '_> {
    pub(crate) fn clear_byte_writes(&mut self) {
        self.byte_array = None;
        self.byte_written.clear();
    }
}

/// Accumulated solver state for the current path.
///
/// `assertions` is the assertion stream fed to Z3; `term_caches` holds the
/// per-phenomenon term-provenance caches that keep expressions compact and
/// linear.  Everything is path-scoped and monotonic: it accumulates as the VM
/// steps and is never reset within a path (or across inlined frames).
#[derive(Default, Clone)]
pub(crate) struct Constraints<'z3, 'tcx> {
    /// Path conditions, call preconditions, and layout facts asserted to Z3.
    pub(crate) assertions: Vec<Bool<'z3>>,
    /// Path-scoped term provenance caches used to keep expressions compact.
    pub(crate) term_caches: TermCaches<'z3, 'tcx>,
}

/// Term-provenance caches, one per phenomenon the VM must shape by hand.
///
/// Z3's nonlinear integer solver (NIA) cannot rewrite degree-3 products or
/// deeply-nested pointer chains, so the VM records the *semantic meaning* of a
/// symbol (what it divides, which iterator it indexes, …) and uses that
/// provenance later to emit a compact, degree-≤2 term instead.  Each cache is
/// independent — they share only the path-scoped, monotonic lifetime.
#[derive(Default, Clone)]
pub(crate) struct TermCaches<'z3, 'tcx> {
    /// Shared symbolic `sizeof_T` term for each generic type.
    pub(crate) sizes: FxHashMap<Ty<'tcx>, Int<'z3>>,
    /// Positive size terms already proved on this path. Assertions only accumulate.
    pub(crate) non_zst: FxHashSet<Int<'z3>>,
    /// Shared symbolic `align_T` term for each generic type.
    pub(crate) aligns: FxHashMap<Ty<'tcx>, Int<'z3>>,
    /// Bitwise `Not` terms used to recognize alignment masks.
    pub(crate) not_mask_terms: FxHashSet<Int<'z3>>,
    /// Exact-division quotient mapped to its dividend for later bound proofs.
    pub(crate) exact_div_roots: FxHashMap<Int<'z3>, Int<'z3>>,
    /// Non-exact quotient mapped to its dividend and divisor.
    pub(crate) div_roots: FxHashMap<Int<'z3>, (Int<'z3>, Int<'z3>)>,
    /// Iterator offset and optional length, keyed by backing buffer and pointer.
    pub(crate) iter_ptr_offset:
        FxHashMap<(AllocId, Int<'z3>), (AllocId, Int<'z3>, Option<Int<'z3>>)>,
    /// Shared byte-array sentinel outside the `u8` range.
    pub(crate) uninit_byte: Option<Int<'z3>>,
}

/// The frame-scoped subset of [`VmState`]: the name → allocation binding keyed
/// by MIR `Local`, which the callee reuses, so it must be swapped out for the
/// duration of an inlined callee and swapped back afterwards.
#[derive(Clone)]
pub(crate) struct FrameState<'tcx> {
    /// Function executed by this frame.
    pub(crate) current_def_id: DefId,
    /// Optimized MIR with this frame's selected generic arguments substituted, if available.
    pub(crate) instantiated_body: Option<&'tcx Body<'tcx>>,
    /// Stack allocation backing each MIR local and its field values.
    pub(crate) local_alloc: FxHashMap<Local, AllocId>,
    /// Enum variant and payload fields assembled before `SetDiscriminant`.
    pub(crate) pending_enum_fields: FxHashMap<Local, (VariantIdx, FxHashSet<usize>)>,
}

/// Caller state parked during a path-replay call, including its method snapshot.
#[derive(Clone)]
pub(crate) struct SavedCallerFrame<'z3, 'tcx> {
    /// Caller MIR frame restored when the inlined callee returns.
    pub(crate) frame: FrameState<'tcx>,
    /// Call snapshot used to cache a stable return value.
    pub(crate) method_call: Option<MethodSnapshot<'z3, 'tcx>>,
    /// Caller locals used to bind trait-method `ensures` after inlining.
    pub(crate) postcondition_args: Vec<Option<Local>>,
    /// Caller frame's argument referents restored on return.
    pub(crate) arg_referents: Vec<Option<Local>>,
    /// Caller frame's pending field writes restored on return.
    pub(crate) deferred_writes: Vec<(Local, Vec<usize>, VmValue<'z3, 'tcx>)>,
}

/// Optional memory diagnostics collected along one execution path.
#[derive(Clone, Default)]
pub(crate) struct SafeDropEventLog {
    events: Option<RefCell<Vec<SafeDropEvent>>>,
}

impl SafeDropEventLog {
    pub(crate) fn enable(&mut self) {
        self.events.get_or_insert_with(RefCell::default);
    }

    pub(crate) fn is_enabled(&self) -> bool {
        self.events.is_some()
    }

    pub(crate) fn len(&self) -> usize {
        self.events.as_ref().map_or(0, |events| events.borrow().len())
    }

    pub(crate) fn push(&self, event: SafeDropEvent) {
        if let Some(events) = &self.events {
            events.borrow_mut().push(event);
        }
    }

    pub(crate) fn events(&self) -> std::cell::Ref<'_, Vec<SafeDropEvent>> {
        self.events.as_ref().expect("SafeDrop event log is disabled").borrow()
    }
}

/// A transferable ownership share. Copies of its pointer use the same entry.
#[derive(Clone)]
pub(crate) struct OwnershipTransfer {
    alloc_id: AllocId,
    owner: DefId,
    available: usize,
}

/// The full symbolic execution state at a program point.
///
/// Accumulates the name → allocation bindings, allocations, and solver
/// constraints as the VM steps through retained MIR items. The Z3 context is
/// borrowed so a single context can be reused across property checks.
#[derive(Clone)]
pub(crate) struct VmState<'z3, 'tcx> {
    /// Function being verified, retained while inlined callee frames execute.
    target_def_id: DefId,
    /// Target MIR instantiated with a selected trait-bound implementor when an
    /// unresolved, unmodeled generic trait call needs a concrete method target.
    /// `None` uses the original optimized MIR, even for generic functions.
    instantiated_target_body: Option<&'tcx Body<'tcx>>,
    /// Shared Z3 context.
    pub(crate) z3_ctx: &'z3 Context,
    /// Compiler type context.
    pub(crate) tcx: TyCtxt<'tcx>,
    /// Currently executing MIR frame and its local allocation bindings.
    pub(crate) current_frame: FrameState<'tcx>,
    /// Caller frames saved by path-replay inlining.
    pub(super) caller_frames: Vec<SavedCallerFrame<'z3, 'tcx>>,
    /// Allocation units indexed by `AllocId`.
    pub(super) units: Vec<MemoryUnit<'z3, 'tcx>>,
    /// Ownership transfers shared by copies of the same raw pointer.
    ownership_transfers: Vec<OwnershipTransfer>,
    /// Stable allocation for each thread-local static across MIR locals and frames.
    pub(super) thread_local_allocs: FxHashMap<DefId, AllocId>,
    /// Path conditions and term caches.
    pub(crate) constraints: Constraints<'z3, 'tcx>,
    /// Scratch state for recursive inlining.
    pub(crate) inline: InlineCtx<'z3, 'tcx>,
    /// Stable `&self` results reused by contracts only when the method, caller,
    /// receiver allocation and offset, fields, and slice length still match.
    pub(super) method_result_cache: Vec<CachedMethodResult<'z3, 'tcx>>,
    /// Allocation roots licensed by declared `Alias` contract sources.
    pub(super) alias_hazard_allocs: FxHashSet<AllocId>,
    /// Slice and index terms with their originating MIR locals.
    pub(crate) index_access_facts: Vec<(Int<'z3>, Int<'z3>, Local, Local)>,
    /// Optional SafeDrop log of drops, use-after-free, and dangling pointers.
    pub(crate) safedrop_events: SafeDropEventLog,
    /// Path diagnostics and the MIR location used to attribute new records.
    pub(crate) diagnostics: Diagnostics,
}

impl<'z3, 'tcx> VmState<'z3, 'tcx> {
    pub(crate) fn ownership_share(&self, value: &VmValue<'z3, 'tcx>, owner: DefId) -> Option<usize> {
        let transfer = self.ownership_transfers.get(value.facts.ownership_transfer?)?;
        (transfer.owner == owner
            && value
                .provenance_alloc_id()
                .is_some_and(|id| self.root_alloc(id) == transfer.alloc_id))
        .then_some(transfer.available)
    }

    pub(crate) fn has_available_transfer(&self, alloc_id: AllocId) -> bool {
        let root = self.root_alloc(alloc_id);
        self.ownership_transfers
            .iter()
            .any(|transfer| transfer.alloc_id == root && transfer.available > 0)
    }

    pub(crate) fn begin_ownership_transfer(&mut self, local: Local, owner: DefId) {
        let Some(alloc_id) = self.local_value(local).and_then(|value| value.provenance_alloc_id()) else {
            return;
        };
        let id = self.ownership_transfers.len();
        self.ownership_transfers.push(OwnershipTransfer {
            alloc_id: self.root_alloc(alloc_id),
            owner,
            available: 1,
        });
        if let Some(mut value) = self.local_value(local).cloned() {
            value.facts.ownership_transfer = Some(id);
            self.set_local(local, value);
        }
    }

    pub(crate) fn grant_ownership_share(&mut self, value: &VmValue<'z3, 'tcx>, owner: DefId) {
        if self.ownership_share(value, owner).is_some()
            && let Some(id) = value.facts.ownership_transfer
        {
            self.ownership_transfers[id].available += 1;
        }
    }

    pub(crate) fn consume_ownership_share(
        &mut self,
        value: &VmValue<'z3, 'tcx>,
        owner: DefId,
        may_free: bool,
    ) {
        if self.ownership_share(value, owner).is_some()
            && let Some(id) = value.facts.ownership_transfer
        {
            self.ownership_transfers[id].available =
                self.ownership_transfers[id].available.saturating_sub(1);
        }
        if may_free && let Some(alloc_id) = value.provenance_alloc_id() {
            self.alloc_mut(self.root_alloc(alloc_id)).facts.drop_may_free = true;
        }
    }

    pub(crate) fn record_memory_drop(&mut self, alloc_id: AllocId, local: Local) {
        if self.safedrop_events.is_enabled() {
            self.safedrop_events.push(SafeDropEvent {
                alloc_id,
                kind: if self.alloc(alloc_id).facts.dead {
                    SafeDropEventKind::DoubleFree
                } else {
                    SafeDropEventKind::Drop
                },
                block: self.diagnostics.active_mir.as_ref().map(|location| location.block),
                local: local.as_usize(),
                span: self
                    .diagnostics.active_mir
                    .as_ref()
                    .map(|location| location.span)
                    .unwrap_or(rustc_span::DUMMY_SP),
            });
        }
        self.alloc_mut(alloc_id).facts.dead = true;
    }

    pub(crate) fn record_memory_use(&self, alloc_id: AllocId, local: Local) {
        if self.safedrop_events.is_enabled() && self.alloc(alloc_id).facts.dead {
            self.safedrop_events.push(SafeDropEvent {
                alloc_id,
                kind: SafeDropEventKind::UseAfterFree,
                block: self.diagnostics.active_mir.as_ref().map(|location| location.block),
                local: local.as_usize(),
                span: self
                    .diagnostics.active_mir
                    .as_ref()
                    .map(|location| location.span)
                    .unwrap_or(rustc_span::DUMMY_SP),
            });
        }
    }

    pub(crate) fn scalar_bits_term(&self, ty: Ty<'tcx>, bits: u128) -> Option<Int<'z3>> {
        let bytes = self.size_of_ty(ty);
        if bytes == 0 || bytes > 16 {
            return None;
        }
        if bytes == 16 {
            let two_64 = Int::add(
                self.z3_ctx,
                &[
                    &Int::from_u64(self.z3_ctx, u64::MAX),
                    &Int::from_u64(self.z3_ctx, 1),
                ],
            );
            let unsigned = self.u128_term(bits);
            return if matches!(ty.kind(), TyKind::Int(_)) && bits >> 127 != 0 {
                let two_128 = Int::mul(self.z3_ctx, &[&two_64, &two_64]);
                Some(Int::sub(self.z3_ctx, &[&unsigned, &two_128]))
            } else {
                Some(unsigned)
            };
        }
        let width = bytes * 8;
        if matches!(ty.kind(), TyKind::Int(_)) {
            let shift = 64 - width;
            let signed = ((bits as u64) << shift) as i64 >> shift;
            Some(Int::from_i64(self.z3_ctx, signed))
        } else {
            u64::try_from(bits)
                .ok()
                .map(|unsigned| Int::from_u64(self.z3_ctx, unsigned))
        }
    }

    pub(crate) fn u128_term(&self, value: u128) -> Int<'z3> {
        let low = Int::from_u64(self.z3_ctx, value as u64);
        if value <= u64::MAX as u128 {
            return low;
        }
        let high = Int::from_u64(self.z3_ctx, (value >> 64) as u64);
        let two_64 = Int::add(
            self.z3_ctx,
            &[
                &Int::from_u64(self.z3_ctx, u64::MAX),
                &Int::from_u64(self.z3_ctx, 1),
            ],
        );
        Int::add(
            self.z3_ctx,
            &[&Int::mul(self.z3_ctx, &[&high, &two_64]), &low],
        )
    }

    pub(crate) fn enum_discriminant_term(
        &self,
        ty: Ty<'tcx>,
        variant: VariantIdx,
    ) -> Option<Int<'z3>> {
        let TyKind::Adt(adt, _) = ty.kind() else {
            return None;
        };
        if !adt.is_enum() {
            return None;
        }
        let discr = adt.discriminant_for_variant(self.tcx, variant);
        self.scalar_bits_term(discr.ty, discr.val)
    }

    /// Create a fresh VM state for executing a path.
    pub(crate) fn new(
        z3_ctx: &'z3 Context,
        tcx: TyCtxt<'tcx>,
        target_def_id: DefId,
        instantiated_target_body: Option<&'tcx Body<'tcx>>,
    ) -> Self {
        // The `UNINIT` sentinel is created once and shared by every byte array:
        // an unwritten offset reads it back, so `select != UNINIT` decides
        // whether a byte was written.
        let mut constraints = Constraints::default();
        let uninit = Int::fresh_const(z3_ctx, "uninit_byte");
        constraints.term_caches.uninit_byte = Some(uninit.clone());
        constraints
            .assertions
            .push(uninit.ge(&Int::from_u64(z3_ctx, 256)));
        Self {
            target_def_id,
            instantiated_target_body,
            z3_ctx,
            tcx,
            current_frame: FrameState {
                current_def_id: target_def_id,
                instantiated_body: instantiated_target_body,
                local_alloc: FxHashMap::default(),
                pending_enum_fields: FxHashMap::default(),
            },
            caller_frames: Vec::default(),
            units: Vec::default(),
            ownership_transfers: Vec::new(),
            thread_local_allocs: FxHashMap::default(),
            constraints,
            inline: InlineCtx::default(),
            method_result_cache: Vec::default(),
            alias_hazard_allocs: FxHashSet::default(),
            index_access_facts: Vec::new(),
            safedrop_events: SafeDropEventLog::default(),
            diagnostics: Diagnostics::default(),
        }
    }

    /// MIR for the current frame, preferring its selected generic instantiation.
    pub(crate) fn body(&self) -> &'tcx Body<'tcx> {
        self.body_for(self.current_frame.current_def_id)
    }

    pub(crate) fn body_for(&self, def_id: DefId) -> &'tcx Body<'tcx> {
        if def_id == self.current_frame.current_def_id
            && let Some(body) = self.current_frame.instantiated_body
        {
            body
        } else if def_id == self.target_def_id
            && let Some(body) = &self.instantiated_target_body
        {
            body
        } else {
            self.tcx.optimized_mir(def_id)
        }
    }

    /// MIR for the verification target, preferring its selected generic instantiation.
    pub(crate) fn target_body(&self) -> &rustc_middle::mir::Body<'tcx> {
        self.instantiated_target_body
            .unwrap_or_else(|| self.tcx.optimized_mir(self.target_def_id))
    }

    pub(crate) fn record_unsupported(&mut self, operation: &str) {
        let location = self.diagnostics.location_label(self.tcx);
        self.diagnostics.record_unsupported(
            location.as_deref(),
            operation,
        );
    }

    pub(crate) fn record_unsupported_effect(&mut self, effect: &str) {
        let location = self.diagnostics.location_label(self.tcx);
        self.diagnostics.record_unsupported_effect(
            location.as_deref(),
            effect,
        );
    }

    pub(crate) fn record_missing_mir(&mut self, callee: DefId) {
        let location = self.diagnostics.location_label(self.tcx);
        self.diagnostics.record_missing_mir(
            location.as_deref(),
            &self.tcx.def_path_str(callee),
        );
    }

    pub(crate) fn record_opaque_control_flow(&mut self, operation: &str) {
        let location = self.diagnostics.location_label(self.tcx);
        self.diagnostics.record_opaque_control_flow(
            location.as_deref(),
            operation,
        );
    }

    /// Capture the frame-scoped state before switching to an inlined callee.
    ///
    /// This is the single source of truth for *what* is frame-scoped: the whole
    /// [`FrameState`] (function identity, local bindings, and operand sources).
    /// Both inline mechanisms (`handle_callee_entry` in path replay and
    /// `exec_inline_call`) call this, so they can no longer drift apart.
    pub(crate) fn enter_frame(
        &mut self,
        callee: DefId,
        body: Option<&'tcx Body<'tcx>>,
    ) -> FrameState<'tcx> {
        std::mem::replace(
            &mut self.current_frame,
            FrameState {
                current_def_id: callee,
                instantiated_body: body,
                local_alloc: FxHashMap::default(),
                pending_enum_fields: FxHashMap::default(),
            },
        )
    }

    /// Restore the frame-scoped state after an inlined callee returns.
    pub(crate) fn restore_frame(&mut self, frame: FrameState<'tcx>) {
        self.current_frame = frame;
    }

    /// Look up the whole value bound to a MIR local (its `path == []` slot in
    /// the allocation backing the local).
    pub(crate) fn local_value(&self, local: Local) -> Option<&VmValue<'z3, 'tcx>> {
        let alloc_id = *self.current_frame.local_alloc.get(&local)?;
        let view_ty = self.body().local_decls[local].ty;
        self.load_value(alloc_id, view_ty, &[])
    }

    pub(crate) fn term_involves(terms: &FxHashSet<Int<'z3>>, term: &Int<'z3>) -> bool {
        let mut pending = vec![Dynamic::from_ast(term)];
        let mut seen = FxHashSet::default();
        while let Some(ast) = pending.pop() {
            if !seen.insert(ast.clone()) {
                continue;
            }
            if ast.as_int().is_some_and(|value| terms.contains(&value)) {
                return true;
            }
            pending.extend(ast.children());
        }
        false
    }

    /// Bind a whole value to a MIR local (store it at `path == []` in the
    /// allocation backing the local, allocating that stack slot on demand).
    pub(crate) fn set_local(&mut self, local: Local, mut value: VmValue<'z3, 'tcx>) {
        self.current_frame.pending_enum_fields.remove(&local);
        self.ensure_local_allocation(local);
        let alloc_id = self.current_frame.local_alloc[&local];
        self.content_mut(alloc_id).facts.may_be_uninit = false;
        let view_ty = self.body().local_decls[local].ty;
        if matches!(view_ty.kind(), TyKind::Adt(def, _)
            if crate::verify::api_classify::is_std_vec(def.did()))
            && value.provenance.as_ref().is_none_or(|prov| {
                let source = self.alloc(prov.alloc_id);
                matches!(source.kind, AllocKind::Object)
                    && matches!(source.element_ty.as_ty(), Some(ty)
                        if matches!(ty.kind(), TyKind::Adt(source_def, _)
                            if crate::verify::api_classify::is_std_vec(source_def.did())))
            })
        {
            value.provenance = Some(Provenance {
                alloc_id,
                offset: Int::from_u64(self.z3_ctx, 0),
                offset_kind: None,
            });
        }
        if matches!(view_ty.kind(), TyKind::Adt(def, _)
            if crate::verify::api_classify::is_maybe_uninit_type(def.did()))
        {
            self.clear_write_evidence(alloc_id);
            self.content_mut(alloc_id).facts.inner_uninit = false;
        }
        self.store_value(alloc_id, view_ty, vec![], value);
    }

    pub(crate) fn invalidate_indexed_array(&mut self, local: Local) {
        let view_ty = self.body().local_decls[local].ty;
        let mut element_ty = view_ty;
        let mut is_array = false;
        while let rustc_middle::ty::TyKind::Array(inner, _) = element_ty.kind() {
            element_ty = *inner;
            is_array = true;
        }
        if is_array && let Some(&alloc_id) = self.current_frame.local_alloc.get(&local) {
            let content = self.content_mut(alloc_id);
            let was_tracked =
                content.indexed_elements_modified || !content.indexed_elements.is_empty();
            content.indexed_elements.clear();
            content.indexed_elements_modified = was_tracked;
            content
                .values
                .retain(|(ty, path), _| *ty != view_ty || path.is_empty());
        }
    }

    /// Mark a value as initialized (written), and sync its backing allocation's
    /// [`ContentFacts::initialized`] fact.
    ///
    /// This is the single entry point that keeps the value-level
    /// [`ValueFacts::init`] and the allocation-level [`ContentFacts::initialized`]
    /// in sync; callers must set the pair through here rather than by hand so
    /// the two facts cannot drift apart.
    pub(crate) fn mark_initialized(&mut self, value: &mut VmValue<'z3, 'tcx>) {
        value.facts.init = true;
        if let Some(prov) = &value.provenance {
            self.content_mut(prov.alloc_id).facts.initialized = true;
        }
    }

    /// Get the symbolic address of a MIR local (its stack allocation's base).
    pub(crate) fn local_address(&mut self, local: Local) -> Int<'z3> {
        self.ensure_local_allocation(local);
        let id = self.current_frame.local_alloc[&local];
        self.units[id.0].allocation.base.clone()
    }

    /// Allocate a fresh symbolic object and return its ID and base address.
    pub(crate) fn allocate(
        &mut self,
        size: Int<'z3>,
        align: Int<'z3>,
        element_ty: Option<Ty<'tcx>>,
    ) -> (AllocId, Int<'z3>) {
        self.allocate_internal(size, align, element_ty, AllocKind::Object)
    }

    /// Allocate a fresh external allocation (for raw-pointer parameters).
    /// External allocations may be null and have unlimited size.
    pub(crate) fn allocate_external(
        &mut self,
        size: Int<'z3>,
        align: Int<'z3>,
        element_ty: Option<Ty<'tcx>>,
    ) -> (AllocId, Int<'z3>) {
        self.allocate_internal(size, align, element_ty, AllocKind::External)
    }

    /// Allocate a slice/array data allocation with a known (possibly symbolic)
    /// element count. Computes `size = len * elem_size` and materializes `len`
    /// in one step, so `size` and the slice length can never diverge (the
    /// `size == len * elem_size` invariant is established here instead of being
    /// re-derived by every caller).
    pub(crate) fn allocate_slice(
        &mut self,
        len: Int<'z3>,
        elem_size: Int<'z3>,
        align: Int<'z3>,
        element_ty: Option<Ty<'tcx>>,
    ) -> (AllocId, Int<'z3>) {
        let size = Int::mul(self.z3_ctx, &[&len, &elem_size]);
        let (id, base) = self.allocate(size, align, element_ty);
        self.alloc_mut(id).set_slice_len(len);
        (id, base)
    }

    fn allocate_internal(
        &mut self,
        size: Int<'z3>,
        align: Int<'z3>,
        element_ty: Option<Ty<'tcx>>,
        kind: AllocKind<'z3>,
    ) -> (AllocId, Int<'z3>) {
        let id = AllocId(self.units.len());
        let base = {
            let name = format!(
                "{}_{}",
                if matches!(kind, AllocKind::External) {
                    "ext"
                } else {
                    "heap"
                },
                id.0
            );
            Int::new_const(self.z3_ctx, name.as_str())
        };
        let alloc = Allocation::new(base.clone(), size, align, element_ty, kind);
        self.units.push(MemoryUnit {
            allocation: alloc,
            content: MemoryContent::default(),
        });
        (id, base)
    }

    /// Indexed access to an allocation by its `AllocId` (the id is the index).
    pub(crate) fn alloc(&self, id: AllocId) -> &Allocation<'z3, 'tcx> {
        &self.units[id.0].allocation
    }

    /// Mutable indexed access to an allocation by its `AllocId`.
    pub(crate) fn alloc_mut(&mut self, id: AllocId) -> &mut Allocation<'z3, 'tcx> {
        &mut self.units[id.0].allocation
    }

    /// Indexed access to an allocation's contents by its `AllocId`.
    pub(crate) fn content(&self, id: AllocId) -> &MemoryContent<'z3, 'tcx> {
        &self.units[id.0].content
    }

    /// Mutable indexed access to an allocation's contents by its `AllocId`.
    pub(crate) fn content_mut(&mut self, id: AllocId) -> &mut MemoryContent<'z3, 'tcx> {
        &mut self.units[id.0].content
    }

    /// Whether `id` was asserted a valid C string via a `ValidCStr` contract
    /// fact / struct invariant.
    pub(crate) fn is_cstr_trusted(&self, id: AllocId) -> bool {
        self.content(id).facts.cstr_trusted
    }

    /// Whether `id` was asserted valid UTF-8 via a `ValidString` contract fact.
    pub(crate) fn is_utf8_trusted(&self, id: AllocId) -> bool {
        self.content(id).facts.utf8_trusted
    }

    /// The ultimate root allocation, following `parent` chains (sub-allocations
    /// created by `from_raw_parts` / `split_at` / `as_chunks`, whose `parent`
    /// points at the allocation they were split from).
    pub(crate) fn root_alloc(&self, id: AllocId) -> AllocId {
        let mut cur = id;
        let mut guard = 0;
        while let Some(parent) = self.alloc(cur).parent {
            cur = parent;
            guard += 1;
            // A parent chain as long as the total allocation count means a
            // cycle; stop rather than loop forever.
            if guard >= self.units.len() {
                break;
            }
        }
        cur
    }

    /// Create a fresh symbolic Z3 int constant (globally unique, even across
    /// calls with the same prefix — `Z3_mk_fresh_const` auto-suffixes the name).
    pub(crate) fn fresh_int(&self, prefix: &str) -> Int<'z3> {
        Int::fresh_const(self.z3_ctx, prefix)
    }

    /// Get the value of a specific field within an aggregate local.
    ///
    /// Field values live in the allocation backing the local (the
    /// memory-contents layer [`MemoryContent::values`]), keyed by the local's declared
    /// type as the view type.  Returns `None` if the local has no allocation
    /// (the field was never materialized).
    pub(crate) fn field_value(&self, local: Local, path: &[usize]) -> Option<&VmValue<'z3, 'tcx>> {
        let alloc_id = *self.current_frame.local_alloc.get(&local)?;
        let view_ty = self.body().local_decls[local].ty;
        self.load_value(alloc_id, view_ty, path).or_else(|| {
            let mut candidates = vec![path.to_vec()];
            for position in (0..path.len()).rev() {
                if path[position] == REPEATED_ARRAY_ELEMENT {
                    continue;
                }
                let alternatives = candidates.clone();
                for mut candidate in alternatives {
                    candidate[position] = REPEATED_ARRAY_ELEMENT;
                    if let Some(value) = self.load_value(alloc_id, view_ty, &candidate) {
                        return Some(value);
                    }
                    candidates.push(candidate);
                }
            }
            None
        })
    }

    /// Enumerate the field paths materialized for a local: every non-empty
    /// `path` for which [`Self::field_value`] currently returns a value (the
    /// local's allocation's fields under its declared view type).  The whole
    /// value (`path == []`) is deliberately excluded — it is read via
    /// [`Self::local_value`], not as a "field", so callers iterating fields do
    /// not accidentally treat the whole value as a field projection.
    pub(crate) fn field_paths(&self, local: Local) -> Vec<Vec<usize>> {
        let Some(&alloc_id) = self.current_frame.local_alloc.get(&local) else {
            return Vec::new();
        };
        let view_ty = self.body().local_decls[local].ty;
        self.units[alloc_id.0]
            .content
            .values
            .keys()
            .filter(|(t, p)| *t == view_ty && !p.is_empty())
            .map(|(_, p)| p.clone())
            .collect()
    }

    /// The declared type of `local` in `frame`'s body.
    pub(crate) fn frame_local_ty(&self, frame: &FrameState<'tcx>, local: Local) -> Ty<'tcx> {
        let body = frame
            .instantiated_body
            .or_else(|| {
                (frame.current_def_id == self.target_def_id)
                    .then_some(self.instantiated_target_body)
                    .flatten()
            })
            .unwrap_or_else(|| self.tcx.optimized_mir(frame.current_def_id));
        body.local_decls[local].ty
    }

    /// Enumerate the field paths materialized for `local` in a saved caller
    /// `frame`. Field values live in the path-scoped [`MemoryContent::values`], so they
    /// are read via `frame`'s `local_alloc` and declared type.
    pub(crate) fn frame_field_paths(
        &self,
        frame: &FrameState<'tcx>,
        local: Local,
    ) -> Vec<Vec<usize>> {
        let Some(&alloc_id) = frame.local_alloc.get(&local) else {
            return Vec::new();
        };
        let view_ty = self.frame_local_ty(frame, local);
        self.units[alloc_id.0]
            .content
            .values
            .keys()
            .filter(|(t, p)| *t == view_ty && !p.is_empty())
            .map(|(_, p)| p.clone())
            .collect()
    }

    /// Read a field of `local` in a saved caller `frame`.
    pub(crate) fn frame_field_value(
        &self,
        frame: &FrameState<'tcx>,
        local: Local,
        path: &[usize],
    ) -> Option<&VmValue<'z3, 'tcx>> {
        let alloc_id = *frame.local_alloc.get(&local)?;
        let view_ty = self.frame_local_ty(frame, local);
        self.load_value(alloc_id, view_ty, path)
    }

    /// Read the whole value of `local` in a saved caller `frame` (its
    /// `path == []` slot). The value lives in the path-scoped [`MemoryContent::values`],
    /// while the name → allocation binding lives in the saved `frame`.
    pub(crate) fn frame_local_value(
        &self,
        frame: &FrameState<'tcx>,
        local: Local,
    ) -> Option<&VmValue<'z3, 'tcx>> {
        let alloc_id = *frame.local_alloc.get(&local)?;
        let view_ty = self.frame_local_ty(frame, local);
        self.load_value(alloc_id, view_ty, &[])
    }

    /// Enumerate `(local, whole value)` for every local with a materialized
    /// whole value (its `path == []` slot). This is the whole-value counterpart
    /// to [`Self::field_paths`], used where code used to iterate `locals`.
    pub(crate) fn all_local_values(&self) -> Vec<(Local, &VmValue<'z3, 'tcx>)> {
        self.current_frame
            .local_alloc
            .keys()
            .copied()
            .filter_map(|local| self.local_value(local).map(|value| (local, value)))
            .collect()
    }

    /// The field carrying an owned value's heap pointer (`Box`/`Vec`/`String`'s
    /// owning pointer field), located generically via
    /// [`Self::container_ptr_field`] (e.g. `Box` → `[0, 0]`, `Vec` → `[0, 0, 0]`).
    /// Falls back to the first materialized field with heap provenance for
    /// owners whose deep `NonNull` leaf was not explicitly materialized (e.g. a
    /// `Box` produced by `into_boxed_slice`, which only records the whole value).
    pub(crate) fn owner_ptr_field(&self, local: Local) -> Option<&VmValue<'z3, 'tcx>> {
        let ty = self.body().local_decls[local].ty;
        if let Some(path) = self.container_ptr_field(ty)
            && let Some(v) = self.field_value(local, &path)
            && v.provenance_alloc_id().is_some()
        {
            return Some(v);
        }
        self.field_paths(local).iter().find_map(|path| {
            self.field_value(local, path)
                .filter(|v| v.provenance_alloc_id().is_some())
        })
    }

    /// Invalidate `local`'s owner-field provenance (mark it moved-out after a
    /// whole-place move), so a later `Owning` check does not treat it as a
    /// second owner of the heap allocation it no longer owns.
    pub(crate) fn invalidate_owner_field(&mut self, local: Local) {
        let ty = self.body().local_decls[local].ty;
        let Some(path) = self.container_ptr_field(ty) else {
            return;
        };
        let Some(mut fv) = self.field_value(local, &path).cloned() else {
            return;
        };
        if fv.provenance_alloc_id().is_some() {
            fv.provenance = None;
            self.set_field_value(local, path, fv);
        }
    }

    /// Set the value of a specific field within an aggregate local.
    ///
    /// Ensures the local has a backing allocation, then stores into the
    /// memory-contents layer ([`MemoryContent::values`]) keyed by the local's declared
    /// type as the view type.
    pub(crate) fn set_field_value(
        &mut self,
        local: Local,
        path: Vec<usize>,
        value: VmValue<'z3, 'tcx>,
    ) {
        let view_ty = self.body().local_decls[local].ty;
        self.ensure_local_allocation(local);
        let alloc_id = self.current_frame.local_alloc[&local];
        self.store_value(alloc_id, view_ty, path, value);
    }

    pub(crate) fn write_local_path(
        &mut self,
        local: Local,
        path: Vec<usize>,
        value: VmValue<'z3, 'tcx>,
    ) {
        let written_ty = value.ty;
        let written_inner = matches!(self.body().local_decls[local].ty.kind(), TyKind::Adt(def, args)
            if crate::verify::api_classify::is_maybe_uninit_type(def.did())
                && args.first().and_then(|arg| arg.as_type()) == Some(value.ty))
            && !path.is_empty()
            && path.iter().all(|field| *field == 0)
            && value.facts.init;
        let prior_term = self
            .local_value(local)
            .map(|value| value.z3_term.to_string());
        self.index_access_facts
            .retain(|(slice_term, index_term, slice, index)| {
                *slice != local
                    && *index != local
                    && prior_term.as_ref().is_none_or(|term| {
                        *term != slice_term.to_string() && *term != index_term.to_string()
                    })
            });
        if path.is_empty() {
            self.invalidate_indexed_array(local);
            self.invalidate_field_descendants(local, &[]);
            self.set_local(local, value);
        } else {
            self.invalidate_field_descendants(local, &path);
            self.set_field_value(local, path, value);
            if written_inner && let Some(&alloc_id) = self.current_frame.local_alloc.get(&local) {
                self.content_mut(alloc_id).facts.written_pointee_ty = Some(written_ty);
            }
        }
    }

    pub(crate) fn invalidate_field_descendants(&mut self, local: Local, path: &[usize]) {
        if let Some(&alloc_id) = self.current_frame.local_alloc.get(&local) {
            let view_ty = self.body().local_decls[local].ty;
            self.content_mut(alloc_id)
                .values
                .retain(|(ty, stored_path), _| {
                    *ty != view_ty
                        || stored_path.len() <= path.len()
                        || !stored_path.starts_with(path)
                });
        }
    }

    /// Assert path conditions and invariant constraints into a solver.
    pub(crate) fn assert_all(&self, solver: &z3::Solver<'z3>) {
        self.assert_path_constraints(solver);
        let zero = Int::from_u64(self.z3_ctx, 0);
        for unit in &self.units {
            let alloc = &unit.allocation;
            if !alloc.is_external() {
                solver.assert(&alloc.base._eq(&zero).not());
            }
            solver.assert(&alloc.size.ge(&zero));
            if alloc.align.simplify().as_u64() != Some(1) {
                solver.assert(&alloc.base.rem(&alloc.align)._eq(&zero));
            }
        }

        // Whole values (`path == []`) and field values (`path == [i, ..]`) both
        // live in the memory-contents layer.  Field paths exclude the whole
        // value (see [`Self::field_paths`]), so assert the whole value and the
        // fields separately.
        let local_ids: Vec<Local> = self.current_frame.local_alloc.keys().copied().collect();
        for local in local_ids {
            if let Some(value) = self.local_value(local) {
                self.assert_value_constraints(solver, value);
            }
            for path in self.field_paths(local) {
                if let Some(value) = self.field_value(local, &path) {
                    self.assert_value_constraints(solver, value);
                }
            }
        }
    }

    pub(crate) fn assert_path_constraints(&self, solver: &z3::Solver<'z3>) {
        for cond in &self.constraints.assertions {
            solver.assert(cond);
        }
    }

    /// Assert a single symbolic value's known invariant constraints.
    fn assert_value_constraints(&self, solver: &z3::Solver<'z3>, value: &VmValue<'z3, 'tcx>) {
        let zero = Int::from_u64(self.z3_ctx, 0);
        if value.facts.non_null {
            solver.assert(&value.z3_term._eq(&zero).not());
        }
        if let Some(ref prov) = value.provenance {
            let is_scalar = matches!(
                value.ty.kind(),
                rustc_middle::ty::TyKind::Uint(_)
                    | rustc_middle::ty::TyKind::Int(_)
                    | rustc_middle::ty::TyKind::Bool
                    | rustc_middle::ty::TyKind::Char
            );
            if !is_scalar {
                let alloc = self.alloc(prov.alloc_id);
                let expected = Int::add(self.z3_ctx, &[&alloc.base, &prov.offset]);
                solver.assert(&value.z3_term._eq(&expected));
            }
        }
        if matches!(
            value.ty.kind(),
            rustc_middle::ty::TyKind::Uint(_)
                | rustc_middle::ty::TyKind::Bool
                | rustc_middle::ty::TyKind::Char
        ) {
            solver.assert(&value.z3_term.ge(&zero));
        }
        if matches!(value.ty.kind(), rustc_middle::ty::TyKind::Bool) {
            let one = Int::from_u64(self.z3_ctx, 1);
            solver.assert(&value.z3_term.le(&one));
        }
        if matches!(value.ty.kind(), rustc_middle::ty::TyKind::Char) {
            let max = Int::from_u64(self.z3_ctx, 0x10FFFF);
            solver.assert(&value.z3_term.le(&max));
        }
    }
}

impl std::fmt::Debug for VmState<'_, '_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("VmState")
            .field("locals_count", &self.current_frame.local_alloc.len())
            .field("allocations_count", &self.units.len())
            .field("assertions", &self.constraints.assertions.len())
            .finish()
    }
}

// ── Shared value extraction ──────────────────────────────────────

impl<'z3, 'tcx> VmState<'z3, 'tcx> {
    pub(crate) fn indexed_element_target(
        &self,
        place: &Place<'tcx>,
    ) -> Option<(AllocId, Int<'z3>)> {
        let element_ty = place.ty(self.body(), self.tcx).ty;
        if !matches!(
            element_ty.kind(),
            rustc_middle::ty::TyKind::RawPtr(..)
                | rustc_middle::ty::TyKind::Int(..)
                | rustc_middle::ty::TyKind::Uint(..)
                | rustc_middle::ty::TyKind::Bool
                | rustc_middle::ty::TyKind::Char
                | rustc_middle::ty::TyKind::Float(..)
        ) {
            return None;
        }
        if !matches!(
            place.projection.last()?.kind(),
            ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. }
        ) {
            return None;
        }
        let mut current_ty = self.body().local_decls[place.local].ty;
        let mut fields = Vec::new();
        let mut index = Int::from_u64(self.z3_ctx, 0);
        let element_size = self.size_of_ty(element_ty);
        if element_size == 0 {
            return None;
        }
        let mut indexed = false;
        for projection in place.projection.iter() {
            match projection {
                ProjectionElem::Field(field, field_ty) if !indexed => {
                    fields.push(field.as_usize());
                    current_ty = field_ty;
                }
                ProjectionElem::Deref => {
                    current_ty = match current_ty.kind() {
                        rustc_middle::ty::TyKind::Ref(_, inner, _)
                        | rustc_middle::ty::TyKind::RawPtr(inner, _) => *inner,
                        _ => return None,
                    };
                }
                ProjectionElem::Downcast(..) => {}
                ProjectionElem::Index(local) => {
                    let inner = match current_ty.kind() {
                        rustc_middle::ty::TyKind::Array(inner, _)
                        | rustc_middle::ty::TyKind::Slice(inner) => *inner,
                        _ => return None,
                    };
                    let inner_size = self.size_of_ty(inner);
                    if inner_size == 0 || inner_size % element_size != 0 {
                        return None;
                    }
                    let term = self.local_value(local)?.z3_term.clone();
                    let stride = Int::from_u64(self.z3_ctx, inner_size / element_size);
                    let step = Int::mul(self.z3_ctx, &[&term, &stride]);
                    index = Int::add(self.z3_ctx, &[&index, &step]);
                    current_ty = inner;
                    indexed = true;
                }
                ProjectionElem::ConstantIndex {
                    offset, from_end, ..
                } => {
                    let (inner, length) = match current_ty.kind() {
                        rustc_middle::ty::TyKind::Array(inner, length) => (*inner, Some(length)),
                        rustc_middle::ty::TyKind::Slice(inner) => (*inner, None),
                        _ => return None,
                    };
                    let inner_size = self.size_of_ty(inner);
                    if inner_size == 0 || inner_size % element_size != 0 {
                        return None;
                    }
                    let position = if from_end {
                        length?.try_to_target_usize(self.tcx)?.checked_sub(offset)?
                    } else {
                        offset
                    };
                    let term = Int::from_u64(self.z3_ctx, position);
                    let stride = Int::from_u64(self.z3_ctx, inner_size / element_size);
                    let step = Int::mul(self.z3_ctx, &[&term, &stride]);
                    index = Int::add(self.z3_ctx, &[&index, &step]);
                    current_ty = inner;
                    indexed = true;
                }
                _ => return None,
            }
        }
        if current_ty != element_ty {
            return None;
        }
        let alloc_id = if fields.is_empty() {
            let local_ty = self.body().local_decls[place.local].ty;
            if matches!(local_ty.kind(), rustc_middle::ty::TyKind::Array(..)) {
                self.current_frame.local_alloc.get(&place.local).copied()?
            } else {
                self.local_value(place.local)
                    .and_then(|value| value.provenance_alloc_id())
                    .or_else(|| self.current_frame.local_alloc.get(&place.local).copied())?
            }
        } else {
            self.field_value(place.local, &fields)?
                .provenance_alloc_id()?
        };
        let stored_ty = self.alloc(alloc_id).element_ty.as_ty()?;
        let mut stored_leaf_ty = stored_ty;
        while let rustc_middle::ty::TyKind::Array(inner, _) = stored_leaf_ty.kind() {
            stored_leaf_ty = *inner;
        }
        (stored_leaf_ty == element_ty).then_some((alloc_id, index))
    }

    pub(crate) fn store_indexed_element(
        &mut self,
        alloc_id: AllocId,
        index: Int<'z3>,
        value: VmValue<'z3, 'tcx>,
    ) {
        let retained = self
            .content(alloc_id)
            .indexed_elements
            .iter()
            .filter(|(stored_index, _)| self.path_implies(&stored_index._eq(&index).not()))
            .cloned()
            .collect();
        let content = self.content_mut(alloc_id);
        content.indexed_elements_modified = true;
        content.indexed_elements = retained;
        content.indexed_elements.push((index, value));
    }

    pub(crate) fn store_repeated_indexed_elements(
        &mut self,
        alloc_id: AllocId,
        base: Int<'z3>,
        count: u64,
        value: VmValue<'z3, 'tcx>,
    ) {
        let end = Int::add(self.z3_ctx, &[&base, &Int::from_u64(self.z3_ctx, count)]);
        let retained = self
            .content(alloc_id)
            .indexed_elements
            .iter()
            .filter(|(index, _)| {
                let outside = Bool::or(self.z3_ctx, &[&index.lt(&base), &index.ge(&end)]);
                self.path_implies(&outside)
            })
            .cloned()
            .collect::<Vec<_>>();
        let mut elements = retained;
        for offset in 0..count {
            let index = Int::add(self.z3_ctx, &[&base, &Int::from_u64(self.z3_ctx, offset)]);
            elements.push((index, value.clone()));
        }
        let content = self.content_mut(alloc_id);
        content.indexed_elements_modified = true;
        content.indexed_elements = elements;
    }

    pub(crate) fn path_implies(&self, condition: &Bool<'z3>) -> bool {
        if condition.simplify().as_bool() == Some(true) {
            return true;
        }
        let solver = Solver::new(self.z3_ctx);
        for assertion in &self.constraints.assertions {
            solver.assert(assertion);
        }
        solver.assert(&condition.not());
        solver.check() == SatResult::Unsat
    }

    fn stored_indexed_element(&self, place: &Place<'tcx>) -> Option<VmValue<'z3, 'tcx>> {
        let (alloc_id, index) = self.indexed_element_target(place)?;
        let elements = &self.content(alloc_id).indexed_elements;
        if let Some((_, value)) = elements
            .iter()
            .rev()
            .find(|(stored_index, _)| index == *stored_index)
        {
            return Some(value.clone());
        }
        for (stored_index, value) in elements.iter().rev() {
            if self.path_implies(&index._eq(stored_index)) {
                return Some(value.clone());
            }
        }
        None
    }

    pub(crate) fn symbolic_const_term(
        &self,
        constant: &rustc_middle::mir::Const<'tcx>,
    ) -> Int<'z3> {
        self.symbolic_const_term_text(&format!("{constant:?}"))
    }

    pub(crate) fn symbolic_const_term_text(&self, text: &str) -> Int<'z3> {
        let name = format!("const_{}", text.replace([':', '#', ' '], "_"));
        Int::new_const(self.z3_ctx, name.as_str())
    }

    pub(crate) fn const_param_term(&self, index: u32) -> Option<Int<'z3>> {
        let generics = self.tcx.generics_of(self.current_frame.current_def_id);
        if index as usize >= generics.count() {
            return None;
        }
        let param = generics.param_at(index as usize, self.tcx);
        if !matches!(
            param.kind,
            rustc_middle::ty::GenericParamDefKind::Const { .. }
        ) {
            return None;
        }
        let ty = self.tcx.type_of(param.def_id).instantiate_identity();
        let ty = ty.skip_norm_wip();
        let value = rustc_middle::ty::Const::new_param(
            self.tcx,
            rustc_middle::ty::ParamConst::new(index, param.name),
        );
        Some(self.symbolic_const_term(&rustc_middle::mir::Const::Ty(ty, value)))
    }

    /// Extract a VmValue from a MIR operand.
    pub(crate) fn value_of_operand(&self, operand: &Operand<'tcx>) -> VmValue<'z3, 'tcx> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => self
                .value_of_place(place)
                .unwrap_or_else(|| self.unknown_value_for_place(place)),
            Operand::Constant(constant) => {
                let text = format!("{:?}", constant.const_);
                // `size_of::<T>()` / `align_of::<T>()` lower to the
                // `SizedTypeProperties::SIZE`/`::ALIGN` associated consts for a
                // generic `T`.  Bind them to the shared symbolic `sizeof_T` /
                // `align_T` (created by `size_sym`/`align_sym` during
                // `init_parameters`) so they agree with allocation sizes and
                // pointer strides instead of being unrelated fresh constants.
                if let rustc_middle::mir::Const::Unevaluated(uneval, _) = constant.const_ {
                    if mir_utils::is_sized_type_property(self.tcx, uneval.def, "IS_ZST")
                        && !uneval.args.is_empty()
                    {
                        let ty = uneval.args.type_at(0);
                        let size = if mir_utils::ty_has_type_param(ty) {
                            self.size_sym_read(ty)
                        } else {
                            Int::from_u64(self.z3_ctx, self.size_of_ty(ty))
                        };
                        let zero = Int::from_u64(self.z3_ctx, 0);
                        let one = Int::from_u64(self.z3_ctx, 1);
                        return VmValue::new(
                            size._eq(&zero).ite(&one, &zero),
                            constant.const_.ty(),
                        );
                    }
                    let is_size = mir_utils::is_sized_type_property(self.tcx, uneval.def, "SIZE");
                    let is_align = mir_utils::is_sized_type_property(self.tcx, uneval.def, "ALIGN");
                    if (is_size || is_align) && !uneval.args.is_empty() {
                        let ty = uneval.args.type_at(0);
                        let term = if is_size {
                            self.size_sym_read(ty)
                        } else {
                            self.align_sym_read(ty)
                        };
                        return VmValue::new(term, constant.const_.ty());
                    }
                }
                let int_val = mir_utils::eval_const_scalar_int(self.tcx, &constant.const_, &text);
                let field_offset = int_val.is_none()
                    && mir_utils::offset_of_container(self.tcx, &constant.const_).is_some();
                let enum_variant = mir_utils::const_destructure(self.tcx, &constant.const_)
                    .and_then(|(variant, _)| variant)
                    .or_else(|| {
                        let TyKind::Adt(adt, args) = constant.const_.ty().kind() else {
                            return None;
                        };
                        (int_val == Some(0)
                            && self
                                .tcx
                                .is_diagnostic_item(rustc_span::sym::Option, adt.did())
                            && matches!(args.type_at(0).kind(), TyKind::Ref(..)))
                        .then_some(0)
                    });
                let ty = constant.const_.ty();
                let wide_literal = matches!(
                    ty.kind(),
                    TyKind::Int(rustc_middle::ty::IntTy::I128)
                        | TyKind::Uint(rustc_middle::ty::UintTy::U128)
                )
                .then(|| {
                    constant
                        .const_
                        .eval(
                            self.tcx,
                            TypingEnv::fully_monomorphized(),
                            rustc_span::DUMMY_SP,
                        )
                        .ok()
                        .and_then(|value| value.try_to_scalar_int())
                        .and_then(|scalar| self.scalar_bits_term(ty, scalar.to_bits(scalar.size())))
                })
                .flatten();
                let term = wide_literal
                    .or_else(|| int_val.and_then(|value| self.scalar_bits_term(ty, value as u128)))
                    .unwrap_or_else(|| self.symbolic_const_term(&constant.const_));
                let enum_discriminant = enum_variant.and_then(|variant| {
                    self.enum_discriminant_term(ty, VariantIdx::from_usize(variant as usize))
                });
                VmValue {
                    z3_term: term,
                    ty,
                    provenance: None,
                    facts: ValueFacts::default(),
                    source: if let Some(term) = enum_discriminant {
                        ValueSource::KnownDiscriminant(term)
                    } else if field_offset {
                        ValueSource::FieldOffset
                    } else {
                        ValueSource::None
                    },
                }
            }
            Operand::RuntimeChecks(_) => VmValue::new(
                self.fresh_int("runtime_checks"),
                self.body().local_decls[Local::from_usize(0)].ty,
            ),
        }
    }

    pub(crate) fn materialize_const_adt(
        &mut self,
        local: Local,
        constant: &rustc_middle::mir::Const<'tcx>,
    ) {
        if let rustc_middle::mir::Const::Unevaluated(uneval, _) = constant
            && mir_utils::is_sized_type_property(self.tcx, uneval.def, "LAYOUT")
            && !uneval.args.is_empty()
            && let TyKind::Adt(layout_def, layout_args) = constant.ty().kind()
        {
            let ty = uneval.args.type_at(0);
            for (index, field) in layout_def.non_enum_variant().fields.iter().enumerate() {
                let term = match field.name.as_str() {
                    "size" => self.size_sym(ty),
                    "align" => self.align_sym(ty),
                    _ => continue,
                };
                let field_ty = mir_utils::field_ty(self.tcx, field, layout_args);
                self.set_field_value(local, vec![index], VmValue::new(term, field_ty));
            }
            return;
        }
        let Some((_variant, fields)) = mir_utils::const_destructure(self.tcx, constant) else {
            return;
        };
        for (idx, (field_val, field_ty)) in fields.iter().enumerate() {
            let term = self.const_field_term(field_val, *field_ty);
            self.set_field_value(local, vec![idx], VmValue::new(term, *field_ty));
        }
    }

    fn const_field_term(&self, val: &ConstValue, ty: Ty<'tcx>) -> Int<'z3> {
        if let Some(scalar) = (*val).try_to_scalar_int() {
            if let Some(term) = self.scalar_bits_term(ty, scalar.to_bits(scalar.size())) {
                return term;
            }
        }
        let name = format!(
            "const_field_{}",
            format!("{:?}", val).replace([':', '#', ' '], "_")
        );
        Int::new_const(self.z3_ctx, name.as_str())
    }

    /// Read the byte at `offset` within a `repr(C)`-style ADT from its
    /// materialized scalar field values — the field→byte direction of the cast
    /// cross-view materialization.  Returns `None` when `offset` does not land
    /// inside a concrete scalar field (so the caller falls back to the base).
    fn byte_from_field(&self, alloc_id: AllocId, ty: Ty<'tcx>, offset: usize) -> Option<Int<'z3>> {
        let rustc_middle::ty::TyKind::Adt(adt_def, substs) = ty.kind() else {
            return None;
        };
        let variant = adt_def.non_enum_variant();
        for (idx, field_def) in variant.fields.iter().enumerate() {
            let field_ty = mir_utils::field_ty(self.tcx, field_def, substs);
            let field_off = self.field_offset_in_bytes(ty, idx) as usize;
            let field_size = self.size_of_ty(field_ty) as usize;
            if offset >= field_off && offset < field_off + field_size {
                let fv = self.load_value(alloc_id, ty, &[idx])?;
                let byte_idx = offset - field_off;
                // Fields wider than 8 bytes (e.g. `u128`) cannot be shifted by a
                // `u64` divisor; fall back to the base rather than overflow.
                if byte_idx >= 8 {
                    return None;
                }
                let divisor = Int::from_u64(self.z3_ctx, 1u64 << (byte_idx * 8));
                let modulus = Int::from_u64(self.z3_ctx, 256);
                return Some(fv.z3_term.div(&divisor).rem(&modulus));
            }
        }
        None
    }

    /// Look up the value stored at a MIR place.
    pub(crate) fn value_of_place(&self, place: &Place<'tcx>) -> Option<VmValue<'z3, 'tcx>> {
        if place
            .projection
            .iter()
            .any(|projection| matches!(projection, ProjectionElem::Deref))
            && let Some(alloc_id) = self
                .local_value(place.local)
                .and_then(VmValue::provenance_alloc_id)
        {
            self.record_memory_use(alloc_id, place.local);
        }
        if place.projection.is_empty() {
            return self.local_value(place.local).cloned();
        }
        let place_ty = place.ty(self.body(), self.tcx).ty;
        if place.projection.len() == 3
            && matches!(place.projection[0].kind(), ProjectionElem::Deref)
            && matches!(place.projection[1].kind(), ProjectionElem::Downcast(..))
            && let ProjectionElem::Field(field, _) = place.projection[2].kind()
            && let Some(pointer) = self.local_value(place.local)
            && let Some(provenance) = &pointer.provenance
            && provenance.offset.simplify().as_u64() == Some(0)
            && let Some(pointee) = mir_utils::pointee_ty(pointer.ty)
            && matches!(pointee.kind(), TyKind::Adt(def, _) if def.is_enum())
            && self.alloc(provenance.alloc_id).element_ty.as_ty() == Some(pointee)
            && let Some(value) = self.load_value(provenance.alloc_id, pointee, &[field.as_usize()])
        {
            return Some(value.clone());
        }
        let last_is_index = place.projection.last().is_some_and(|projection| {
            matches!(
                projection.kind(),
                ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. }
            )
        });
        let indexed_target_modified = last_is_index
            && self
                .indexed_element_target(place)
                .is_some_and(|(alloc_id, _)| self.content(alloc_id).indexed_elements_modified);
        let index_count = place
            .projection
            .iter()
            .filter(|projection| {
                matches!(
                    projection.kind(),
                    ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. }
                )
            })
            .count();
        let indexed_value = last_is_index
            && (matches!(place_ty.kind(), rustc_middle::ty::TyKind::RawPtr(..))
                || index_count > 1
                || indexed_target_modified);
        if indexed_value {
            if let Some(value) = self.stored_indexed_element(place) {
                return Some(value);
            }
            if indexed_target_modified {
                return Some(self.unknown_value_for_place(place));
            }
            if let Some(&alloc_id) = self.current_frame.local_alloc.get(&place.local)
                && !self.content(alloc_id).indexed_elements_modified
            {
                let mut path = Vec::new();
                let mut supported = true;
                for projection in place.projection.iter() {
                    match projection {
                        ProjectionElem::Field(field, _) => path.push(field.as_usize()),
                        ProjectionElem::Index(local) => {
                            let index = self
                                .local_value(local)
                                .and_then(|value| value.z3_term.simplify().as_u64())
                                .and_then(|index| usize::try_from(index).ok())
                                .unwrap_or(REPEATED_ARRAY_ELEMENT);
                            path.push(index);
                        }
                        ProjectionElem::ConstantIndex {
                            offset,
                            from_end: false,
                            ..
                        } => {
                            path.push(offset as usize);
                        }
                        _ => supported = false,
                    }
                }
                if supported && let Some(value) = self.field_value(place.local, &path) {
                    return Some(value.clone());
                }
            }
        }
        if let Some(ProjectionElem::Index(index_local)) = place.projection.last()
            && place.projection[..place.projection.len() - 1]
                .iter()
                .all(|projection| matches!(projection.kind(), ProjectionElem::Field(..)))
            && let Some(index) = self
                .local_value(*index_local)
                .and_then(|value| value.z3_term.simplify().as_u64())
        {
            let mut path = place.projection[..place.projection.len() - 1]
                .iter()
                .filter_map(|projection| match projection.kind() {
                    ProjectionElem::Field(index, _) => Some(index.as_usize()),
                    _ => None,
                })
                .collect::<Vec<_>>();
            path.push(index as usize);
            if let Some(value) = self.field_value(place.local, &path) {
                return Some(value.clone());
            }
        }
        if indexed_value {
            return Some(self.unknown_value_for_place(place));
        }
        if place.projection.len() == 1
            && matches!(place.projection[0], ProjectionElem::Deref)
            && let Some(pointer) = self.local_value(place.local)
            && let Some(provenance) = &pointer.provenance
            && self.alloc(provenance.alloc_id).element_ty.as_ty() == Some(place_ty)
            && let Some(offset) = provenance.offset.simplify().as_u64()
            && let size = self.size_of_ty(place_ty)
            && size != 0
            && offset % size == 0
        {
            let value = self.units[provenance.alloc_id.0]
                .content
                .values
                .iter()
                .find_map(|((ty, path), value)| {
                    (matches!(ty.kind(), rustc_middle::ty::TyKind::Array(elem, _) if *elem == place_ty)
                        && path.as_slice() == [offset as usize / size as usize])
                        .then_some(value.clone())
                });
            if let Some(value) = value {
                return Some(value);
            }
        }
        if place.projection.len() == 1
            && matches!(place.projection[0], ProjectionElem::Deref)
            && matches!(place_ty.kind(), TyKind::Adt(def, _) if def.is_enum())
            && let Some(pointer) = self.local_value(place.local)
            && let Some(provenance) = &pointer.provenance
            && provenance.offset.simplify().as_u64() == Some(0)
            && self.alloc(provenance.alloc_id).element_ty.as_ty() == Some(place_ty)
            && let Some(value) = self.load_value(provenance.alloc_id, place_ty, &[])
        {
            return Some(value.clone());
        }
        if place.projection.len() == 1
            && matches!(place.projection[0], ProjectionElem::Deref)
            && matches!(
                place_ty.kind(),
                rustc_middle::ty::TyKind::Int(_)
                    | rustc_middle::ty::TyKind::Uint(_)
                    | rustc_middle::ty::TyKind::Bool
                    | rustc_middle::ty::TyKind::Char
                    | rustc_middle::ty::TyKind::Float(_)
            )
        {
            let pointer = self.local_value(place.local)?;
            if let Some(value) = self.read_field_allocation(pointer, place_ty) {
                return Some(value);
            }
            if let Some(provenance) = &pointer.provenance
                && provenance.offset.simplify().as_u64() == Some(0)
                && let Some(value) = self.load_value(provenance.alloc_id, place_ty, &[])
            {
                return Some(value.clone());
            }
            return Some(self.unknown_value_for_place(place));
        }

        let field_path: Vec<usize> = place
            .projection
            .iter()
            .filter_map(|proj| match proj.kind() {
                ProjectionElem::Field(field_idx, _) => Some(field_idx.as_usize()),
                _ => None,
            })
            .collect();

        // If we have a pure field path (only Field / Downcast projections),
        // look up in the per-field value map first.  For `Option`/`ControlFlow`,
        // the variant's data is stored under the same field index as the enum
        // field (the discriminant is tracked separately, not in the field map),
        // so `(x as Some).0` resolves to `x`'s field `[0]`.
        let is_pure_field = place.projection.iter().all(|p| {
            matches!(
                p.kind(),
                ProjectionElem::Field(..) | ProjectionElem::Downcast(..)
            )
        });
        let has_downcast = place
            .projection
            .iter()
            .any(|p| matches!(p.kind(), ProjectionElem::Downcast(..)));
        if !field_path.is_empty() && is_pure_field {
            if let Some(val) = self.field_value(place.local, &field_path).cloned() {
                return Some(val);
            }
            if let Some(base_val) = self.local_value(place.local)
                && self.is_len_field_read(base_val.ty, &field_path)
                && let Some(len) = self.len_from_value(base_val)
            {
                return Some(VmValue::new(len, place_ty));
            }
            if let Some(base_val) = self.local_value(place.local)
                && self.is_cap_field_read(base_val.ty, &field_path)
                && let Some(cap) = self.capacity_from_value(base_val)
            {
                return Some(VmValue::new(cap, place_ty));
            }
            if !has_downcast {
                // Fallback: when the base local has provenance, propagate it
                // to field accesses. This handles pointer-wrapper types (Box,
                // Unique, NonNull) where accessing inner pointer fields yields
                // the same provenance as the container.
                if let Some(base_val) = self.local_value(place.local)
                    && let Some(ref prov) = base_val.provenance
                    && !matches!(place_ty.kind(), TyKind::Int(_) | TyKind::Uint(_) | TyKind::Bool | TyKind::Char | TyKind::Float(_))
                {
                    return Some(VmValue {
                        z3_term: base_val.z3_term.clone(),
                        ty: place_ty,
                        provenance: Some(prov.clone()),
                        facts: base_val.facts.clone(),
                        source: ValueSource::None,
                    });
                }
                return None;
            }
            // A Downcast without a materialized field falls through to the
            // Deref+Field / multi-element fallback below, which returns the
            // base local (preserving the pre-Downcast behavior instead of
            // forcing a fresh value).
        }

        if !field_path.is_empty()
            && field_path.len() < place.projection.len()
            && place
                .projection
                .iter()
                .any(|p| matches!(p.kind(), ProjectionElem::Deref))
        {
            let non_field_deref = place.projection.iter().all(|p| {
                matches!(
                    p.kind(),
                    ProjectionElem::Field(..)
                        | ProjectionElem::Deref
                        | ProjectionElem::Subslice { .. }
                )
            });
            if non_field_deref {
                if let Some(val) = self.field_value(place.local, &field_path).cloned() {
                    return Some(val);
                }
                // Resolve a Deref+Field access through the pointee allocation's
                // per-allocation field tracking (e.g. `(*leaf).len` → the
                // `LeafNode.len` field value materialized by
                // `decompose_pointee_fields`).  The viewed type (pointee) is part
                // of the key so reinterpret casts (e.g. `LeafNode` → `InternalNode`)
                // resolve to the right field view.
                if let Some(base_val) = self.local_value(place.local)
                    && let Some(alloc_id) = base_val.provenance_alloc_id()
                {
                    let view_ty = mir_utils::pointee_ty(base_val.ty).unwrap_or(base_val.ty);
                    if let Some(val) = self.load_value(alloc_id, view_ty, &field_path).cloned() {
                        return Some(val);
                    }
                }
                if let Some(base_val) = self.local_value(place.local)
                    && self.is_len_field_read(base_val.ty, &field_path)
                    && let Some(len) = self.len_from_value(base_val)
                {
                    return Some(VmValue::new(len, place_ty));
                }
                if let Some(base_val) = self.local_value(place.local)
                    && self.is_cap_field_read(base_val.ty, &field_path)
                    && let Some(cap) = self.capacity_from_value(base_val)
                {
                    return Some(VmValue::new(cap, place_ty));
                }
            }
        }

        let mut base = self.local_value(place.local)?.clone();
        for proj in place.projection.iter() {
            match proj.kind() {
                ProjectionElem::Deref => {
                    base.ty = place_ty;
                }
                ProjectionElem::Field(_field_idx, _) => {
                    if !field_path.is_empty()
                        && let Some(val) = self.field_value(place.local, &field_path).cloned()
                    {
                        return Some(val);
                    }
                    base.ty = place_ty;
                }
                _ => {}
            }
        }

        let proj = place.projection.last().expect("non-empty projection");
        let prefix_is_deref = place.projection[..place.projection.len() - 1]
            .iter()
            .all(|p| matches!(p.kind(), ProjectionElem::Deref));
        if prefix_is_deref {
            let index = match proj {
                ProjectionElem::Index(local) => self
                    .local_value(*local)
                    .and_then(|value| value.z3_term.simplify().as_u64()),
                ProjectionElem::ConstantIndex {
                    offset,
                    from_end: false,
                    ..
                } => Some(*offset),
                _ => None,
            };
            if let Some(index) = index
                && let Some(value) = self.field_value(place.local, &[index as usize])
            {
                return Some(value.clone());
            }
            if let ProjectionElem::Index(local) = proj
                && let Some(index_value) = self.local_value(*local)
                && matches!(
                    place_ty.kind(),
                    rustc_middle::ty::TyKind::Int(_)
                        | rustc_middle::ty::TyKind::Uint(_)
                        | rustc_middle::ty::TyKind::Bool
                        | rustc_middle::ty::TyKind::Char
                )
                && let rustc_middle::ty::TyKind::Array(_, length) =
                    self.body().local_decls[place.local].ty.kind()
                && let Some(length) = length.try_to_target_usize(self.tcx)
            {
                let repeated = self
                    .field_value(place.local, &[REPEATED_ARRAY_ELEMENT])
                    .cloned();
                let elements = if repeated.is_some() {
                    self.field_paths(place.local)
                        .into_iter()
                        .filter_map(|path| {
                            (path.len() == 1
                                && path[0] < length as usize
                                && path[0] != REPEATED_ARRAY_ELEMENT)
                                .then(|| {
                                    self.field_value(place.local, &path)
                                        .cloned()
                                        .map(|value| (path[0], value))
                                })
                                .flatten()
                        })
                        .collect::<Vec<_>>()
                } else {
                    (0..length)
                        .filter_map(|index| {
                            self.field_value(place.local, &[index as usize])
                                .cloned()
                                .map(|value| (index as usize, value))
                        })
                        .collect::<Vec<_>>()
                };
                if repeated.is_some() || elements.len() == length as usize {
                    let mut term = repeated
                        .map(|value| value.z3_term)
                        .unwrap_or_else(|| self.fresh_int("array_index"));
                    for (index, element) in elements {
                        let selected = index_value
                            .z3_term
                            ._eq(&Int::from_u64(self.z3_ctx, index as u64));
                        term = selected.ite(&element.z3_term, &term);
                    }
                    return Some(VmValue::new(term, place_ty));
                }
            }
        }
        if let ProjectionElem::Index(local) = proj {
            if prefix_is_deref && let Some(ref prov) = base.provenance {
                let alloc_id = prov.alloc_id;
                // The base's type may have been overwritten to the
                // element type by the Deref strip above; recover the
                // pointee element type from the base local's declared
                // type (`&[u8]` → `u8`, `&[T; N]` → `T`).
                let decl_ty = self.body().local_decls[place.local].ty;
                let inner_ty = match decl_ty.kind() {
                    rustc_middle::ty::TyKind::Array(inner, _) => *inner,
                    rustc_middle::ty::TyKind::Ref(_, inner, _) => match inner.kind() {
                        rustc_middle::ty::TyKind::Slice(e) => *e,
                        _ => return Some(base.clone()),
                    },
                    rustc_middle::ty::TyKind::Slice(e) => *e,
                    _ => return Some(base.clone()),
                };
                let elem_sz = self.size_of_ty(inner_ty) as usize;
                let step = elem_sz.max(1);
                if let Some(index_val) = self.local_value(*local) {
                    let offset = Int::mul(
                        self.z3_ctx,
                        &[&index_val.z3_term, &Int::from_u64(self.z3_ctx, step as u64)],
                    );
                    // Byte-level tracking only exists once some byte of the
                    // allocation has been written; otherwise fall through to
                    // the field→byte materialization below.  Even when the
                    // allocation has a byte array, the byte may still read
                    // `UNINIT` (e.g. a struct whose fields were written in
                    // the value layer only), so also fall through to the
                    // field→byte materialization in that case.
                    if self.units[alloc_id.0].content.byte_array.is_some() {
                        let term = self.byte_read(alloc_id, &offset);
                        let is_uninit = offset
                            .simplify()
                            .as_u64()
                            .map(|off| !self.is_byte_init(alloc_id, off as usize))
                            .unwrap_or(false);
                        if !is_uninit {
                            return Some(VmValue {
                                z3_term: term,
                                ty: place_ty,
                                provenance: None,
                                facts: ValueFacts::default(),
                                source: ValueSource::None,
                            });
                        }
                    }
                    // Field→byte direction of the cast cross-view
                    // materialization: the buffer was reinterpreted from a
                    // struct whose scalar fields were written in the value
                    // layer, so read the byte back out of the field value.
                    if let Some(off) = offset.simplify().as_u64()
                        && let Some(ty) = self.alloc(alloc_id).element_ty.as_ty()
                        && let Some(b) = self.byte_from_field(alloc_id, ty, off as usize)
                    {
                        return Some(VmValue {
                            z3_term: b,
                            ty: place_ty,
                            provenance: None,
                            facts: ValueFacts::default(),
                            source: ValueSource::None,
                        });
                    }
                }
            }
            return Some(self.unknown_value_for_place(place));
        }
        if !field_path.is_empty()
            && matches!(place_ty.kind(), TyKind::Int(_) | TyKind::Uint(_) | TyKind::Bool | TyKind::Char | TyKind::Float(_))
        {
            return Some(self.unknown_value_for_place(place));
        }
        let mut val = base;
        val.ty = place_ty;
        Some(val)
    }

    /// Whether `field_path` selects a length field.
    fn is_len_field_read(&self, ty: Ty<'tcx>, field_path: &[usize]) -> bool {
        if field_path.is_empty() {
            return false;
        }
        let mut view_ty = match ty.kind() {
            rustc_middle::ty::TyKind::Ref(_, inner, _)
            | rustc_middle::ty::TyKind::RawPtr(inner, _) => match inner.kind() {
                rustc_middle::ty::TyKind::Slice(_) | rustc_middle::ty::TyKind::Str => {
                    return field_path == [1];
                }
                rustc_middle::ty::TyKind::Adt(..) => *inner,
                _ => return false,
            },
            rustc_middle::ty::TyKind::Adt(..) => ty,
            _ => return false,
        };
        if field_path.len() > 1
            && !matches!(view_ty.kind(), TyKind::Adt(adt, _) if crate::verify::api_classify::is_std_string(adt.did()))
        {
            return false;
        }
        for (index, &field_idx) in field_path.iter().enumerate() {
            let TyKind::Adt(adt, substs) = view_ty.kind() else {
                return false;
            };
            if !adt.is_struct() {
                return false;
            }
            let Some(field) = adt
                .non_enum_variant()
                .fields
                .get(rustc_abi::FieldIdx::from_usize(field_idx))
            else {
                return false;
            };
            if index + 1 == field_path.len() {
                return field.name.as_str() == "len";
            }
            view_ty = mir_utils::field_ty(self.tcx, field, substs);
        }
        false
    }

    pub(super) fn is_cap_field_read(&self, ty: Ty<'tcx>, field_path: &[usize]) -> bool {
        if field_path.is_empty() {
            return false;
        }
        let mut view_ty = match ty.kind() {
            TyKind::Ref(_, inner, _) | TyKind::RawPtr(inner, _) => *inner,
            _ => ty,
        };
        if !matches!(view_ty.kind(), TyKind::Adt(adt, _) if crate::verify::api_classify::is_std_vec(adt.did()) || crate::verify::api_classify::is_std_string(adt.did()))
        {
            return false;
        }
        for (index, &field_idx) in field_path.iter().enumerate() {
            let TyKind::Adt(adt, substs) = view_ty.kind() else {
                return false;
            };
            let Some(field) = adt
                .non_enum_variant()
                .fields
                .get(rustc_abi::FieldIdx::from_usize(field_idx))
            else {
                return false;
            };
            if index + 1 == field_path.len() {
                return field.name.as_str() == "cap";
            }
            view_ty = mir_utils::field_ty(self.tcx, field, substs);
        }
        false
    }

    /// Create an unknown value for a place.
    ///
    /// The value carries no `non_null` (or any other) assumption: a raw pointer
    /// whose provenance was lost may still be null, so assuming non-null here
    /// would let `NonNull`/null-guard checks pass unsoundly.
    pub(crate) fn unknown_value_for_place(&self, place: &Place<'tcx>) -> VmValue<'z3, 'tcx> {
        let ty = place.ty(self.body(), self.tcx).ty;
        VmValue::new(self.fresh_int("unknown"), ty)
    }
}
