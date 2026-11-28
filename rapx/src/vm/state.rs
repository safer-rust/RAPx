//! Supporting symbolic VM state types and operations.
//!
//! Symbolic values, memory allocations, and operations on [`VmExecutor`] live
//! here; the core state and its constructor are defined in the parent module.

use crate::def_ids::type_ids;
use crate::util::mir_utils;
use rustc_abi::VariantIdx;
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{Body, Local},
    ty::{Region, Ty, TyKind},
};
use z3::{
    SatResult, Solver,
    ast::{Array, Ast, Bool, Dynamic, Int},
};

use crate::compat::{FxHashMap, FxHashSet};
pub(crate) use super::VmExecutor;
use super::diagnostics::ActiveMirLocation;
use super::integer::{self, IntLayout};
use crate::util::def_use::PlaceKey;

/// Reserved field-path index for array repeats, not a valid element bound.
pub(crate) const ARRAY_INDEX_MAX: usize = usize::MAX;

/// Unique identifier for a VM allocation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct AllocId(pub usize);

/// Memory operations observed while executing a MIR path.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum MemoryEventKind {
    Drop,
    Use,
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct MemoryEvent {
    /// Allocation accessed by this event.
    pub alloc_id: AllocId,
    /// Whether this event drops or uses the allocation.
    pub kind: MemoryEventKind,
    /// Whether the allocation was already dead when this operation occurred.
    pub was_dead: bool,
    /// MIR item that caused the access, when known.
    pub site: Option<ActiveMirLocation>,
    /// MIR local used for the access.
    pub local: usize,
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
    /// Element index and byte stride; byte offset is `index · stride`.
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
    /// Offset structure; `None` means a base or an unclassified address calculation.
    pub offset_kind: Option<OffsetKind<'z3>>,
}

/// Value-level facts about a symbolic value (nullness, alignment, bounds, and
/// relationships to other values). These travel *with* the value — a
/// [`VmValue`] leaves its allocation when passed as an operand or stashed in
/// `InlineCtx::deferred_field_writes` — so they live on the value, not the
/// allocation. The allocation-level counterpart to `init` is
/// [`ContentFacts::initialized`]; the two facts are updated for their respective views.
///
/// `PartialEq`/`Eq` are deliberately *not* derived: `align_n` is a Z3 AST
/// whose equality is structural (`Z3_is_eq_ast`), not semantic, so comparing
/// two `ValueFacts` would silently report semantically-equal values as
/// unequal.
#[derive(Clone, Debug, Default)]
pub(crate) struct ValueFacts<'z3> {
    /// The pointer value is known to be non-null.
    pub non_null: bool,
    /// The pointer is known to be dangling.
    pub dangling: bool,
    /// The value is known to be initialized.
    pub init: bool,
    /// The pointer is known to stay within its allocation.
    pub in_bounds: bool,
    /// Slice bounds established for this index value by `InBound` contracts.
    pub index_bounds: Option<Box<Vec<IndexBoundFact<'z3>>>>,
    /// Known divisor `n` for which `z3_term % n == 0`, possibly symbolic.
    pub align_n: Option<Int<'z3>>,
    /// ID of the raw owner share carried by this pointer and its copies.
    pub into_raw_id: Option<usize>,
}

/// A checked slice/index relation carried by an index value when `SliceIndex` cannot be reduced to arithmetic.
#[derive(Clone, Debug)]
pub(crate) struct IndexBoundFact<'z3> {
    /// Symbolic identity of the slice whose bound was checked.
    pub slice_term: Int<'z3>,
    /// Slice length at the time of the bound check.
    pub slice_len: Int<'z3>,
    /// Backing allocation, when the slice has known provenance.
    pub slice_alloc: Option<AllocId>,
    /// Symbolic index licensed by the bound check.
    pub index_term: Int<'z3>,
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
    /// Rust type used to interpret the symbolic term.
    pub ty: Ty<'tcx>,
    /// Allocation origin and offset, when this is a pointer.
    pub provenance: Option<Provenance<'z3>>,
    /// Facts that travel with this value through copies and calls.
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

    /// Whether this value carries allocation provenance.
    pub(crate) fn has_provenance(&self) -> bool {
        self.provenance.is_some()
    }
}

/// Allocation category and optional element count.
#[derive(Clone, Debug)]
pub(crate) enum AllocKind<'z3> {
    /// A modeled object, such as a struct, scalar, or heap pointee.
    Object,
    /// Externally supplied storage without a recorded element count.
    External,
    /// A slice/array buffer with a known element count.
    Slice { len: Int<'z3> },
    /// External allocation with a known, possibly symbolic element count.
    ExternalSlice { len: Int<'z3> },
    /// Storage returned by a modeled allocation or reallocation call.
    Allocator { len: Option<Int<'z3>> },
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

/// Properties shared by every pointer element in the stored contents.
#[derive(Clone, Debug, Default)]
pub(crate) struct ElementPointerFacts<'z3, 'tcx> {
    /// Every element pointer points at a valid value of this type.
    pub target_ty: Option<Ty<'tcx>>,
    /// Every element pointer is aligned for this type.
    pub aligned_ty: Option<Ty<'tcx>>,
    /// Every element pointer backs at least this many values of the given type.
    pub allocated: Option<(Ty<'tcx>, Int<'z3>)>,
    /// Every element pointer has trusted ownership; aliasing is checked separately.
    pub own_pointees: bool,
}

/// An object or byte-range bound recorded on an allocation.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum AllocBoundFact<'z3, 'tcx> {
    /// Object bound; `len` is present only for slices and strings.
    Object { address: Int<'z3>, ty: Ty<'tcx>, len: Option<Int<'z3>> },
    /// Byte range beginning at `address` with length `size`.
    Bytes { address: Int<'z3>, size: Int<'z3> },
}

/// Per-allocation *content* facts: whether the allocation's contents are
/// readable (initialized), whether they were asserted to be a valid C string /
/// UTF-8, and whether they were licensed for `SplitTransmute` re-interpretation.
/// These describe the stored bytes/values, so they live on [`MemoryContent`]
/// next to that data, rather than on [`Allocation`].
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

/// A memory allocation: a stack local, a heap object, or external storage.
///
/// The allocation is stored in a [`MemoryUnit`] at index `AllocId.0` (an
/// `AllocId` is a monotonic counter that doubles as the vector index).
#[derive(Clone, Debug)]
pub(crate) struct Allocation<'z3, 'tcx> {
    /// Allocation category and optional element count.
    pub kind: AllocKind<'z3>,
    /// Symbolic base address.
    pub base: Int<'z3>,
    /// Size in bytes, possibly symbolic.
    pub size: Int<'z3>,
    /// Alignment in bytes, possibly symbolic for a generic type.
    pub align: Int<'z3>,
    /// Element type of the stored object or slice.
    pub element_ty: ElementTy<'tcx>,
    /// Pointer term licensed by an `Owning` precondition.
    pub owning: Option<Int<'z3>>,
    /// Assumed live region for external allocations; `None` grants no lifetime.
    pub liveness: Option<Region<'tcx>>,
    /// Object and byte-range bounds licensed by contracts.
    pub bounds: Vec<AllocBoundFact<'z3, 'tcx>>,
    /// Source allocation of a view; followed to find its aliasing root.
    pub parent: Option<AllocId>,
    /// Whether the allocation is dead after storage ends or a drop.
    pub dead: bool,
    /// Whether an unresolved `Fn*` call may have freed this allocation.
    pub function_var_may_free: bool,
    /// A destructor may have freed this allocation.
    pub drop_may_free: bool,
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
            kind,
            base,
            size,
            align,
            element_ty: element_ty.into(),
            owning: None,
            liveness: None,
            bounds: Vec::new(),
            parent: None,
            dead: false,
            function_var_may_free: false,
            drop_may_free: false,
        }
    }

    pub(crate) fn record_bound(&mut self, bound: AllocBoundFact<'z3, 'tcx>) {
        if !self.bounds.contains(&bound) {
            self.bounds.push(bound);
        }
    }

    /// Storage whose nullability and validity require explicit evidence.
    pub(crate) fn is_raw_storage(&self) -> bool {
        matches!(
            self.kind,
            AllocKind::External | AllocKind::ExternalSlice { .. } | AllocKind::Allocator { .. }
        )
    }

    pub(crate) fn is_allocator(&self) -> bool {
        matches!(self.kind, AllocKind::Allocator { .. })
    }

    /// Legacy external-allocation placeholder, not evidence of a byte extent.
    pub(crate) fn has_unbounded_size(&self) -> bool {
        self.is_raw_storage() && self.size.simplify().as_u64() == Some(i64::MAX as u64)
    }

    /// The slice/array element count, if this allocation is slice data.
    ///
    /// The length may be smaller than the allocation's capacity (for example,
    /// for `Vec`); `slice_len_from_value` can infer it from size when absent.
    pub(crate) fn slice_len(&self) -> Option<&Int<'z3>> {
        match &self.kind {
            AllocKind::Slice { len } | AllocKind::ExternalSlice { len } => Some(len),
            AllocKind::Allocator { len } => len.as_ref(),
            _ => None,
        }
    }

    /// Record a slice's logical length without changing its allocated size.
    pub(crate) fn set_slice_len(&mut self, len: Int<'z3>) {
        self.kind = match &self.kind {
            AllocKind::Allocator { .. } => AllocKind::Allocator { len: Some(len) },
            AllocKind::External | AllocKind::ExternalSlice { .. } => AllocKind::ExternalSlice { len },
            _ => AllocKind::Slice { len },
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
    /// The inlined callee has a generic-dependent constant call operand and an unresolved type argument.
    pub symbolic_generic_const_inline: bool,
    /// Terms from depth-limited calls; dependent checks become `Unknown`.
    pub inline_truncated_terms: FxHashSet<Int<'z3>>,
    /// Caller referent local for each inlined callee argument.
    pub arg_referents: Vec<Option<Local>>,
    /// `(caller local, field path, value)` writes replayed after frame restoration.
    pub deferred_field_writes: Vec<(Local, Vec<usize>, VmValue<'z3, 'tcx>)>,
    /// Alternative VM states produced by inline branches.
    pub pending_states: Vec<Box<VmExecutor<'z3, 'tcx>>>,
}

/// The extra semantics attached to a value, beyond its term/type/provenance.
///
/// A value carries one semantic origin, such as a field borrow, slice length,
/// enum discriminant, or arithmetic result. Operand sources support guard
/// inference and division reasoning.
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
    /// Original pointer relation for address checks; integer arithmetic grants no provenance.
    ExposedAddress { address: Int<'z3>, provenance: Provenance<'z3> },
    /// Borrow of a field path rooted at a caller local.
    FieldBorrow { base: Local, fields: Vec<usize> },
    /// A known enum discriminant.
    KnownDiscriminant(Int<'z3>),
    /// Variant whose payload fields are being written before `SetDiscriminant`.
    PendingEnumVariant(Int<'z3>),
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
/// anchored layers — lifecycle ([`Allocation`]), content ([`ContentFacts`]),
/// and value ([`ValueFacts`] on each [`VmValue`]) — see each type's doc.
#[derive(Clone)]
pub(crate) struct MemoryUnit<'z3, 'tcx> {
    /// Allocation identity, layout, and lifecycle facts.
    pub(crate) allocation: Allocation<'z3, 'tcx>,
    /// Bytes, typed values, and content facts stored in the allocation.
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
    /// Values written at symbolic array indices.
    pub(crate) indexed_elements: Vec<(Int<'z3>, VmValue<'z3, 'tcx>)>,
    /// Whether indexed writes invalidate fallback reads from typed fields.
    pub(crate) indexed_elements_modified: bool,
    /// Initialized prefix copied into this allocation, with its element type.
    pub(crate) copied_prefix: Option<(Ty<'tcx>, Int<'z3>)>,
    /// Initialization and validity facts about the stored contents.
    pub(crate) facts: ContentFacts<'tcx>,
    /// Properties of every pointer element stored here.
    pub(crate) element_facts: ElementPointerFacts<'z3, 'tcx>,
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

/// The frame-scoped subset of [`VmExecutor`]: the name → allocation binding keyed
/// by MIR `Local`, which the callee reuses, so it must be swapped out for the
/// duration of an inlined callee and swapped back afterwards.
///
/// # Agent Rules
/// Do not add new fields without human approval.
#[derive(Clone)]
pub(crate) struct FrameState<'tcx> {
    /// Function executed by this frame.
    pub(crate) current_def_id: DefId,
    /// Optimized MIR with this frame's selected generic arguments substituted, if available.
    pub(crate) instantiated_body: Option<&'tcx Body<'tcx>>,
    /// Stack allocation backing each MIR local and its field values.
    pub(crate) local_alloc: FxHashMap<Local, AllocId>,
}

/// Caller state parked during a path-replay call.
#[derive(Clone)]
pub(crate) struct SavedCallerFrame<'z3, 'tcx> {
    /// Caller MIR frame restored when the inlined callee returns.
    pub(crate) frame: FrameState<'tcx>,
    /// Caller locals used to bind trait-method `ensures` after inlining.
    pub(crate) postcondition_args: Vec<Option<Local>>,
    /// Caller frame's argument referents restored on return.
    pub(crate) arg_referents: Vec<Option<Local>>,
    /// Caller frame's pending field writes restored on return.
    pub(crate) deferred_writes: Vec<(Local, Vec<usize>, VmValue<'z3, 'tcx>)>,
}

/// A raw pointer's ownership share; pointer copies refer to the same entry.
#[derive(Clone)]
pub(crate) struct RawOwnerShare {
    /// Root allocation whose ownership was passed to a raw pointer.
    alloc_id: AllocId,
    /// Owner type reconstructed from this raw pointer.
    owner: DefId,
    /// Shares still available for reconstructing an owner.
    remaining_shares: usize,
}

impl<'z3, 'tcx> VmExecutor<'z3, 'tcx> {
    pub(crate) fn ownership_share(&self, value: &VmValue<'z3, 'tcx>, owner: DefId) -> Option<usize> {
        let transfer = self.path_state.raw_owner_shares.get(value.facts.into_raw_id?)?;
        (transfer.owner == owner
            && value
                .provenance_alloc_id()
                .is_some_and(|id| self.root_alloc(id) == transfer.alloc_id))
        .then_some(transfer.remaining_shares)
    }

    pub(crate) fn has_available_transfer(&self, alloc_id: AllocId) -> bool {
        let root = self.root_alloc(alloc_id);
        self.path_state.raw_owner_shares
            .iter()
            .any(|transfer| transfer.alloc_id == root && transfer.remaining_shares > 0)
    }

    pub(crate) fn begin_ownership_transfer(&mut self, local: Local, owner: DefId) {
        let Some(alloc_id) = self.local_value(local).and_then(|value| value.provenance_alloc_id()) else {
            return;
        };
        let id = self.path_state.raw_owner_shares.len();
        self.path_state.raw_owner_shares.push(RawOwnerShare {
            alloc_id: self.root_alloc(alloc_id),
            owner,
            remaining_shares: 1,
        });
        if let Some(mut value) = self.local_value(local).cloned() {
            value.facts.into_raw_id = Some(id);
            self.set_local(local, value);
        }
    }

    pub(crate) fn grant_ownership_share(&mut self, value: &VmValue<'z3, 'tcx>, owner: DefId) {
        if self.ownership_share(value, owner).is_some()
            && let Some(id) = value.facts.into_raw_id
        {
            self.path_state.raw_owner_shares[id].remaining_shares += 1;
        }
    }

    pub(crate) fn consume_ownership_share(
        &mut self,
        value: &VmValue<'z3, 'tcx>,
        owner: DefId,
        may_free: bool,
    ) {
        if self.ownership_share(value, owner).is_some()
            && let Some(id) = value.facts.into_raw_id
        {
            self.path_state.raw_owner_shares[id].remaining_shares =
                self.path_state.raw_owner_shares[id].remaining_shares.saturating_sub(1);
        }
        if may_free && let Some(alloc_id) = value.provenance_alloc_id() {
            self.alloc_mut(self.root_alloc(alloc_id)).drop_may_free = true;
        }
    }

    pub(crate) fn record_memory_drop(&mut self, alloc_id: AllocId, local: Local) {
        self.record_memory_event(alloc_id, local, MemoryEventKind::Drop);
        self.alloc_mut(alloc_id).dead = true;
    }

    pub(crate) fn record_memory_use(&self, alloc_id: AllocId, local: Local) {
        self.record_memory_event(alloc_id, local, MemoryEventKind::Use);
    }

    fn record_memory_event(&self, alloc_id: AllocId, local: Local, kind: MemoryEventKind) {
        if let Some(events) = &self.path_state.memory_events {
            events.borrow_mut().push(MemoryEvent {
                alloc_id,
                kind,
                was_dead: self.alloc(alloc_id).dead,
                site: self.path_state.diagnostics.active_mir,
                local: local.as_usize(),
            });
        }
    }

    /// Resolve integer width from the analysis target, including `isize`/`usize`.
    pub(crate) fn integer_layout(&self, ty: Ty<'tcx>) -> Option<IntLayout> {
        let signed = match ty.kind() {
            TyKind::Int(_) => true,
            TyKind::Uint(_) => false,
            _ => return None,
        };
        let (_, bytes) = mir_utils::type_layout(self.tcx, self.path_state.current_frame.current_def_id, ty)?;
        let bits = u16::try_from(bytes.checked_mul(8)?).ok()?;
        IntLayout::new(bits, signed)
    }

    pub(crate) fn scalar_bits_term(&self, ty: Ty<'tcx>, bits: u128) -> Option<Int<'z3>> {
        if matches!(ty.kind(), TyKind::Int(_) | TyKind::Uint(_)) {
            return self
                .integer_layout(ty)
                .map(|layout| layout.from_bits(self.z3_ctx, bits));
        }
        let bytes = self.size_of_ty(ty);
        if bytes == 0 || bytes > 16 {
            return None;
        }
        if bytes == 16 {
            return Some(self.u128_term(bits));
        }
        u64::try_from(bits)
            .ok()
            .map(|unsigned| Int::from_u64(self.z3_ctx, unsigned))
    }

    pub(crate) fn u128_term(&self, value: u128) -> Int<'z3> {
        integer::u128_term(self.z3_ctx, value)
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

    /// MIR for the current frame, preferring its selected generic instantiation.
    pub(crate) fn body(&self) -> &'tcx Body<'tcx> {
        self.body_for(self.path_state.current_frame.current_def_id)
    }

    pub(crate) fn body_for(&self, def_id: DefId) -> &'tcx Body<'tcx> {
        if def_id == self.path_state.current_frame.current_def_id
            && let Some(body) = self.path_state.current_frame.instantiated_body
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
        let location = self.path_state.diagnostics.location_label(self.tcx);
        self.path_state.diagnostics.record_unsupported(location.as_deref(), operation);
    }

    pub(crate) fn record_unsupported_effect(&mut self, effect: &str) {
        let location = self.path_state.diagnostics.location_label(self.tcx);
        self.path_state.diagnostics.record_unsupported_effect(location.as_deref(), effect);
    }

    pub(crate) fn record_missing_mir(&mut self, callee: DefId) {
        let location = self.path_state.diagnostics.location_label(self.tcx);
        self.path_state.diagnostics.record_missing_mir(location.as_deref(), &self.tcx.def_path_str(callee));
    }

    /// Capture the frame-scoped state before switching to an inlined callee.
    ///
    /// Both path replay and recursive inlining swap the function identity,
    /// instantiated body, and local allocation bindings together.
    pub(crate) fn enter_frame(
        &mut self,
        callee: DefId,
        body: Option<&'tcx Body<'tcx>>,
    ) -> FrameState<'tcx> {
        std::mem::replace(
            &mut self.path_state.current_frame,
            FrameState {
                current_def_id: callee,
                instantiated_body: body,
                local_alloc: FxHashMap::default(),
            },
        )
    }

    /// Restore the frame-scoped state after an inlined callee returns.
    pub(crate) fn restore_frame(&mut self, frame: FrameState<'tcx>) {
        self.path_state.current_frame = frame;
    }

    /// Look up the whole value bound to a MIR local (its `path == []` slot in
    /// the allocation backing the local).
    pub(crate) fn local_value(&self, local: Local) -> Option<&VmValue<'z3, 'tcx>> {
        let alloc_id = *self.path_state.current_frame.local_alloc.get(&local)?;
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
        self.ensure_local_allocation(local);
        let alloc_id = self.path_state.current_frame.local_alloc[&local];
        self.content_mut(alloc_id).facts.may_be_uninit = false;
        let view_ty = self.body().local_decls[local].ty;
        if matches!(view_ty.kind(), TyKind::Adt(def, _)
            if type_ids::is_std_vec(def.did()))
            && value.provenance.as_ref().is_none_or(|prov| {
                let source = self.alloc(prov.alloc_id);
                matches!(source.kind, AllocKind::Object)
                    && matches!(source.element_ty.as_ty(), Some(ty)
                        if matches!(ty.kind(), TyKind::Adt(source_def, _)
                            if type_ids::is_std_vec(source_def.did())))
            })
        {
            value.provenance = Some(Provenance {
                alloc_id,
                offset: Int::from_u64(self.z3_ctx, 0),
                offset_kind: None,
            });
        }
        if matches!(view_ty.kind(), TyKind::Adt(def, _)
            if type_ids::is_maybe_uninit_type(def.did()))
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
        if is_array && let Some(&alloc_id) = self.path_state.current_frame.local_alloc.get(&local) {
            let content = self.content_mut(alloc_id);
            let was_tracked = content.indexed_elements_modified || !content.indexed_elements.is_empty();
            content.indexed_elements.clear();
            content.indexed_elements_modified = was_tracked;
            content.values.retain(|(ty, path), _| *ty != view_ty || path.is_empty());
        }
    }

    /// Mark a value and its backing allocation as initialized when both apply.
    pub(crate) fn mark_initialized(&mut self, value: &mut VmValue<'z3, 'tcx>) {
        value.facts.init = true;
        if let Some(prov) = &value.provenance {
            self.content_mut(prov.alloc_id).facts.initialized = true;
        }
    }

    /// Get the symbolic address of a MIR local (its stack allocation's base).
    pub(crate) fn local_address(&mut self, local: Local) -> Int<'z3> {
        self.ensure_local_allocation(local);
        let id = self.path_state.current_frame.local_alloc[&local];
        self.path_state.mem_units[id.0].allocation.base.clone()
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

    /// Model external storage; nullability and extent require separate evidence.
    pub(crate) fn allocate_external(
        &mut self,
        size: Int<'z3>,
        align: Int<'z3>,
        element_ty: Option<Ty<'tcx>>,
    ) -> (AllocId, Int<'z3>) {
        self.allocate_internal(size, align, element_ty, AllocKind::External)
    }

    pub(crate) fn allocate_from_allocator(
        &mut self,
        size: Int<'z3>,
        align: Int<'z3>,
        element_ty: Option<Ty<'tcx>>,
    ) -> (AllocId, Int<'z3>) {
        self.allocate_internal(size, align, element_ty, AllocKind::Allocator { len: None })
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
        let id = AllocId(self.path_state.mem_units.len());
        let base = {
            let prefix = if matches!(kind, AllocKind::External | AllocKind::Allocator { .. }) { "ext" } else { "heap" };
            let name = format!("{prefix}_{}", id.0);
            Int::new_const(self.z3_ctx, name.as_str())
        };
        let alloc = Allocation::new(base.clone(), size, align, element_ty, kind);
        self.path_state.mem_units.push(MemoryUnit {
            allocation: alloc,
            content: MemoryContent::default(),
        });
        (id, base)
    }

    /// Indexed access to an allocation by its `AllocId` (the id is the index).
    pub(crate) fn alloc(&self, id: AllocId) -> &Allocation<'z3, 'tcx> {
        &self.path_state.mem_units[id.0].allocation
    }

    /// Mutable indexed access to an allocation by its `AllocId`.
    pub(crate) fn alloc_mut(&mut self, id: AllocId) -> &mut Allocation<'z3, 'tcx> {
        &mut self.path_state.mem_units[id.0].allocation
    }

    /// Indexed access to an allocation's contents by its `AllocId`.
    pub(crate) fn content(&self, id: AllocId) -> &MemoryContent<'z3, 'tcx> {
        &self.path_state.mem_units[id.0].content
    }

    /// Mutable indexed access to an allocation's contents by its `AllocId`.
    pub(crate) fn content_mut(&mut self, id: AllocId) -> &mut MemoryContent<'z3, 'tcx> {
        &mut self.path_state.mem_units[id.0].content
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
            if guard >= self.path_state.mem_units.len() {
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

    /// Constrain an incoming machine integer at its introduction. The original
    /// symbol keeps this domain after its parameter local is overwritten.
    pub(crate) fn fresh_integer_input(&mut self, prefix: &str, ty: Ty<'tcx>) -> Int<'z3> {
        let term = self.fresh_int(prefix);
        self.constrain_integer_input(&term, ty);
        term
    }

    pub(crate) fn constrain_integer_input(&mut self, term: &Int<'z3>, ty: Ty<'tcx>) {
        if let Some(layout) = self.integer_layout(ty) {
            self.path_state.constraints
                .assertions
                .push(layout.in_domain(self.z3_ctx, term));
        }
    }

    /// Get the value of a specific field within an aggregate local.
    ///
    /// Field values live in the allocation backing the local (the
    /// memory-contents layer [`MemoryContent::values`]), keyed by the local's declared
    /// type as the view type.  Returns `None` if the local has no allocation
    /// (the field was never materialized).
    pub(crate) fn field_value(&self, local: Local, path: &[usize]) -> Option<&VmValue<'z3, 'tcx>> {
        let alloc_id = *self.path_state.current_frame.local_alloc.get(&local)?;
        let view_ty = self.body().local_decls[local].ty;
        self.load_value(alloc_id, view_ty, path).or_else(|| {
            let mut candidates = vec![path.to_vec()];
            for position in (0..path.len()).rev() {
                if path[position] == ARRAY_INDEX_MAX {
                    continue;
                }
                let alternatives = candidates.clone();
                for mut candidate in alternatives {
                    candidate[position] = ARRAY_INDEX_MAX;
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
        let Some(&alloc_id) = self.path_state.current_frame.local_alloc.get(&local) else {
            return Vec::new();
        };
        let view_ty = self.body().local_decls[local].ty;
        self.path_state.mem_units[alloc_id.0]
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
        self.path_state.mem_units[alloc_id.0]
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
        self.path_state.current_frame
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
        let alloc_id = self.path_state.current_frame.local_alloc[&local];
        self.store_value(alloc_id, view_ty, path, value);
    }

    /// Discard slice bounds tied to a local whose index fields are being changed.
    pub(crate) fn clear_index_bounds(&mut self, local: Local) {
        let Some(&alloc_id) = self.path_state.current_frame.local_alloc.get(&local) else { return };
        let view_ty = self.body().local_decls[local].ty;
        if let Some(whole) = self.content_mut(alloc_id).values.get_mut(&(view_ty, Vec::new())) {
            whole.facts.index_bounds = None;
        }
    }

    pub(crate) fn write_local_path(
        &mut self,
        local: Local,
        path: Vec<usize>,
        value: VmValue<'z3, 'tcx>,
    ) {
        let written_ty = value.ty;
        let written_inner = matches!(self.body().local_decls[local].ty.kind(), TyKind::Adt(def, args)
            if type_ids::is_maybe_uninit_type(def.did())
                && args.first().and_then(|arg| arg.as_type()) == Some(value.ty))
            && !path.is_empty()
            && path.iter().all(|field| *field == 0)
            && value.facts.init;
        if !path.is_empty() { self.clear_index_bounds(local); }
        if path.is_empty() {
            self.invalidate_indexed_array(local);
            self.invalidate_field_descendants(local, &[]);
            self.set_local(local, value);
        } else {
            self.invalidate_field_descendants(local, &path);
            self.set_field_value(local, path, value);
            if written_inner && let Some(&alloc_id) = self.path_state.current_frame.local_alloc.get(&local) {
                self.content_mut(alloc_id).facts.written_pointee_ty = Some(written_ty);
            }
        }
    }

    pub(crate) fn invalidate_field_descendants(&mut self, local: Local, path: &[usize]) {
        if let Some(&alloc_id) = self.path_state.current_frame.local_alloc.get(&local) {
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
        for unit in &self.path_state.mem_units {
            let alloc = &unit.allocation;
            if !alloc.is_raw_storage() {
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
        let local_ids: Vec<Local> = self.path_state.current_frame.local_alloc.keys().copied().collect();
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
        for cond in &self.path_state.constraints.assertions {
            solver.assert(cond);
        }
    }

    pub(crate) fn path_implies(&self, condition: &Bool<'z3>) -> bool {
        if condition.simplify().as_bool() == Some(true) {
            return true;
        }
        let solver = Solver::new(self.z3_ctx);
        for assertion in &self.path_state.constraints.assertions {
            solver.assert(assertion);
        }
        solver.assert(&condition.not());
        super::integer_solver::check(&solver) == SatResult::Unsat
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
            if integer::natural_upper_bound(&value.z3_term, 5).is_none() {
                solver.assert(&value.z3_term.ge(&zero).simplify());
            }
        }
        if matches!(value.ty.kind(), rustc_middle::ty::TyKind::Bool) {
            let one = Int::from_u64(self.z3_ctx, 1);
            solver.assert(&value.z3_term.le(&one).simplify());
        }
        if matches!(value.ty.kind(), rustc_middle::ty::TyKind::Char) {
            let max = Int::from_u64(self.z3_ctx, 0x10FFFF);
            solver.assert(&value.z3_term.le(&max));
        }
    }
}

impl std::fmt::Debug for VmExecutor<'_, '_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("VmExecutor")
            .field("locals_count", &self.path_state.current_frame.local_alloc.len())
            .field("allocations_count", &self.path_state.mem_units.len())
            .field("assertions", &self.path_state.constraints.assertions.len())
            .finish()
    }
}
