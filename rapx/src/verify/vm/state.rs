//! Symbolic VM state types.
//!
//! The data structures that represent the symbolic execution state: symbolic
//! values and their invariants, memory allocations, and the full execution
//! state at a program point.

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{Body, Local, Operand, Place, ProjectionElem},
    ty::{Region, Ty, TyCtxt},
};
use z3::{
    Context,
    ast::{Array, Ast, Bool, Int},
};

use crate::compat::{FxHashMap, FxHashSet};
use crate::verify::{def_use::PlaceKey, path_extractor::Path};

/// Unique identifier for a heap or stack allocation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct AllocId(pub usize);

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
    /// Element index from element-strided arithmetic (`ptr.add(k)`); the byte
    /// offset is `element · S`.
    Element(Int<'z3>),
    /// A byte-strided or otherwise unclassifiable offset (`byte_add`).
    Byte,
}

/// Pointer provenance: which allocation, at what byte offset, and (when known)
/// what structure that offset has.
#[derive(Clone, Debug)]
pub(crate) struct Provenance<'z3> {
    /// The allocation this pointer derives from.
    pub alloc_id: AllocId,
    /// Byte offset from the allocation base (always present). A freshly created
    /// pointer to the base of an allocation has `offset = 0`.
    pub offset: Int<'z3>,
    /// The offset's structure. `None` means the pointer sits at the base
    /// (`offset == 0`) with no further structure; `Some(..)` records whether the
    /// offset is a compile-time field offset (`Field`), an element index from
    /// element-strided arithmetic (`Element`), or a byte-strided offset (`Byte`).
    pub offset_kind: Option<OffsetKind<'z3>>,
}

/// Known invariants about a symbolic value.
///
/// `PartialEq`/`Eq` are deliberately *not* derived: `align_n` is a Z3 AST
/// whose equality is structural (`Z3_is_eq_ast`), not semantic, so comparing
/// two `ValueInvariants` would silently report semantically-equal values as
/// unequal.
#[derive(Clone, Debug, Default)]
pub(crate) struct ValueInvariants<'z3> {
    pub non_null: bool,
    pub init: bool,
    pub in_bounds: bool,
    /// If Some(n), the value's term is known to satisfy `z3_term % n == 0`.
    /// Set by alignment guards, Mul by power-of-two, and type alignment.
    /// `n` is a Z3 term so that a generic type's alignment (a symbolic
    /// `align_T`) can be carried the same way as a concrete alignment.
    pub align_n: Option<Int<'z3>>,
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
    /// The Z3 integer term (address or scalar value, see struct docs).
    pub z3_term: Int<'z3>,
    /// Rust type, for layout queries.
    pub ty: Ty<'tcx>,
    /// Which allocation this pointer derives from and at what offset.
    pub provenance: Option<Provenance<'z3>>,
    /// Known constraints on this value.
    pub invariants: ValueInvariants<'z3>,
    /// Extra semantics (field offset, discriminant, comparison, or binary-op
    /// source); see [`ValueSource`].
    pub source: ValueSource<'z3>,
}

impl<'z3, 'tcx> VmValue<'z3, 'tcx> {
    pub(crate) fn new(term: Int<'z3>, ty: Ty<'tcx>) -> Self {
        VmValue {
            z3_term: term,
            ty,
            provenance: None,
            invariants: ValueInvariants::default(),
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
            ValueSource::Discriminant(d) => Some(d),
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

/// The shape of an allocation. Replaces the implicit `slice_len` / `is_external`
/// combination that previously encoded the kind. `element_ty` (typed vs untyped)
/// and `parent`/`slice_data` (sub-view / slice-ref edges) stay separate fields.
#[derive(Clone, Debug)]
pub(crate) enum AllocKind<'z3> {
    /// A single object: a `Box<T>` heap object, a struct, a scalar, or an
    /// untyped raw buffer.
    Object,
    /// A slice/array buffer with a known element count.
    Slice { len: Int<'z3> },
    /// An external raw-pointer parameter. `size` is an unconstrained symbolic
    /// term (the caller may pass any allocation); nullability is *not* stored
    /// here — it is tracked via the pointer term (`term == 0`) path conditions.
    External,
}

/// The type of an allocation's contents.
///
/// This replaces the previous `Option<Ty>` (whose `None` conflated two distinct
/// cases): `Typed` carries a concrete `Ty` — the element type of a slice, the
/// object type of a `Box<T>`/struct, or `u8` for a raw byte buffer — while
/// `Generic` marks a symbolic element type whose concrete `Ty` cannot be
/// determined (e.g. `from_raw_parts::<T>`; its `size` uses the shared symbolic
/// `sizeof_T` and its length must be materialized via `set_slice_len`).
#[derive(Clone, Debug)]
pub(crate) enum ContentTy<'tcx> {
    Typed(Ty<'tcx>),
    Generic,
}

impl<'tcx> ContentTy<'tcx> {
    /// The concrete type, if known.
    pub(crate) fn as_ty(&self) -> Option<Ty<'tcx>> {
        match self {
            ContentTy::Typed(t) => Some(*t),
            ContentTy::Generic => None,
        }
    }

    /// Whether the element type is symbolic/unknown (no concrete `Ty`).
    pub(crate) fn is_generic(&self) -> bool {
        matches!(self, ContentTy::Generic)
    }
}

impl<'tcx> From<Option<Ty<'tcx>>> for ContentTy<'tcx> {
    fn from(o: Option<Ty<'tcx>>) -> Self {
        match o {
            Some(t) => ContentTy::Typed(t),
            None => ContentTy::Generic,
        }
    }
}

/// Uniform facts about the *pointer elements* of a container, established by
/// `x.iter()` for_each invariants.
///
/// Each fact is a property every element pointer satisfies.  The facts are
/// anchored to the container's allocation (not the container value) because a
/// pointer loaded from the container resolves its provenance through this
/// allocation, so the checker finds the fact via the loaded pointer's
/// provenance.
#[derive(Clone, Debug, Default)]
pub(crate) struct ForEachFacts<'z3, 'tcx> {
    /// `Typed(iter(), T)`: every element pointer points at a valid `T`.
    pub target_ty: Option<Ty<'tcx>>,
    /// `Align(iter(), T)`: every element pointer is aligned to `align_of(T)`.
    pub aligned_ty: Option<Ty<'tcx>>,
    /// `Allocated(iter(), T, n)`: every element pointer backs `>= n` `T`
    /// elements (`n` may be symbolic).
    pub allocated: Option<(Ty<'tcx>, Int<'z3>)>,
    /// `Owning(iter())`: every element pointer is the sole owner of its
    /// pointee (mutually non-aliasing).  Established by the trusted invariant;
    /// the aliasing *check* of the invariant itself is done by the alias
    /// analysis, not by this flag.
    pub owning: bool,
}

/// A memory allocation: a stack local, a heap object (`Box`/`Vec`), or an
/// external raw-pointer placeholder.
///
/// The allocation is stored in [`Memory::allocations`] at index `AllocId.0`
/// (an `AllocId` is a monotonic counter that doubles as the vector index).
#[derive(Clone, Debug)]
pub(crate) struct Allocation<'z3, 'tcx> {
    // ── Shape (always present) ──
    /// Base address (fresh Z3 constant).
    pub base: Int<'z3>,

    /// Size in bytes (Z3 term, may be symbolic).
    pub size: Int<'z3>,

    /// Alignment in bytes (Z3 term, may be symbolic for a generic element
    /// type).
    pub align: Int<'z3>,

    /// Type of the allocation's contents (concrete `Ty` or symbolic `Generic`).
    pub element_ty: ContentTy<'tcx>,

    /// The allocation shape (object vs slice vs external).
    pub kind: AllocKind<'z3>,

    // ── Lifecycle ──
    /// Whether the allocation has been freed (StorageDead / Drop).
    pub dead: bool,

    /// Whether the allocation's contents hold an initialized (readable) value:
    /// a heap constructor (`Box::new`, `Vec`), a reference parameter's referent,
    /// a callee return, a `write`, `ValidCStr`, or const/static byte data.
    /// Stays `false` for uninitialized memory (`Box::new_uninit`,
    /// `MaybeUninit::uninit`).
    pub initialized: bool,

    /// The region this external allocation is assumed alive for, via an
    /// `Alive(p, 'a)` contract/invariant (or `'static` for `ValidCStr`/`Allocated`
    /// params/`'static` data).  Only consulted for *external* allocations, whose
    /// memory is owned by the caller (so `dead` carries no liveness guarantee):
    /// the checker rejects a use that demands a longer region than this.  `None`
    /// means no assumption — an external allocation then fails `Alive` unless
    /// grounded in a live reference; a VM-owned allocation is alive while
    /// `!dead` and never sets this.
    pub liveness: Option<Region<'tcx>>,

    // ── Content semantics ──
    /// Uniform facts about this allocation's pointer elements, established by
    /// `x.iter()` for_each invariants (`Typed`/`Align`/`Allocated`).
    pub for_each: ForEachFacts<'z3, 'tcx>,

    /// Whether this allocation was asserted valid C string via a `ValidCStr`
    /// contract fact / struct invariant (the "no interior NUL + terminal NUL"
    /// trust marker).
    pub cstr_trusted: bool,

    // ── Relationships (Option) ──
    /// The allocation a sub-view was derived from: a slice view created by
    /// `s[i..j]` / `s.get(range)`, `split_at` / `align_to` / `as_chunks`, or
    /// `from_raw_parts`. Each view is a fresh `AllocId` but a window onto the
    /// same memory as its source, so `root_alloc` follows this edge to group
    /// aliasing views. The address linkage back to the source lives in the
    /// pointer term (`parent_term + offset`) and provenance `offset`, not in
    /// base arithmetic.
    pub parent: Option<AllocId>,

    /// The *data* allocation of a two-part value, reached from the *header*
    /// allocation whose provenance the value carries. A `Vec`/`String`/`CString`
    /// value's provenance names its struct's stack slot, not the heap buffer it
    /// owns, so `as_ptr()`/`into_boxed_slice`/`drop`/mutation follow this edge
    /// to the buffer. A `&[T]` fat pointer's provenance already names the slice
    /// data, so this is redundant there.
    pub slice_data: Option<AllocId>,
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
            dead: false,
            initialized: false,
            liveness: None,
            for_each: ForEachFacts::default(),
            cstr_trusted: false,
            parent: None,
            slice_data: None,
        }
    }

    /// Whether this allocation models an external raw-pointer parameter.
    pub(crate) fn is_external(&self) -> bool {
        matches!(self.kind, AllocKind::External)
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
            AllocKind::Slice { len } => Some(len),
            _ => None,
        }
    }

    /// Mark this allocation as slice data with the given element count.
    /// Callers must keep `size == len * sizeof(element_ty)` consistent.
    pub(crate) fn set_slice_len(&mut self, len: Int<'z3>) {
        self.kind = AllocKind::Slice { len };
    }
}

/// Per-path facts, read afterwards by the property checker.
///
/// Most flags are latched at most once during path execution (a contract fact
/// or a recognized discriminant / bounds check); `reenter` is instead derived
/// from the input path in [`VmState::new`].  They are per-path state, not
/// per-step: once set they are never cleared within a path.  (`has_checked_bounds`
/// is additionally accumulated *across checkpoints* by the engine, which reads
/// it back into the next path's flags.)
#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct PathFacts {
    /// Whether the current path re-enters a block (loop-unrolled), which lets
    /// the checker exempt the unrolled iteration's "second drop".
    pub reenter: bool,
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

/// Scratch state for the *recursive* inlined-callee mechanism
/// ([`crate::verify::vm::call::exec_inline_call`]), which unwinds via the Rust
/// call stack, is bounded by `inline_depth`, and stashes its per-call bindings
/// in `arg_referents`/`deferred_field_writes`.
///
/// (The *path-replay* mechanism — `CalleeEntry`/`CalleeExit` items — keeps its
/// saved caller frames on [`VmState::caller_frames`] instead, which lives next to
/// [`VmState::current_frame`] to form the frame stack.)
///
/// # Deferring `&mut` writes across the inline frame
///
/// While the callee runs, the caller's `local_alloc` (the name → allocation
/// binding) is parked in the saved [`FrameState`], so a write through a `&mut`
/// argument cannot resolve the caller referent local by address and land in its
/// field values immediately.  `arg_referents` pre-resolves (before `save_frame`)
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
/// 1. Enter `bar`: `save_frame` parks `main`'s locals; `arg_referents[0] = x`.
/// 2. Run `bar`: `foo.field = 1` (`(*foo).field`) can no longer resolve `x` by
///    address (the caller's address map is gone), so it pushes `(x, [0], 1)`.
/// 3. Exit `bar`: `restore_frame` brings `main`'s locals back, then the deferred
///    write is replayed, giving `x.field == 1`.
#[derive(Default)]
pub(crate) struct InlineCtx<'z3, 'tcx> {
    /// Current inlining depth (nested inlined callees), bounded by
    /// `MAX_INLINE_DEPTH`.
    pub inline_depth: usize,
    /// During `exec_inline_call`, maps each callee argument index to the
    /// *caller* local its value points at (resolved from the reference's
    /// address term before the caller's address map is saved away).  Used by
    /// `exec_assign` to resolve `(*self).field = val` writes through a `&mut
    /// self` reborrow temp back to the caller's referent.
    pub arg_referents: Vec<Option<Local>>,
    /// Field writes through a `&mut` argument collected during
    /// `exec_inline_call`, replayed against the caller's field values after
    /// `restore_frame` (the caller's address map is parked while the callee
    /// runs).  Each entry is `(caller_local, field_path, value)`, where
    /// `caller_local` comes from `arg_referents` — the caller local the `&mut`
    /// argument points at, not the argument itself.
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
    /// A compile-time `offset_of!` field offset.
    FieldOffset,
    /// A symbolic enum discriminant (variant index).
    Discriminant(Int<'z3>),
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
    pub(crate) fn operands(&self) -> Option<(&Option<PlaceKey>, &Option<PlaceKey>, rustc_middle::mir::BinOp)> {
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

/// The object space: every allocation plus the per-allocation contents that are
/// keyed purely by `AllocId` (fields and byte state).
///
/// This is the *address/place* layer — the memory that values live in — kept
/// separate from [`FrameState`], which binds MIR locals (names) to values. An
/// `AllocId` doubles as the index into `allocations` (a fresh id is
/// `allocations.len()`), so the `AllocId`-keyed field/byte tables stay
/// consistent with the allocation vector.
#[derive(Default)]
pub(crate) struct Memory<'z3, 'tcx> {
    /// All known allocations, indexed by `AllocId`.
    pub(crate) allocations: Vec<Allocation<'z3, 'tcx>>,

    /// Per-allocation byte value function: `byte[i] = select(array, i)` for any
    /// (possibly symbolic) offset `i`.  Unwritten offsets read back the `UNINIT`
    /// sentinel, so `init`/`nul` are derived from `select`, not stored per byte.
    pub(crate) byte_arrays: FxHashMap<AllocId, Array<'z3>>,

    /// The highest concrete byte offset written to each allocation.  Z3 arrays
    /// cannot enumerate their stored indices, so this bounds the `0..=max` range
    /// the byte-level checkers iterate; `select != UNINIT` distinguishes written
    /// from unwritten offsets within that range.
    pub(crate) byte_max: FxHashMap<AllocId, usize>,

    /// The typed-value (Value) layer: (alloc_id, viewed_type, field_indices) →
    /// value, i.e. the value of a field *within an allocation* viewed as
    /// `viewed_type`.  The `viewed_type` distinguishes reinterprets of the same
    /// allocation under different ADTs (e.g. `LeafNode` vs `InternalNode` cast
    /// views), so field index `1` resolves to `parent_idx` under `LeafNode` and
    /// `edges` under `InternalNode` without colliding.  This is the alloc-keyed
    /// counterpart to the byte-level [`Self::byte_arrays`]; the Local-keyed
    /// `field_value`/`set_field_value` resolve a local's backing allocation and
    /// then read/write this layer.
    pub(crate) values: FxHashMap<(AllocId, Ty<'tcx>, Vec<usize>), VmValue<'z3, 'tcx>>,
}

/// Accumulated solver state for the current path.
///
/// `assertions` is the assertion stream fed to Z3; `term_caches` holds the
/// per-phenomenon term-provenance caches that keep expressions compact and
/// linear.  Everything is path-scoped and monotonic: it accumulates as the VM
/// steps and is never reset within a path (or across inlined frames).
#[derive(Default)]
pub(crate) struct Constraints<'z3, 'tcx> {
    /// Accumulated solver constraints along the current path: branch/guard
    /// constraints (`SwitchInt`/`Assert`), API preconditions, and symbolic
    /// layout facts (`sizeof_T`, `align_T`).  Asserted into the solver by
    /// [`VmState::assert_all`] and by the property checker's feasibility
    /// queries.
    pub(crate) assertions: Vec<Bool<'z3>>,

    /// Term-provenance caches that shape terms into a form Z3 can solve.
    pub(crate) term_caches: TermCaches<'z3, 'tcx>,
}

/// Term-provenance caches, one per phenomenon the VM must shape by hand.
///
/// Z3's nonlinear integer solver (NIA) cannot rewrite degree-3 products or
/// deeply-nested pointer chains, so the VM records the *semantic meaning* of a
/// symbol (what it divides, which iterator it indexes, …) and uses that
/// provenance later to emit a compact, degree-≤2 term instead.  Each cache is
/// independent — they share only the path-scoped, monotonic lifetime.
#[derive(Default)]
pub(crate) struct TermCaches<'z3, 'tcx> {
    /// `sizeof_T` for each generic type, one symbolic constant per type.  Keeps
    /// `ptr.add` strides, `access_bytes` element sizes, and allocation sizes
    /// consistent so that SMT can cancel the `S` factor in `InBound`.
    pub(crate) sizes: FxHashMap<Ty<'tcx>, Int<'z3>>,

    /// `align_T` for each generic type, one symbolic constant per type; linked
    /// to the size by the layout constraint `sizeof_T % align_T == 0`.
    pub(crate) aligns: FxHashMap<Ty<'tcx>, Int<'z3>>,

    /// Terms that are the result of a bitwise `Not` (two's-complement mask).
    /// Used to recognize `x & !(align-1)` alignment patterns in BitAnd so we
    /// can derive `align = -mask` and emit linear bounds for the result.
    pub(crate) not_mask_terms: FxHashSet<Int<'z3>>,

    /// `quotient → dividend` for each *exact* division (`lhs % rhs == 0`),
    /// recording which size each `exact_div` symbol divides (e.g. `us` →
    /// `sizeof_T`).  Lets a later `us_len = (len / ts) * us` multiplication
    /// emit the byte bound `us_len * sizeof_U <= len * sizeof_T`.
    pub(crate) exact_div_roots: FxHashMap<Int<'z3>, Int<'z3>>,

    /// `quotient → (lhs, rhs)` for each *non-exact* division, recovering the
    /// `len` and divisor (`ts`) operands at a following `us_len = (len / ts) * us`.
    pub(crate) div_roots: FxHashMap<Int<'z3>, (Int<'z3>, Int<'z3>)>,

    /// Per-iterator element index, keyed by the *buffer* the iterator walks
    /// (`end` field's provenance alloc id, which is frame-independent).  The
    /// value is `(offset, base_len)`: the current element index and the total
    /// element count (the end field's `Element` offset, `None` when unknown).
    /// Caching both keeps `next`/`len`/`is_empty` checks linear
    /// (`base_len - offset`) instead of a deeply-nested `((base + S) + S) …`
    /// pointer chain that Z3's NIA cannot reason about.
    pub(crate) iter_ptr_offset: FxHashMap<AllocId, (Int<'z3>, Option<Int<'z3>>)>,

    /// `UNINIT` sentinel byte value (≥ 256, outside the `u8` value range).
    /// The default element of every byte array; `select(array, i) != UNINIT`
    /// is how "byte `i` was written" is decided.
    pub(crate) uninit_byte: Option<Int<'z3>>,
}

/// The frame-scoped subset of [`VmState`]: everything keyed by MIR `Local` /
/// `PlaceKey`, which the callee reuses, so it must be swapped out for the
/// duration of an inlined callee and swapped back afterwards.
pub(crate) struct FrameState<'z3, 'tcx> {
    /// The function whose body we execute (the MIR is derived via
    /// [`VmState::body`]).
    pub(crate) current_def_id: DefId,

    /// Current whole value bound to each MIR local (its rvalue). This is the
    /// Local layer's name → value binding; the per-field values live in the
    /// Value layer ([`Memory::values`]).
    pub(crate) locals: FxHashMap<Local, VmValue<'z3, 'tcx>>,

    /// The stack allocation backing each local's place (lvalue identity). A
    /// local's field values live *in* that allocation (see [`Memory::values`],
    /// keyed `(AllocId, view_ty, path)` with the local's declared type as the
    /// view type), so there is no local-keyed field table here.
    pub(crate) local_alloc: FxHashMap<Local, AllocId>,
}

/// The full symbolic execution state at a program point.
///
/// Accumulates locals, allocations, and solver constraints as the VM steps
/// through retained MIR items. The Z3 context is borrowed so a single context
/// can be reused across property checks.
pub(crate) struct VmState<'z3, 'tcx> {
    // ── Shared handles (passed in at run start; not execution state, but
    //    needed to create terms and query types during checking)
    /// Shared Z3 context.
    pub(crate) z3_ctx: &'z3 Context,

    /// Compiler type context.
    pub(crate) tcx: TyCtxt<'tcx>,

    // ── Frame-scoped state (swapped on inline entry/exit; the exact set
    //    captured by [`Self::save_frame`])
    pub(crate) current_frame: FrameState<'z3, 'tcx>,

    // ── Path-scoped state (accumulates across the whole path, including
    //    inlined frames)
    /// Stack of saved caller frames for path-replay inlining
    /// (`CalleeEntry`/`CalleeExit` items).  Together with [`Self::current_frame`]
    /// (the current frame) it forms the call stack: entering an inlined callee
    /// moves the current frame here, exiting restores it.
    pub(crate) caller_frames: Vec<FrameState<'z3, 'tcx>>,

    /// The object space: allocations, per-byte state, and per-allocation fields.
    pub(crate) memory: Memory<'z3, 'tcx>,

    /// Solver constraints and term caches accumulated along the current path.
    pub(crate) constraints: Constraints<'z3, 'tcx>,

    /// Recursive-inlining scratch state (depth and per-call temporary bindings
    /// pushed/popped on inline entry/exit).
    pub(crate) inline: InlineCtx<'z3, 'tcx>,

    /// Per-path facts (latched while stepping, or derived in [`Self::new`]),
    /// read by the property checker.
    pub(crate) path_facts: PathFacts,
}

impl<'z3, 'tcx> VmState<'z3, 'tcx> {
    /// Create a fresh VM state for executing a path.
    pub(crate) fn new(
        z3_ctx: &'z3 Context,
        tcx: TyCtxt<'tcx>,
        path: &Path,
        caller_def_id: DefId,
    ) -> Self {
        // Derive the one path fact the checker needs after `run` (whether the
        // path re-enters a block); the raw `Path` itself is not kept.
        let reenter = path.reenters();
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
            z3_ctx,
            tcx,
            current_frame: FrameState {
                current_def_id: caller_def_id,
                locals: FxHashMap::default(),
                local_alloc: FxHashMap::default(),
            },
            caller_frames: Vec::default(),
            memory: Memory::default(),
            inline: InlineCtx::default(),
            constraints,
            path_facts: PathFacts {
                reenter,
                ..PathFacts::default()
            },
        }
    }

    /// The MIR body of the current function, derived from `current_def_id`.
    pub(crate) fn body(&self) -> &'tcx Body<'tcx> {
        self.tcx.optimized_mir(self.current_frame.current_def_id)
    }

    /// Capture the frame-scoped state before switching to an inlined callee.
    ///
    /// This is the single source of truth for *what* is frame-scoped: the whole
    /// [`FrameState`] (function identity, local bindings, and operand sources).
    /// Both inline mechanisms (`handle_callee_entry` in path replay and
    /// `exec_inline_call`) call this, so they can no longer drift apart.
    pub(crate) fn save_frame(&mut self) -> FrameState<'z3, 'tcx> {
        FrameState {
            current_def_id: self.current_frame.current_def_id,
            locals: std::mem::take(&mut self.current_frame.locals),
            local_alloc: std::mem::take(&mut self.current_frame.local_alloc),
        }
    }

    /// Restore the frame-scoped state after an inlined callee returns.
    pub(crate) fn restore_frame(&mut self, frame: FrameState<'z3, 'tcx>) {
        self.current_frame = frame;
    }

    /// Look up the value bound to a MIR local.
    pub(crate) fn local_value(&self, local: Local) -> Option<&VmValue<'z3, 'tcx>> {
        self.current_frame.locals.get(&local)
    }

    /// Bind a value to a MIR local.
    pub(crate) fn set_local(&mut self, local: Local, value: VmValue<'z3, 'tcx>) {
        self.current_frame.locals.insert(local, value);
    }

    /// Get the symbolic address of a MIR local (its stack allocation's base).
    pub(crate) fn local_address(&mut self, local: Local) -> Int<'z3> {
        self.ensure_local_allocation(local);
        let id = self.current_frame.local_alloc[&local];
        self.memory.allocations[id.0].base.clone()
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
        let id = AllocId(self.memory.allocations.len());
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
        self.memory.allocations.push(alloc);
        (id, base)
    }

    /// Indexed access to an allocation by its `AllocId` (the id is the index).
    pub(crate) fn alloc(&self, id: AllocId) -> &Allocation<'z3, 'tcx> {
        &self.memory.allocations[id.0]
    }

    /// Mutable indexed access to an allocation by its `AllocId`.
    pub(crate) fn alloc_mut(&mut self, id: AllocId) -> &mut Allocation<'z3, 'tcx> {
        &mut self.memory.allocations[id.0]
    }

    /// Whether `id` was asserted a valid C string via a `ValidCStr` contract
    /// fact / struct invariant.
    pub(crate) fn is_cstr_trusted(&self, id: AllocId) -> bool {
        self.alloc(id).cstr_trusted
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
            // A parent chain longer than the total allocation count means a
            // cycle; stop rather than loop forever.
            if guard > self.memory.allocations.len() {
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
    /// memory-contents layer [`Memory::values`]), keyed by the local's declared
    /// type as the view type.  Returns `None` if the local has no allocation
    /// (the field was never materialized).
    pub(crate) fn field_value(&self, local: Local, path: &[usize]) -> Option<&VmValue<'z3, 'tcx>> {
        let alloc_id = *self.current_frame.local_alloc.get(&local)?;
        let view_ty = self.body().local_decls[local].ty;
        self.load_value(alloc_id, view_ty, path)
    }

    /// Enumerate the field paths materialized for a local: every `path` for
    /// which [`Self::field_value`] currently returns a value (the local's
    /// allocation's fields under its declared view type).
    pub(crate) fn field_paths(&self, local: Local) -> Vec<Vec<usize>> {
        let Some(&alloc_id) = self.current_frame.local_alloc.get(&local) else {
            return Vec::new();
        };
        let view_ty = self.body().local_decls[local].ty;
        self.memory
            .values
            .keys()
            .filter(|(a, t, _)| *a == alloc_id && *t == view_ty)
            .map(|(_, _, p)| p.clone())
            .collect()
    }

    /// The declared type of `local` in `frame`'s body.
    fn frame_local_ty(&self, frame: &FrameState<'z3, 'tcx>, local: Local) -> Ty<'tcx> {
        self.tcx.optimized_mir(frame.current_def_id).local_decls[local].ty
    }

    /// Enumerate the field paths materialized for `local` in a saved caller
    /// `frame`. Field values live in the path-scoped [`Memory::values`], so they
    /// are read via `frame`'s `local_alloc` and declared type.
    pub(crate) fn frame_field_paths(
        &self,
        frame: &FrameState<'z3, 'tcx>,
        local: Local,
    ) -> Vec<Vec<usize>> {
        let Some(&alloc_id) = frame.local_alloc.get(&local) else {
            return Vec::new();
        };
        let view_ty = self.frame_local_ty(frame, local);
        self.memory
            .values
            .keys()
            .filter(|(a, t, _)| *a == alloc_id && *t == view_ty)
            .map(|(_, _, p)| p.clone())
            .collect()
    }

    /// Read a field of `local` in a saved caller `frame`.
    pub(crate) fn frame_field_value(
        &self,
        frame: &FrameState<'z3, 'tcx>,
        local: Local,
        path: &[usize],
    ) -> Option<&VmValue<'z3, 'tcx>> {
        let alloc_id = *frame.local_alloc.get(&local)?;
        let view_ty = self.frame_local_ty(frame, local);
        self.load_value(alloc_id, view_ty, path)
    }

    /// The buffer an `Iter`/`IterMut` at `local` walks: the provenance of its
    /// `end` field.  This is frame-independent (the buffer allocation is
    /// path-scoped), unlike the `local` itself, so it keys the per-iterator
    /// element index in [`TermCaches::iter_ptr_offset`].
    pub(crate) fn iter_buffer(&self, local: Local) -> Option<AllocId> {
        self.field_value(local, &[1])
            .and_then(|end| end.provenance.as_ref())
            .map(|ep| ep.alloc_id)
    }

    /// The byte buffer walked by an iterator at `local`, possibly wrapped in
    /// adapter types (`Cloned`/`Rev`/…).  `Rvalue::Aggregate` flattens nested
    /// adapters, so the innermost `Iter`/`IterMut` `end` pointer is any tracked
    /// field whose path ends in `[1]`.  Return its allocation and end offset
    /// (the end offset doubles as the byte length when the element is `u8`).
    pub(crate) fn iter_utf8_buffer(&self, local: Local) -> Option<(AllocId, Int<'z3>)> {
        let mut best: Option<(usize, AllocId, Int<'z3>)> = None;
        for path in self.field_paths(local) {
            if path.last() != Some(&1) {
                continue;
            }
            let Some(v) = self.field_value(local, &path) else {
                continue;
            };
            let Some(prov) = v.provenance.as_ref() else {
                continue;
            };
            if best.as_ref().map_or(true, |(depth, _, _)| path.len() < *depth) {
                best = Some((path.len(), prov.alloc_id, prov.offset.clone()));
            }
        }
        best.map(|(_, id, off)| (id, off))
    }

    /// The field carrying an owned value's heap pointer (`Box.0.0`/`Vec.0.0`,
    /// and for nested owners like `String` the deeper data field). Prefer the
    /// canonical `[0, 0]`; fall back to the first field with heap provenance.
    pub(crate) fn owner_ptr_field(&self, local: Local) -> Option<&VmValue<'z3, 'tcx>> {
        self.field_value(local, &[0, 0])
            .filter(|v| v.provenance_alloc_id().is_some())
            .or_else(|| {
                self.field_paths(local)
                    .iter()
                    .find_map(|path| {
                        self.field_value(local, path)
                            .filter(|v| v.provenance_alloc_id().is_some())
                    })
            })
    }

    /// Invalidate `local`'s owner-field provenance (mark it moved-out after a
    /// whole-place move), so a later `Owning` check does not treat it as a
    /// second owner of the heap allocation it no longer owns.
    pub(crate) fn invalidate_owner_field(&mut self, local: Local) {
        // Only the canonical `[0, 0]` owner field (`Box`/`Vec`/`String`'s heap
        // pointer) is invalidated on a move.  The previous fallback that
        // scanned *any* field with provenance wrongly matched non-owning
        // pointer fields (e.g. `IterMut`'s `ptr`/`end`, which view a slice
        // rather than own it) and clobbered their provenance.
        if self
            .field_value(local, &[0, 0])
            .is_some_and(|v| v.provenance_alloc_id().is_some())
        {
            if let Some(mut fv) = self.field_value(local, &[0, 0]).cloned() {
                fv.provenance = None;
                self.set_field_value(local, vec![0, 0], fv);
            }
        }
    }

    /// Set the value of a specific field within an aggregate local.
    ///
    /// Ensures the local has a backing allocation, then stores into the
    /// memory-contents layer ([`Memory::values`]) keyed by the local's declared
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

    /// Assert path conditions and invariant constraints into a solver.
    pub(crate) fn assert_all(&self, solver: &z3::Solver<'z3>) {
        for cond in &self.constraints.assertions {
            solver.assert(cond);
        }
        let zero = Int::from_u64(self.z3_ctx, 0);
        for alloc in &self.memory.allocations {
            if !alloc.is_external() {
                solver.assert(&alloc.base._eq(&zero).not());
            }
            solver.assert(&alloc.size.ge(&zero));
            if alloc.align.simplify().as_u64() != Some(1) {
                solver.assert(&alloc.base.rem(&alloc.align)._eq(&zero));
            }
        }

        for (_local, value) in self.current_frame.locals.iter() {
            self.assert_value_constraints(solver, value);
        }
        // Field values live in the memory-contents layer; assert the constraints
        // of the *current frame's* fields (keyed by each local's allocation and
        // declared view type) — the M1 translation of the old frame-scoped
        // `field_values` iteration.
        let local_ids: Vec<Local> = self.current_frame.local_alloc.keys().copied().collect();
        for local in local_ids {
            for path in self.field_paths(local) {
                if let Some(value) = self.field_value(local, &path) {
                    self.assert_value_constraints(solver, value);
                }
            }
        }
    }

    /// Assert a single symbolic value's known invariant constraints.
    fn assert_value_constraints(&self, solver: &z3::Solver<'z3>, value: &VmValue<'z3, 'tcx>) {
        let zero = Int::from_u64(self.z3_ctx, 0);
        if value.invariants.non_null {
            solver.assert(&value.z3_term._eq(&zero).not());
        }
        if let Some(ref prov) = value.provenance {
            let alloc = self.alloc(prov.alloc_id);
            let expected = Int::add(self.z3_ctx, &[&alloc.base, &prov.offset]);
            solver.assert(&value.z3_term._eq(&expected));
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
            .field("locals_count", &self.current_frame.locals.len())
            .field("allocations_count", &self.memory.allocations.len())
            .field("assertions", &self.constraints.assertions.len())
            .finish()
    }
}

// ── Shared value extraction ──────────────────────────────────────

impl<'z3, 'tcx> VmState<'z3, 'tcx> {
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
                    let def_name = self.tcx.def_path_str(uneval.def);
                    let is_size = def_name.ends_with("SizedTypeProperties::SIZE");
                    let is_align = def_name.ends_with("SizedTypeProperties::ALIGN");
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
                let int_val = crate::helpers::mir_utils::eval_const_scalar_int(
                    self.tcx,
                    &constant.const_,
                    &text,
                );
                let field_offset = int_val.is_none()
                    && crate::helpers::mir_utils::offset_of_container(self.tcx, &constant.const_)
                        .is_some();
                let term = if let Some(v) = int_val {
                    if v < 0 {
                        Int::from_i64(self.z3_ctx, v as i64)
                    } else {
                        Int::from_u64(self.z3_ctx, v as u64)
                    }
                } else {
                    // Create a deterministic name for const generics so
                    // multiple uses of the same parameter share one term.
                    let name = format!("const_{}", text.replace([':', '#', ' '], "_"));
                    Int::new_const(self.z3_ctx, name.as_str())
                };
                let ty = constant.const_.ty();
                VmValue {
                    z3_term: term,
                    ty,
                    provenance: None,
                    invariants: ValueInvariants::default(),
                    source: if field_offset {
                        ValueSource::FieldOffset
                    } else {
                        ValueSource::None
                    },
                }
            }
            #[cfg(rapx_ge_95)]
            Operand::RuntimeChecks(_) => VmValue::new(
                self.fresh_int("runtime_checks"),
                self.body().local_decls[Local::from_usize(0)].ty,
            ),
        }
    }

    /// Look up the value stored at a MIR place.
    pub(crate) fn value_of_place(&self, place: &Place<'tcx>) -> Option<VmValue<'z3, 'tcx>> {
        if place.projection.is_empty() {
            return self.current_frame.locals.get(&place.local).cloned();
        }
        let place_ty = place.ty(self.body(), self.tcx).ty;

        // Collect field indices from projections
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
            if !has_downcast {
                // Fallback: when the base local has provenance, propagate it
                // to field accesses. This handles pointer-wrapper types (Box,
                // Unique, NonNull) where accessing inner pointer fields yields
                // the same provenance as the container.
                if let Some(base_val) = self.current_frame.locals.get(&place.local) {
                    if let Some(ref prov) = base_val.provenance {
                        return Some(VmValue {
                            z3_term: base_val.z3_term.clone(),
                            ty: place_ty,
                            provenance: Some(prov.clone()),
                            invariants: base_val.invariants.clone(),
                            source: ValueSource::None,
                        });
                    }
                }
                return None;
            }
            // A Downcast without a materialized field falls through to the
            // Deref+Field / multi-element fallback below, which returns the
            // base local (preserving the pre-Downcast behavior instead of
            // forcing a fresh value).
        }

        // For Deref+Field chains (e.g. (*self).ptr), strip the leading Deref
        // projection(s) and look up the field values with the remaining path.
        if !field_path.is_empty()
            && field_path.len() < place.projection.len()
            && place
                .projection
                .iter()
                .any(|p| matches!(p.kind(), ProjectionElem::Deref))
        {
            // Only Deref and Field projections — all non-Field must be Deref
            // (a full-range `Subslice` (`arr[..]`) is transparent: it converts
            // `[T; N]` → `[T]` without changing which field is selected, so
            // `(*ptr).edges[..]` still resolves to the `edges` field).
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
                if let Some(base_val) = self.current_frame.locals.get(&place.local) {
                    if let Some(alloc_id) = base_val.provenance_alloc_id() {
                        let view_ty = crate::helpers::mir_utils::pointee_ty(base_val.ty)
                            .unwrap_or(base_val.ty);
                        if let Some(val) = self.load_value(alloc_id, view_ty, &field_path).cloned() {
                            return Some(val);
                        }
                    }
                }
            }
        }

        // Handle Deref + Field projections: follow the dereference chain to
        // get the pointee base, then apply field offsets.
        // E.g. `(*self).ptr` → Deref then Field(0).
        let mut base = self.current_frame.locals.get(&place.local)?.clone();
        for proj in place.projection.iter() {
            match proj.kind() {
                ProjectionElem::Deref => {
                    base.ty = place_ty;
                }
                ProjectionElem::Field(_field_idx, _) => {
                    // Try to get the field value from the VM's field tracking
                    if !field_path.is_empty() {
                        if let Some(val) = self.field_value(place.local, &field_path).cloned() {
                            return Some(val);
                        }
                    }
                    // Fallback: return the base with updated type info
                    base.ty = place_ty;
                }
                _ => {}
            }
        }

        // Fall back to type-level resolution for an Index access whose prefix is
        // empty or only Deref projections (`arr[i]` / `(*slice)[i]`).
        if let Some(proj) = place.projection.last() {
            let prefix_is_deref = place.projection[..place.projection.len() - 1]
                .iter()
                .all(|p| matches!(p.kind(), ProjectionElem::Deref));
            if let ProjectionElem::Index(local) = proj {
                if prefix_is_deref {
                    if let Some(ref prov) = base.provenance {
                        let alloc_id = prov.alloc_id;
                        // Byte-level tracking only exists once some byte of the
                        // allocation has been written; otherwise fall back to the base.
                        if self.memory.byte_arrays.contains_key(&alloc_id) {
                            let inner_ty = {
                                // The base's type may have been overwritten to the
                                // element type by the Deref strip above; recover the
                                // pointee element type from the base local's declared
                                // type (`&[u8]` → `u8`, `&[T; N]` → `T`).
                                let decl_ty = self.body().local_decls[place.local].ty;
                                match decl_ty.kind() {
                                    rustc_middle::ty::TyKind::Array(inner, _) => *inner,
                                    rustc_middle::ty::TyKind::Ref(_, inner, _) => {
                                        match inner.kind() {
                                            rustc_middle::ty::TyKind::Slice(e) => *e,
                                            _ => return Some(base.clone()),
                                        }
                                    }
                                    rustc_middle::ty::TyKind::Slice(e) => *e,
                                    _ => return Some(base.clone()),
                                }
                            };
                            let elem_sz = self.size_of_ty(inner_ty) as usize;
                            let step = elem_sz.max(1);
                            if let Some(index_val) = self.current_frame.locals.get(local) {
                                // `arr[i]` = the byte at `i * size_of(elem)`; the array
                                // model resolves symbolic indices via `select` directly.
                                let offset = Int::mul(
                                    self.z3_ctx,
                                    &[&index_val.z3_term, &Int::from_u64(self.z3_ctx, step as u64)],
                                );
                                let term = self.byte_read(alloc_id, &offset);
                                return Some(VmValue {
                                    z3_term: term,
                                    ty: place_ty,
                                    provenance: None,
                                    invariants: ValueInvariants::default(),
                                    source: ValueSource::None,
                                });
                            }
                        }
                    }
                }
                return Some(base.clone());
                }
                match proj.kind() {
                    ProjectionElem::Deref => {
                        // A `*dest` load of a reference created from a field
                        // (`let r = &mut self.v`) should yield the field's
                        // *value* (materialized by `propagate_field_values_to_ref`
                        // at the empty field path), not the field's address.
                        if let Some(v) = self.field_value(place.local, &[]).cloned() {
                            return Some(v);
                        }
                        let mut val = base.clone();
                        val.ty = place_ty;
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
                        val.ty = place_ty;
                        return Some(val);
                    }
                }
            }

        // For multi-element projections with Deref+Field or Downcast, return
        // the base value since we already traced through Deref above.
        if place.projection.len() > 1
            && place.projection.iter().any(|p| {
                matches!(
                    p.kind(),
                    ProjectionElem::Deref | ProjectionElem::Downcast(..)
                )
            })
        {
            let mut val = base;
            val.ty = place_ty;
            return Some(val);
        }

        None
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
