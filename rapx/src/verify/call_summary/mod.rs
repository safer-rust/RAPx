//! Call summaries for the staged verifier: backward dependency (which call
//! arguments stay relevant) and forward effect (what facts a call adds).
pub(crate) mod effects;
mod dependencies;
pub(crate) mod callback;

pub(crate) use dependencies::dependency_summary;
pub(crate) use dependencies::callsite_write_args;
pub(crate) use dependencies::callsite_replaces_pointer_field;

/// Dependency summary consumed by the backward visitor.
#[derive(Clone, Debug)]
pub(crate) struct CallDependencySummary {
    /// If the call destination is relevant, these call arguments are relevant.
    pub return_depends_on_args: Vec<usize>,
    /// Arguments whose referents the callee may write.
    pub write_args: Vec<usize>,
    /// Arguments the backward slicer needs to model those writes.
    pub write_inputs: Vec<usize>,
}

impl CallDependencySummary {
    /// Conservative fallback: keep all arguments relevant.
    fn fallback(arg_count: usize) -> Self {
        Self {
            return_depends_on_args: (0..arg_count).collect(),
            write_args: Vec::new(),
            write_inputs: Vec::new(),
        }
    }
}

/// Effect summary consumed by the forward visitor.
pub(crate) type CallEffectSummary = Vec<CallEffect>;

/// Path-local effect produced by a retained call.
#[derive(Clone, Debug)]
pub(crate) enum CallEffect {
    /// The return value aliases or is a direct value flow from an argument.
    ReturnAliasArg { arg: usize },
    /// The return value is a transparent copy of an argument's *value*
    /// (`MaybeUninit::assume_init`, `ManuallyDrop::into_inner`): same term and
    /// facts, retyped to the destination — no pointer `non_null` forcing.
    ReturnArgValue { arg: usize },
    ReturnOpaque,
    ReturnSizeOfVal { arg: usize },
    ReturnRawEq { left_arg: usize, right_arg: usize },
    ReturnExactDiv { lhs_arg: usize, rhs_arg: usize },
    /// `select_unpredictable(cond, x, y)` returns either `x` or `y`: the result
    /// is one of the two candidate values (`args[1]`/`args[2]`), non-deterministic
    /// since the boolean selector (`args[0]`) is unpredictable.
    SelectUnpredictable,
    /// The return value is a pointer extracted from an aggregate/reference arg.
    ReturnWrappingPointerOffset { base_arg: usize, offset_arg: usize },
    ReturnPtrOffsetFrom { ptr_arg: usize, base_arg: usize },
    /// The return value is a concrete layout/numeric constant.
    ReturnConst { value: u64 },
    ReallocateVec { arg: usize },
    CopyMemory { source_arg: usize, destination_arg: usize, count_arg: usize },
    SwapMemory { left_arg: usize, right_arg: usize },
    FillBytes { pointer_arg: usize, byte_arg: usize, count_arg: usize },
    ReturnNullableAllocation { size_arg: usize, align_arg: usize, zeroed: bool },
    /// The return value is `min(lhs_arg, rhs_arg)`, satisfying
    /// `return <= lhs_arg` and `return <= rhs_arg`.
    ReturnMin { lhs_arg: usize, rhs_arg: usize },
    /// The return value is `max(lhs_arg, rhs_arg)`.
    ReturnMax { lhs_arg: usize, rhs_arg: usize },
    /// The return value is `lhs_arg + rhs_arg`.
    ReturnAdd { lhs_arg: usize, rhs_arg: usize },
    /// The return value is `lhs_arg * rhs_arg`.
    ReturnMul { lhs_arg: usize, rhs_arg: usize },
    ReturnBoundedArithmetic {
        lhs_arg: usize,
        rhs_arg: usize,
        op: BoundedArithmeticOp,
    },
    ReturnWithOverflow {
        lhs_arg: usize,
        rhs_arg: usize,
        op: OverflowOp,
    },
    /// The return value is non-zero *iff* `arg` is non-zero (models bit-manipulating
    /// intrinsics like `bswap`/`bitreverse`/`ctpop`/`rotate_*`, which map `0` to
    /// `0` and non-zero to non-zero).
    ReturnNonZeroIff { arg: usize },
    ReturnLeadingZeros { arg: usize },
    ReturnTrailingZeros { arg: usize },
    ReturnAlignOfVal { arg: usize },
    ReturnCompareBytes { left_arg: usize, right_arg: usize, count_arg: usize },
    ReturnMaskedPointer { pointer_arg: usize, mask_arg: usize },
    LoadMemory { pointer_arg: usize },
    StoreMemory { pointer_arg: usize, value_arg: usize },
    AtomicRmw { pointer_arg: usize },
    SimdCompare { lhs_arg: usize, rhs_arg: usize, op: SimdCmpOp },
    SimdArithmetic { lhs_arg: usize, rhs_arg: usize, op: SimdArithOp },
    SimdOpaque,
    SimdSplat { arg: usize },
    SimdExtract { vector_arg: usize, index_arg: usize },
    SimdInsert { vector_arg: usize, index_arg: usize, value_arg: usize },
    SimdHavocMemory { pointer_arg: usize, mask_arg: usize },
    SimdMaskedFallback { mask_arg: usize, fallback_arg: usize },
    SimdBitmask { arg: usize },
    /// The slice-to-Vec conversion creates a new allocation with the source length.
    ReturnVecFromSlice,
    /// `ptr.align_offset(align)` returns an offset such that
    /// `(ptr + offset) % align == 0` and `0 <= offset < align` (or `usize::MAX`
    /// when no such offset exists). Models `*const T::align_offset` /
    /// `*mut T::align_offset` by recording the alignment path-condition so
    /// downstream `ptr.add(offset)` dereferences can discharge `Align`.
    ReturnAlignOffset { ptr_arg: usize, align_arg: usize },
    /// `<ManuallyDrop<T> as Deref>::deref` / `MaybeDangling::as_ref` return a
    /// reference to the inner value at the *same* address (transparent
    /// wrappers).  The return aliases `arg` (a `&T` pointing at `arg`'s
    /// pointee) and its pointee field values are the argument's field values
    /// with the leading `peel` transparent field-0 hops stripped.
    ReturnTransparentDeref { arg: usize, peel: usize },
    /// `size_of::<T>()` / `align_of::<T>()` for a *generic* `T` (no concrete
    /// layout): the result is the shared symbolic `sizeof_T` / `align_T`, bound
    /// at apply time from `func`'s type argument.
    ReturnLayoutSymbolic { is_size: bool },
}

impl CallEffect {
    pub(super) fn written_args(&self) -> Vec<usize> {
        match self {
            Self::ReallocateVec { arg } => vec![*arg],
            Self::StoreMemory { pointer_arg, .. }
            | Self::AtomicRmw { pointer_arg }
            | Self::SimdHavocMemory { pointer_arg, .. }
            | Self::FillBytes { pointer_arg, .. } => vec![*pointer_arg],
            Self::CopyMemory { destination_arg, .. } => vec![*destination_arg],
            Self::SwapMemory { left_arg, right_arg } => vec![*left_arg, *right_arg],
            _ => Vec::new(),
        }
    }

    pub(super) fn write_inputs(&self) -> Vec<usize> {
        match self {
            Self::FillBytes { pointer_arg, byte_arg, count_arg } => {
                vec![*pointer_arg, *byte_arg, *count_arg]
            }
            Self::StoreMemory { pointer_arg, value_arg } => vec![*pointer_arg, *value_arg],
            Self::SimdHavocMemory { pointer_arg, mask_arg } => vec![*pointer_arg, *mask_arg],
            Self::AtomicRmw { pointer_arg } => vec![*pointer_arg, 1, 2],
            Self::CopyMemory { source_arg, destination_arg, count_arg } => {
                vec![*source_arg, *destination_arg, *count_arg]
            }
            _ => self.written_args(),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum OverflowOp {
    Add,
    Sub,
    Mul,
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum SimdCmpOp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum SimdArithOp {
    Add,
    Sub,
    Mul,
    SaturatingAdd,
    SaturatingSub,
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum BoundedArithmeticOp {
    SaturatingAdd,
    SaturatingSub,
    WrappingAdd,
    WrappingSub,
}
