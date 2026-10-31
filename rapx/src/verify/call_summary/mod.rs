//! Call summaries for the staged verifier: backward dependency (which call
//! arguments stay relevant) and forward effect (what facts a call adds).
pub(crate) mod effects;
mod dependencies;
pub(crate) mod callback;

pub(crate) use dependencies::dependency_summary;

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
    /// The returned `MaybeUninit<T>` wrapper is valid but its inner `T` is not initialized.
    ReturnUninitWrapper,
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
    /// The call writes one initialized element through a pointer argument.
    WriteMemory { pointer_arg: usize },
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
    /// The slice-to-Vec conversion creates a new allocation with the source length.
    ReturnVecFromSlice,
    /// The call is `Try::branch`: `Option<T>` -> `ControlFlow<Option<!>, T>`,
    /// so the result's `Continue` payload (field 0) equals the input's `Some`
    /// payload (field 0).  Models the `?` operator's `if let Some(..) = expr?`
    /// unwrap so the payload's provenance survives the branch.
    ReturnBranchPayload { arg: usize },
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
    /// The call *frees* the heap allocation behind `pointer_arg` (a `&mut`
    /// reference to a `Box`/`Vec`/`String` pointee). Models `ManuallyDrop::drop`.
    DropMemory { pointer_arg: usize },
    /// `Range<A>::next` / `RangeInclusive<A>::next`: return the current
    /// `start` and advance it by one, carrying the `start < end` bound so a
    /// downstream `InBound(arr, i)` can be discharged.
    ReturnRangeNext,
    /// `size_of::<T>()` / `align_of::<T>()` for a *generic* `T` (no concrete
    /// layout): the result is the shared symbolic `sizeof_T` / `align_T`, bound
    /// at apply time from `func`'s type argument.
    ReturnLayoutSymbolic { is_size: bool },
}

impl CallEffect {
    pub(super) fn written_args(&self) -> Vec<usize> {
        match self {
            Self::WriteMemory { pointer_arg }
            | Self::DropMemory { pointer_arg }
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
pub(crate) enum BoundedArithmeticOp {
    SaturatingAdd,
    SaturatingSub,
    WrappingSub,
}
