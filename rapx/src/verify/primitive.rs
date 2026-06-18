//! Primitive API classification for verifier transfer functions.
//!
//! The staged verifier still needs semantic summaries for compiler/std
//! primitives whose MIR body does not expose the address or memory effect we
//! want to reason about.  This module keeps the name-based recognition in one
//! small registry.  Higher layers translate the classified primitive into
//! dependency summaries, forward effects, and SMT assumptions.

/// Std/core primitive calls with verifier-specific transfer functions.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PrimitiveCall {
    AsPtr,
    AsMutPtr,
    PtrAdd,
    PtrSub,
    PtrOffset,
    PtrByteAdd,
    PtrByteSub,
    PtrByteOffset,
    PtrRead,
    PtrWrite,
    Len,
    MaybeUninitUninit,
    AlignOf,
    SizeOf,
}

impl PrimitiveCall {
    /// Classify a stable rustc def-path string as a known primitive call.
    pub fn classify(name: &str) -> Option<Self> {
        if name.ends_with("::as_ptr") || name.contains("::as_ptr") {
            return Some(Self::AsPtr);
        }
        if name.ends_with("::as_mut_ptr") || name.contains("::as_mut_ptr") {
            return Some(Self::AsMutPtr);
        }
        if name.contains("::byte_add") || name.contains("::wrapping_byte_add") {
            return Some(Self::PtrByteAdd);
        }
        if name.contains("::byte_sub") || name.contains("::wrapping_byte_sub") {
            return Some(Self::PtrByteSub);
        }
        if name.contains("::byte_offset") || name.contains("::wrapping_byte_offset") {
            return Some(Self::PtrByteOffset);
        }
        if name.contains("::add") || name.contains("::wrapping_add") {
            return Some(Self::PtrAdd);
        }
        if name.contains("::sub") || name.contains("::wrapping_sub") {
            return Some(Self::PtrSub);
        }
        if name.contains("::offset") || name.contains("::wrapping_offset") {
            return Some(Self::PtrOffset);
        }
        if name.contains("::read") || name.ends_with("read") {
            return Some(Self::PtrRead);
        }
        if (name.contains("::write") || name.ends_with("write"))
            && !name.contains("write_bytes")
            && !name.contains("write_unaligned")
            && !name.contains("write_volatile")
        {
            return Some(Self::PtrWrite);
        }
        if name.ends_with("::len") || name.contains("::len") {
            return Some(Self::Len);
        }
        if name.contains("MaybeUninit") && name.ends_with("::uninit") {
            return Some(Self::MaybeUninitUninit);
        }
        if name.contains("align_of") {
            return Some(Self::AlignOf);
        }
        if name.contains("size_of") {
            return Some(Self::SizeOf);
        }
        None
    }

    /// Return true for calls that extract a raw pointer from an aggregate.
    pub fn is_as_ptr_like(self) -> bool {
        matches!(self, Self::AsPtr | Self::AsMutPtr)
    }

    /// Return true for pointer arithmetic calls with `base + offset * stride`.
    pub fn is_pointer_add_like(self) -> bool {
        matches!(
            self,
            Self::PtrAdd | Self::PtrOffset | Self::PtrByteAdd | Self::PtrByteOffset
        )
    }

    /// Return true for pointer arithmetic calls with `base - offset * stride`.
    pub fn is_pointer_sub_like(self) -> bool {
        matches!(self, Self::PtrSub | Self::PtrByteSub)
    }

    /// Return true for any pointer arithmetic primitive.
    pub fn is_pointer_arithmetic(self) -> bool {
        matches!(
            self,
            Self::PtrAdd
                | Self::PtrSub
                | Self::PtrOffset
                | Self::PtrByteAdd
                | Self::PtrByteSub
                | Self::PtrByteOffset
        )
    }

    /// Return true when the arithmetic count is measured in bytes.
    pub fn is_byte_pointer_arithmetic(self) -> bool {
        matches!(
            self,
            Self::PtrByteAdd | Self::PtrByteSub | Self::PtrByteOffset
        )
    }

    /// Return true when the arithmetic count can be negative.
    pub fn is_signed_pointer_arithmetic(self) -> bool {
        matches!(self, Self::PtrOffset | Self::PtrByteOffset)
    }

    /// Return true for compile-time layout constant producers.
    pub fn is_layout_constant(self) -> bool {
        matches!(self, Self::AlignOf | Self::SizeOf)
    }
}
