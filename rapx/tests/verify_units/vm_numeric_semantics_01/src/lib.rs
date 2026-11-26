#![feature(register_tool, core_intrinsics)]
#![register_tool(rapx)]
#![allow(internal_features)]

#[rapx::requires(ValidNum(_value == 1), kind = "precond")]
unsafe fn require_true(_value: u8) {}

#[rapx::requires(ValidNum(_value == 0), kind = "precond")]
unsafe fn require_false(_value: u8) {}

// Eager conjunction keeps both computations in the same MIR path.
macro_rules! both {
    ($left:expr, $right:expr) => {
        ((($left) as u8) & (($right) as u8)) != 0
    };
}

// Test the VM's computed result at an unconditional checkpoint on the guarded
// path. The result must satisfy one contract and violate its complement.
macro_rules! numeric_pair {
    ($sound:ident, $unsound:ident, $input:ident: $ty:ty, $value:expr, $condition:block) => {
        #[rapx::verify]
        pub fn $sound($input: $ty) {
            if $input == $value {
                let value: bool = $condition;
                unsafe { require_true(value as u8) };
            }
        }

        #[rapx::verify]
        pub fn $unsound($input: $ty) {
            if $input == $value {
                let value: bool = $condition;
                unsafe { require_false(value as u8) };
            }
        }
    };
}

// Both fields must survive copying an overflow tuple before projection.
numeric_pair!(sound_add_overflow_tuple, unsound_add_overflow_tuple, n: u8, 255, {
    let result = n.overflowing_add(1);
    let moved = result;
    let (value, overflow) = moved;
    both!(value == 0, overflow)
});
numeric_pair!(sound_sub_overflow_tuple, unsound_sub_overflow_tuple, n: u8, 0, {
    let result = n.overflowing_sub(1);
    let moved = result;
    let (value, overflow) = moved;
    both!(value == 255, overflow)
});
numeric_pair!(sound_mul_overflow_tuple, unsound_mul_overflow_tuple, n: u8, 16, {
    let result = n.overflowing_mul(16);
    let moved = result;
    let (value, overflow) = moved;
    both!(value == 0, overflow)
});
numeric_pair!(sound_add_no_overflow, unsound_add_no_overflow, n: u8, 7, {
    let (value, overflow) = n.overflowing_add(1);
    both!(value == 8, !overflow)
});
numeric_pair!(sound_signed_add_overflow, unsound_signed_add_overflow, n: i8, 127, {
    let (value, overflow) = n.overflowing_add(1);
    both!(value == -128, overflow)
});
numeric_pair!(sound_signed_sub_overflow, unsound_signed_sub_overflow, n: i8, -128, {
    let (value, overflow) = n.overflowing_sub(1);
    both!(value == 127, overflow)
});
numeric_pair!(sound_signed_mul_overflow, unsound_signed_mul_overflow, n: i8, -128, {
    let (value, overflow) = n.overflowing_mul(-1);
    both!(value == -128, overflow)
});

numeric_pair!(sound_narrow_cast, unsound_narrow_cast, n: u16, 256, {
    n as u8 == 0
});
numeric_pair!(sound_sign_extend, unsound_sign_extend, n: i8, -1, {
    n as i16 == -1
});
numeric_pair!(sound_zero_extend, unsound_zero_extend, n: u8, 255, {
    n as u16 == 255
});
numeric_pair!(sound_signed_to_unsigned, unsound_signed_to_unsigned, n: i8, -1, {
    n as u16 == 65535
});
numeric_pair!(sound_unsigned_to_signed, unsound_unsigned_to_signed, n: u8, 255, {
    n as i8 == -1
});

numeric_pair!(sound_signed_div_rem, unsound_signed_div_rem, n: i32, -3, {
    both!(n / 2 == -1, n % 2 == -1)
});
numeric_pair!(sound_negative_divisor, unsound_negative_divisor, n: i32, -3, {
    both!(n / -2 == 1, n % -2 == -1)
});
numeric_pair!(sound_positive_dividend, unsound_positive_dividend, n: i32, 3, {
    both!(n / -2 == -1, n % -2 == 1)
});
numeric_pair!(sound_unsigned_not, unsound_unsigned_not, n: u8, 0, {
    !n == 255
});
numeric_pair!(sound_signed_not, unsound_signed_not, n: i8, -1, {
    !n == 0
});
numeric_pair!(sound_boolean_not, unsound_boolean_not, n: bool, false, {
    !n
});
// n is not a power of two minus one: the former mask shortcut is invalid.
numeric_pair!(sound_arbitrary_mask, unsound_arbitrary_mask, n: i32, 2, {
    7 & !n == 5
});
numeric_pair!(sound_bitwise_or_xor, unsound_bitwise_or_xor, n: u8, 2, {
    (n | 8) ^ 1 == 11
});
numeric_pair!(sound_signed_ctlz, unsound_signed_ctlz, n: i8, -1, {
    core::intrinsics::ctlz(n) == 0
});
numeric_pair!(sound_signed_cttz, unsound_signed_cttz, n: i8, -2, {
    core::intrinsics::cttz(n) == 1
});

// The address is non-null, but the numeric result of subtracting it from
// itself is zero and does not overflow.
#[rapx::verify]
pub fn sound_address_subtraction() {
    let data = [7_u8];
    let addr = data.as_ptr() as usize;
    let (zero, overflow) = addr.overflowing_sub(addr);
    unsafe { require_true(both!(zero == 0, !overflow) as u8) };
}

#[rapx::verify]
pub fn unsound_address_subtraction() {
    let data = [7_u8];
    let addr = data.as_ptr() as usize;
    let (zero, overflow) = addr.overflowing_sub(addr);
    unsafe { require_false(both!(zero == 0, !overflow) as u8) };
}
