#![feature(custom_mir, core_intrinsics, register_tool)]
#![register_tool(rapx)]
#![allow(dead_code, internal_features)]

use core::intrinsics::mir::*;

#[repr(isize)]
enum Choice {
    Zero = 4,
    One = 7,
}

#[repr(i8)]
enum SignedChoice {
    Negative = -1,
    Positive = 2,
}

#[repr(isize)]
enum Payload {
    First(u8),
    Second(u8),
    Pair(u8, u8),
}

#[rapx::requires(ValidNum(value == 7))]
unsafe fn expect_seven(value: isize) {}

#[rapx::requires(ValidNum(value == -1))]
unsafe fn expect_negative(value: i8) {}

#[rapx::requires(ValidNum(value == 9))]
unsafe fn expect_nine(value: u8) {}

#[rapx::verify]
#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn set_one_sound() {
    mir! {
        let value: Choice;
        let tag: isize;
        {
            place!(value) = Choice::Zero;
            SetDiscriminant(value, 1);
            tag = Discriminant(value);
            Call(RET = expect_seven(tag), ReturnTo(done), UnwindUnreachable())
        }
        done = {
            Return()
        }
    }
}

#[rapx::verify]
#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn set_zero_unsound() {
    mir! {
        let value: Choice;
        let tag: isize;
        {
            place!(value) = Choice::One;
            SetDiscriminant(value, 0);
            tag = Discriminant(value);
            Call(RET = expect_seven(tag), ReturnTo(done), UnwindUnreachable())
        }
        done = {
            Return()
        }
    }
}

#[rapx::verify]
#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn set_negative_sound() {
    mir! {
        let value: SignedChoice;
        let tag: i8;
        {
            place!(value) = SignedChoice::Positive;
            SetDiscriminant(value, 0);
            tag = Discriminant(value);
            Call(RET = expect_negative(tag), ReturnTo(done), UnwindUnreachable())
        }
        done = {
            Return()
        }
    }
}

#[rapx::verify]
#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn direct_one_sound() {
    mir! {
        let value: Choice;
        let tag: isize;
        {
            place!(value) = Choice::One;
            tag = Discriminant(value);
            Call(RET = expect_seven(tag), ReturnTo(done), UnwindUnreachable())
        }
        done = {
            Return()
        }
    }
}

#[rapx::verify]
#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn direct_negative_sound() {
    mir! {
        let value: SignedChoice;
        let tag: i8;
        {
            place!(value) = SignedChoice::Negative;
            tag = Discriminant(value);
            Call(RET = expect_negative(tag), ReturnTo(done), UnwindUnreachable())
        }
        done = {
            Return()
        }
    }
}

#[rapx::verify]
#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn set_negative_branch_sound() {
    mir! {
        let value: SignedChoice;
        let tag: i8;
        {
            place!(value) = SignedChoice::Positive;
            SetDiscriminant(value, 0);
            tag = Discriminant(value);
            match tag {
                -1 => negative,
                _ => other,
            }
        }
        negative = {
            Call(RET = expect_negative(tag), ReturnTo(done), UnwindUnreachable())
        }
        other = {
            Call(RET = expect_negative(2), ReturnTo(done), UnwindUnreachable())
        }
        done = {
            Return()
        }
    }
}

#[rapx::verify]
#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn set_payload_sound() {
    mir! {
        let value: Payload;
        let field: u8;
        {
            place!(Field(Variant(value, 1), 0)) = 9u8;
            SetDiscriminant(value, 1);
            field = Field(Variant(value, 1), 0);
            Call(RET = expect_nine(field), ReturnTo(done), UnwindUnreachable())
        }
        done = {
            Return()
        }
    }
}

#[rapx::verify]
#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn set_payload_incomplete_unknown() {
    mir! {
        let value: Payload;
        let field: u8;
        {
            place!(value) = Payload::First(9);
            SetDiscriminant(value, 1);
            field = Field(Variant(value, 1), 0);
            Call(RET = expect_nine(field), ReturnTo(done), UnwindUnreachable())
        }
        done = {
            Return()
        }
    }
}

#[rapx::verify]
#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn set_pair_sound() {
    mir! {
        let value: Payload;
        let field: u8;
        {
            place!(Field(Variant(value, 2), 0)) = 1u8;
            place!(Field(Variant(value, 2), 1)) = 9u8;
            SetDiscriminant(value, 2);
            field = Field(Variant(value, 2), 1);
            Call(RET = expect_nine(field), ReturnTo(done), UnwindUnreachable())
        }
        done = {
            Return()
        }
    }
}

#[rapx::verify]
#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn set_pair_partial_unknown() {
    mir! {
        let value: Payload;
        let field: u8;
        {
            place!(Field(Variant(value, 2), 1)) = 9u8;
            SetDiscriminant(value, 2);
            field = Field(Variant(value, 2), 1);
            Call(RET = expect_nine(field), ReturnTo(done), UnwindUnreachable())
        }
        done = {
            Return()
        }
    }
}

#[rapx::verify]
#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn set_payload_replaces_old_unsound() {
    mir! {
        let value: Payload;
        let field: u8;
        {
            place!(value) = Payload::First(9);
            place!(Field(Variant(value, 1), 0)) = 8u8;
            SetDiscriminant(value, 1);
            field = Field(Variant(value, 1), 0);
            Call(RET = expect_nine(field), ReturnTo(done), UnwindUnreachable())
        }
        done = {
            Return()
        }
    }
}

#[rapx::verify]
#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn set_payload_from_local_sound() {
    mir! {
        let value: Payload;
        let input: u8;
        let field: u8;
        {
            input = 9u8;
            place!(Field(Variant(value, 1), 0)) = input;
            SetDiscriminant(value, 1);
            field = Field(Variant(value, 1), 0);
            Call(RET = expect_nine(field), ReturnTo(done), UnwindUnreachable())
        }
        done = {
            Return()
        }
    }
}

#[rapx::verify]
#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn set_payload_from_uninit_unknown() {
    mir! {
        let value: Payload;
        let input: u8;
        let field: u8;
        {
            place!(Field(Variant(value, 1), 0)) = input;
            SetDiscriminant(value, 1);
            field = Field(Variant(value, 1), 0);
            Call(RET = expect_nine(field), ReturnTo(done), UnwindUnreachable())
        }
        done = {
            Return()
        }
    }
}

#[rapx::verify]
#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn set_payload_incomplete_branch_unknown() {
    mir! {
        let value: Payload;
        let tag: isize;
        let field: u8;
        {
            place!(value) = Payload::First(9);
            SetDiscriminant(value, 1);
            tag = Discriminant(value);
            match tag {
                1 => second,
                _ => other,
            }
        }
        second = {
            field = Field(Variant(value, 1), 0);
            Call(RET = expect_nine(field), ReturnTo(done), UnwindUnreachable())
        }
        other = {
            Call(RET = expect_nine(9), ReturnTo(done), UnwindUnreachable())
        }
        done = {
            Return()
        }
    }
}

#[rapx::verify]
#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn set_deref_local_sound() {
    mir! {
        let value: Choice;
        let pointer: &mut Choice;
        let tag: isize;
        {
            place!(value) = Choice::Zero;
            pointer = &mut value;
            SetDiscriminant(*pointer, 1);
            tag = Discriminant(value);
            Call(RET = expect_seven(tag), ReturnTo(done), UnwindUnreachable())
        }
        done = {
            Return()
        }
    }
}

#[rapx::verify]
#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn set_deref_arg_sound(value: &mut Choice) {
    mir! {
        let tag: isize;
        {
            SetDiscriminant(*value, 1);
            tag = Discriminant(*value);
            Call(RET = expect_seven(tag), ReturnTo(done), UnwindUnreachable())
        }
        done = {
            Return()
        }
    }
}

#[rapx::verify]
#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn set_deref_arg_unsound(value: &mut Choice) {
    mir! {
        let tag: isize;
        {
            SetDiscriminant(*value, 0);
            tag = Discriminant(*value);
            Call(RET = expect_seven(tag), ReturnTo(done), UnwindUnreachable())
        }
        done = {
            Return()
        }
    }
}

#[rapx::verify]
#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn set_deref_payload_sound(value: &mut Payload) {
    mir! {
        let field: u8;
        {
            place!(Field(Variant(*value, 1), 0)) = 9u8;
            SetDiscriminant(*value, 1);
            field = Field(Variant(*value, 1), 0);
            Call(RET = expect_nine(field), ReturnTo(done), UnwindUnreachable())
        }
        done = {
            Return()
        }
    }
}

#[rapx::verify]
#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn set_deref_payload_incomplete_unknown(value: &mut Payload) {
    mir! {
        let field: u8;
        {
            SetDiscriminant(*value, 1);
            field = Field(Variant(*value, 1), 0);
            Call(RET = expect_nine(field), ReturnTo(done), UnwindUnreachable())
        }
        done = {
            Return()
        }
    }
}

#[rapx::verify]
#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn set_deref_payload_local_sound() {
    mir! {
        let value: Payload;
        let pointer: &mut Payload;
        let field: u8;
        {
            place!(value) = Payload::First(1);
            pointer = &mut value;
            place!(Field(Variant(*pointer, 1), 0)) = 9u8;
            SetDiscriminant(*pointer, 1);
            field = Field(Variant(value, 1), 0);
            Call(RET = expect_nine(field), ReturnTo(done), UnwindUnreachable())
        }
        done = {
            Return()
        }
    }
}

#[rapx::verify]
#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn set_deref_payload_arg_unsound(value: &mut Payload) {
    mir! {
        let field: u8;
        {
            place!(Field(Variant(*value, 1), 0)) = 8u8;
            SetDiscriminant(*value, 1);
            field = Field(Variant(*value, 1), 0);
            Call(RET = expect_nine(field), ReturnTo(done), UnwindUnreachable())
        }
        done = {
            Return()
        }
    }
}

#[rapx::verify]
#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn set_deref_pair_partial_unknown(value: &mut Payload) {
    mir! {
        let field: u8;
        {
            place!(Field(Variant(*value, 2), 1)) = 9u8;
            SetDiscriminant(*value, 2);
            field = Field(Variant(*value, 2), 1);
            Call(RET = expect_nine(field), ReturnTo(done), UnwindUnreachable())
        }
        done = {
            Return()
        }
    }
}
