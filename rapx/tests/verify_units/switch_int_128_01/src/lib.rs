#![feature(custom_mir, core_intrinsics, register_tool)]
#![register_tool(rapx)]
#![allow(internal_features)]

use core::intrinsics::mir::*;

#[rapx::requires(ValidNum(value == 1))]
unsafe fn expect_one(value: u8) {}

#[rapx::verify]
#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn switch_u128_sound() {
    mir! {
        let tag: u128;
        {
            tag = 18446744073709551617u128;
            match tag {
                18446744073709551617u128 => good,
                _ => bad,
            }
        }
        good = {
            Call(RET = expect_one(1u8), ReturnTo(done), UnwindUnreachable())
        }
        bad = {
            Call(RET = expect_one(2u8), ReturnTo(done), UnwindUnreachable())
        }
        done = {
            Return()
        }
    }
}

#[rapx::verify]
#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn switch_i128_sound() {
    mir! {
        let tag: i128;
        {
            tag = -1i128;
            match tag {
                -1i128 => good,
                _ => bad,
            }
        }
        good = {
            Call(RET = expect_one(1u8), ReturnTo(done), UnwindUnreachable())
        }
        bad = {
            Call(RET = expect_one(2u8), ReturnTo(done), UnwindUnreachable())
        }
        done = {
            Return()
        }
    }
}

#[rapx::verify]
#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn switch_u128_unsound() {
    mir! {
        let tag: u128;
        {
            tag = 18446744073709551618u128;
            match tag {
                18446744073709551617u128 => good,
                _ => bad,
            }
        }
        good = {
            Call(RET = expect_one(1u8), ReturnTo(done), UnwindUnreachable())
        }
        bad = {
            Call(RET = expect_one(2u8), ReturnTo(done), UnwindUnreachable())
        }
        done = {
            Return()
        }
    }
}
