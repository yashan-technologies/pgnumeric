// Copyright 2020 CoD Team

//! Numeric conversion utilities.

use crate::error::NumericTryFromError;
use crate::{NumericDigit, NumericVar, NBASE, NUMERIC_NEG, NUMERIC_POS};
use std::ffi::CStr;
use std::mem::MaybeUninit;

/// Zero value.
pub trait Zero: Copy + PartialEq {
    const ZERO: Self;

    #[inline]
    fn is_zero(self) -> bool {
        self == Self::ZERO
    }
}

macro_rules! impl_zero {
    ($t: ty) => {
        impl Zero for $t {
            const ZERO: Self = 0;
        }
    };
}

impl_zero!(i8);
impl_zero!(i16);
impl_zero!(i32);
impl_zero!(i64);
impl_zero!(i128);
impl_zero!(u8);
impl_zero!(u16);
impl_zero!(u32);
impl_zero!(u64);
impl_zero!(u128);

/// Unsigned integer.
pub trait Unsigned: Copy + Zero + Sized {
    const MAX_NDIGITS: usize;

    fn next_digit(self) -> (NumericDigit, Self);
}

macro_rules! impl_unsigned {
    ($t: ty, $ndigits: expr) => {
        impl Unsigned for $t {
            const MAX_NDIGITS: usize = $ndigits;

            #[inline]
            fn next_digit(self) -> (NumericDigit, Self) {
                let new_val = self / NBASE as Self;
                let digit = (self - new_val * NBASE as Self) as NumericDigit;
                (digit, new_val)
            }
        }
    };
}

impl_unsigned!(u16, 2);
impl_unsigned!(u32, 3);
impl_unsigned!(u64, 5);
impl_unsigned!(u128, 10);

impl Unsigned for u8 {
    const MAX_NDIGITS: usize = 1;

    #[inline]
    fn next_digit(self) -> (NumericDigit, Self) {
        (self as NumericDigit, 0)
    }
}

/// Signed integer.
pub trait Signed: Copy + PartialOrd + Zero {
    type AbsType: Unsigned;

    fn is_negative(self) -> bool;
    fn abs(self) -> Self::AbsType;
}

macro_rules! impl_signed {
    ($t: ty, $abs_ty: ty) => {
        impl Signed for $t {
            type AbsType = $abs_ty;

            #[inline]
            fn is_negative(self) -> bool {
                self < 0
            }

            #[inline]
            fn abs(self) -> $abs_ty {
                if self >= 0 {
                    self as $abs_ty
                } else {
                    -(self + 1) as $abs_ty + 1
                }
            }
        }
    };
}

impl_signed!(i8, u8);
impl_signed!(i16, u16);
impl_signed!(i32, u32);
impl_signed!(i64, u64);
impl_signed!(i128, u128);

/// Converts a signed integer to numeric.
pub fn from_signed<T: Signed>(val: T) -> NumericVar {
    let mut var = NumericVar::nan();

    if val.is_negative() {
        var.sign = NUMERIC_NEG;
    } else {
        var.sign = NUMERIC_POS;
    }

    var.dscale = 0;
    if val.is_zero() {
        var.ndigits = 0;
        var.weight = 0;
        return var;
    }

    set_var_from_unsigned(&mut var, val.abs());

    var
}

/// Converts an unsigned integer to numeric.
pub fn from_unsigned<T: Unsigned>(val: T) -> NumericVar {
    let mut var = NumericVar::nan();

    var.sign = NUMERIC_POS;
    var.dscale = 0;
    if val.is_zero() {
        var.ndigits = 0;
        var.weight = 0;
        return var;
    }

    set_var_from_unsigned(&mut var, val);

    var
}

fn set_var_from_unsigned<T: Unsigned>(var: &mut NumericVar, val: T) {
    var.alloc(T::MAX_NDIGITS as i32);

    let mut u_val = val;
    let digits = var.digits_mut();
    let mut ndigits = 0;
    let mut i = digits.len();
    loop {
        i -= 1;
        ndigits += 1;

        let (digit, new_u_val) = u_val.next_digit();

        digits[i] = digit;
        u_val = new_u_val;

        if u_val.is_zero() {
            break;
        }
    }
    var.offset = var.buf.len() - ndigits as usize;
    var.ndigits = ndigits;
    var.weight = ndigits - 1;
}

/// Floating-point number.
pub trait Floating: Copy {
    const PRECISION: usize;

    fn is_nan(self) -> bool;
    fn is_infinite(self) -> bool;
    fn as_f64(self) -> f64;
}

macro_rules! impl_floating {
    ($t: ty, $precision: expr) => {
        impl Floating for $t {
            const PRECISION: usize = $precision;

            #[inline]
            fn is_nan(self) -> bool {
                self.is_nan()
            }

            #[inline]
            fn is_infinite(self) -> bool {
                self.is_infinite()
            }

            #[inline]
            fn as_f64(self) -> f64 {
                self as f64
            }
        }
    };
}

impl_floating!(f32, 6);
impl_floating!(f64, 15);

extern "C" {
    // format function in libc
    fn snprintf(dest: *mut u8, size: usize, format: *const u8, ...);
}

/// Converts a floating-point number to numeric.
pub fn from_floating<T: Floating>(f: T) -> Result<NumericVar, NumericTryFromError> {
    if f.is_nan() {
        return Ok(NumericVar::nan());
    }

    if f.is_infinite() {
        return Err(NumericTryFromError::invalid());
    }

    const SIZE: usize = 128;

    let n = unsafe {
        let mut buf: [MaybeUninit<u8>; SIZE] = MaybeUninit::uninit().assume_init();
        snprintf(
            buf.as_mut_ptr() as *mut u8,
            SIZE,
            "%.*g\0".as_ptr(),
            T::PRECISION,
            f.as_f64(),
        );
        let s = CStr::from_ptr(buf.as_ptr() as *const i8).to_string_lossy();
        let _s = s.to_string();
        s.parse::<NumericVar>()?
    };

    Ok(n)
}
