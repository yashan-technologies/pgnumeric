// Copyright 2020 CoD Team

//! Numeric conversion utilities.

use crate::data::{NumericDigit, NUMERIC_NEG, NUMERIC_POS};
use crate::error::NumericTryFromError;
use crate::{Numeric, NBASE};
use std::convert::{TryFrom, TryInto};
use std::ffi::CStr;
use std::mem::MaybeUninit;

/// Zero value.
trait Zero: Copy + PartialEq {
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
trait Unsigned: Copy + Zero {
    const MAX_NDIGITS: usize;

    fn next_digit(self) -> (NumericDigit, Self);

    fn from_numeric_digit(n: NumericDigit) -> Self;
    fn from_u64(i: u64) -> Self;
    fn overflowing_mul(self, rhs: Self) -> (Self, bool);
    fn overflowing_add(self, rhs: Self) -> (Self, bool);
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

            #[inline]
            fn from_numeric_digit(n: NumericDigit) -> Self {
                n as Self
            }

            #[inline]
            fn from_u64(i: u64) -> Self {
                i as Self
            }

            #[inline]
            fn overflowing_mul(self, rhs: Self) -> (Self, bool) {
                self.overflowing_mul(rhs)
            }

            #[inline]
            fn overflowing_add(self, rhs: Self) -> (Self, bool) {
                self.overflowing_add(rhs)
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

    fn from_numeric_digit(_n: i16) -> Self {
        panic!("should not use this associate function")
    }

    fn from_u64(_i: u64) -> Self {
        panic!("should not use this associate function")
    }

    fn overflowing_mul(self, _rhs: Self) -> (Self, bool) {
        panic!("should not use this associate function")
    }

    fn overflowing_add(self, _rhs: Self) -> (Self, bool) {
        panic!("should not use this associate function")
    }
}

/// Signed integer.
trait Signed: Copy + PartialOrd + Zero {
    type AbsType: Unsigned;

    const MIN_VALUE: Self;

    fn from_numeric_digit(n: NumericDigit) -> Self;
    fn from_i64(i: i64) -> Self;
    fn is_negative(self) -> bool;
    fn negative(self) -> Self;
    fn abs(self) -> Self::AbsType;
    fn overflowing_mul(self, rhs: Self) -> (Self, bool);
    fn overflowing_sub(self, rhs: Self) -> (Self, bool);
}

macro_rules! impl_signed {
    ($t: ty, $abs_ty: ty) => {
        impl Signed for $t {
            type AbsType = $abs_ty;

            const MIN_VALUE: Self = Self::min_value();

            #[inline]
            fn from_numeric_digit(n: NumericDigit) -> Self {
                debug_assert!(n as i128 <= Self::max_value() as i128);
                debug_assert!(n as i128 >= Self::min_value() as i128);
                n as Self
            }

            #[inline]
            fn from_i64(i: i64) -> Self {
                debug_assert!(i as i128 <= Self::max_value() as i128);
                debug_assert!(i as i128 >= Self::min_value() as i128);
                i as Self
            }

            #[inline]
            fn is_negative(self) -> bool {
                self < 0
            }

            #[inline]
            fn negative(self) -> Self {
                -self
            }

            #[inline]
            fn abs(self) -> $abs_ty {
                if self >= 0 {
                    self as $abs_ty
                } else {
                    -(self + 1) as $abs_ty + 1
                }
            }

            #[inline]
            fn overflowing_mul(self, rhs: Self) -> (Self, bool) {
                self.overflowing_mul(rhs)
            }

            #[inline]
            fn overflowing_sub(self, rhs: Self) -> (Self, bool) {
                self.overflowing_sub(rhs)
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
#[inline]
fn from_signed<T: Signed>(val: T) -> Numeric {
    if val.is_zero() {
        return Numeric::zero();
    }

    let mut var = Numeric::nan();

    if val.is_negative() {
        var.sign = NUMERIC_NEG;
    } else {
        var.sign = NUMERIC_POS;
    }

    var.dscale = 0;

    set_var_from_unsigned(&mut var, val.abs());

    var.make_result_no_overflow();

    var
}

/// Converts an unsigned integer to numeric.
#[inline]
fn from_unsigned<T: Unsigned>(val: T) -> Numeric {
    if val.is_zero() {
        return Numeric::zero();
    }

    let mut var = Numeric::nan();

    var.sign = NUMERIC_POS;
    var.dscale = 0;

    set_var_from_unsigned(&mut var, val);

    var.make_result_no_overflow();

    var
}

fn set_var_from_unsigned<T: Unsigned>(var: &mut Numeric, val: T) {
    var.alloc_buf(T::MAX_NDIGITS as i32);

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
    var.data.offset_set(var.data.len() - ndigits as u32);
    var.ndigits = ndigits;
    var.weight = ndigits - 1;
}

/// Floating-point number.
trait Floating: Copy {
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
fn from_floating<T: Floating>(f: T) -> Result<Numeric, NumericTryFromError> {
    if f.is_nan() {
        return Ok(Numeric::nan());
    }

    if f.is_infinite() {
        return Err(NumericTryFromError::invalid());
    }

    const BUF_SIZE: usize = 128;

    let mut n = unsafe {
        let mut buf: [MaybeUninit<u8>; BUF_SIZE] = MaybeUninit::uninit().assume_init();
        snprintf(
            buf.as_mut_ptr() as *mut u8,
            BUF_SIZE,
            "%.*g\0".as_ptr(),
            T::PRECISION,
            f.as_f64(),
        );
        let s = CStr::from_ptr(buf.as_ptr() as *const i8).to_string_lossy();
        s.parse::<Numeric>()?
    };

    n.make_result_no_overflow();

    Ok(n)
}

macro_rules! impl_from_signed {
    ($t: ty) => {
        impl From<$t> for Numeric {
            #[inline]
            fn from(val: $t) -> Self {
                from_signed(val)
            }
        }
    };
}

macro_rules! impl_from_unsigned {
    ($t: ty) => {
        impl From<$t> for Numeric {
            #[inline]
            fn from(val: $t) -> Self {
                from_unsigned(val)
            }
        }
    };
}

impl_from_signed!(i8);
impl_from_signed!(i16);
impl_from_signed!(i32);
impl_from_signed!(i64);
impl_from_signed!(i128);
impl_from_unsigned!(u8);
impl_from_unsigned!(u16);
impl_from_unsigned!(u32);
impl_from_unsigned!(u64);
impl_from_unsigned!(u128);

impl From<bool> for Numeric {
    #[inline]
    fn from(b: bool) -> Self {
        let val = if b { 1u8 } else { 0u8 };
        val.into()
    }
}

impl From<usize> for Numeric {
    #[inline]
    fn from(u: usize) -> Self {
        if std::mem::size_of::<usize>() == 8 {
            (u as u64).into()
        } else if std::mem::size_of::<usize>() == 4 {
            (u as u32).into()
        } else {
            panic!("invalid usize size")
        }
    }
}

impl From<isize> for Numeric {
    #[inline]
    fn from(i: isize) -> Self {
        if std::mem::size_of::<isize>() == 8 {
            (i as i64).into()
        } else if std::mem::size_of::<isize>() == 4 {
            (i as i32).into()
        } else {
            panic!("invalid isize size")
        }
    }
}

macro_rules! impl_try_from_floating {
    ($t: ty) => {
        impl TryFrom<$t> for Numeric {
            type Error = NumericTryFromError;

            #[inline]
            fn try_from(f: $t) -> Result<Self, Self::Error> {
                from_floating(f)
            }
        }
    };
}

impl_try_from_floating!(f32);
impl_try_from_floating!(f64);

/// Converts a numeric to signed integer.
fn into_signed<T: Signed>(var: &mut Numeric) -> Result<T, NumericTryFromError> {
    // Ensure no overflowing happened when NumericDigit convert to T
    debug_assert!(std::mem::size_of::<T>() >= std::mem::size_of::<NumericDigit>());
    // Ensure enough space for carry.
    debug_assert!(var.data.offset() > 0 || var.ndigits == 0);

    if var.is_nan() {
        return Err(NumericTryFromError::invalid());
    }

    // Round to nearest integer
    var.round_common(0);

    // Check for zero input
    var.strip();
    let ndigits = var.ndigits;
    if ndigits == 0 {
        return Ok(T::ZERO);
    }

    // For input like 10000000000, we must treat stripped digits as real.
    // So the loop assumes there are weight+1 digits before the decimal point.
    let weight = var.weight;
    debug_assert!(weight >= 0);
    debug_assert!(ndigits <= weight + 1);

    // Construct the result. To avoid issues with converting a value
    // corresponding to INT64_MIN (which can't be represented as a positive 64
    // bit two's complement integer), accumulate value as a negative number.
    let digits = var.digits();
    let mut val = T::from_numeric_digit(digits[0]).negative();
    for i in 1..=weight {
        let (new_val, overflowing) = val.overflowing_mul(T::from_i64(NBASE as i64));
        if overflowing {
            return Err(NumericTryFromError::overflow());
        }
        val = new_val;

        if i < ndigits {
            let (new_val, overflowing) =
                val.overflowing_sub(T::from_numeric_digit(digits[i as usize]));
            if overflowing {
                return Err(NumericTryFromError::overflow());
            }
            val = new_val;
        }
    }

    if var.sign != NUMERIC_NEG {
        if val == T::MIN_VALUE {
            return Err(NumericTryFromError::overflow());
        }

        val = val.negative();
    }

    Ok(val)
}

/// Converts a numeric to unsigned integer.
fn into_unsigned<T: Unsigned>(var: &mut Numeric) -> Result<T, NumericTryFromError> {
    // Ensure no overflowing happened when NumericDigit convert to T
    debug_assert!(std::mem::size_of::<T>() >= std::mem::size_of::<NumericDigit>());
    // Ensure enough space for carry.
    debug_assert!(var.data.offset() > 0 || var.ndigits == 0);

    if var.is_nan() {
        return Err(NumericTryFromError::invalid());
    }

    // Round to nearest integer
    var.round_common(0);

    // Check for zero input
    var.strip();
    let ndigits = var.ndigits;
    if ndigits == 0 {
        return Ok(T::ZERO);
    }

    if var.sign == NUMERIC_NEG {
        return Err(NumericTryFromError::overflow());
    }

    // For input like 10000000000, we must treat stripped digits as real.
    // So the loop assumes there are weight+1 digits before the decimal point.
    let weight = var.weight;
    debug_assert!(weight >= 0);
    debug_assert!(ndigits <= weight + 1);

    // Construct the result.
    let digits = var.digits();
    let mut val = T::from_numeric_digit(digits[0]);
    for i in 1..=weight {
        let (new_val, overflowing) = val.overflowing_mul(T::from_u64(NBASE as u64));
        if overflowing {
            return Err(NumericTryFromError::overflow());
        }
        val = new_val;

        if i < ndigits {
            let (new_val, overflowing) =
                val.overflowing_add(T::from_numeric_digit(digits[i as usize]));
            if overflowing {
                return Err(NumericTryFromError::overflow());
            }
            val = new_val;
        }
    }

    Ok(val)
}

macro_rules! impl_try_from_numeric_for_signed {
    ($t: ty) => {
        impl TryFrom<Numeric> for $t {
            type Error = NumericTryFromError;

            #[inline]
            fn try_from(mut value: Numeric) -> Result<Self, Self::Error> {
                value.reserve_rounding_digit();
                into_signed(&mut value)
            }
        }
    };
}

macro_rules! impl_try_from_numeric_for_unsigned {
    ($t: ty) => {
        impl TryFrom<Numeric> for $t {
            type Error = NumericTryFromError;

            #[inline]
            fn try_from(mut value: Numeric) -> Result<Self, Self::Error> {
                value.reserve_rounding_digit();
                into_unsigned(&mut value)
            }
        }
    };
}

impl_try_from_numeric_for_signed!(i16);
impl_try_from_numeric_for_signed!(i32);
impl_try_from_numeric_for_signed!(i64);
impl_try_from_numeric_for_signed!(i128);

impl_try_from_numeric_for_unsigned!(u16);
impl_try_from_numeric_for_unsigned!(u32);
impl_try_from_numeric_for_unsigned!(u64);
impl_try_from_numeric_for_unsigned!(u128);

impl TryFrom<Numeric> for i8 {
    type Error = NumericTryFromError;

    #[inline]
    fn try_from(value: Numeric) -> Result<Self, Self::Error> {
        let val = TryInto::<i16>::try_into(value)?;
        if val > i8::max_value() as i16 || val < i8::min_value() as i16 {
            Err(NumericTryFromError::overflow())
        } else {
            Ok(val as i8)
        }
    }
}

impl TryFrom<Numeric> for u8 {
    type Error = NumericTryFromError;

    #[inline]
    fn try_from(value: Numeric) -> Result<Self, Self::Error> {
        let val = TryInto::<u16>::try_into(value)?;
        if val > u8::max_value() as u16 {
            Err(NumericTryFromError::overflow())
        } else {
            Ok(val as u8)
        }
    }
}

impl TryFrom<Numeric> for usize {
    type Error = NumericTryFromError;

    #[inline]
    fn try_from(value: Numeric) -> Result<Self, Self::Error> {
        if std::mem::size_of::<usize>() == 8 {
            let val = TryInto::<u64>::try_into(value)?;
            Ok(val as usize)
        } else if std::mem::size_of::<usize>() == 4 {
            let val = TryInto::<u32>::try_into(value)?;
            Ok(val as usize)
        } else {
            panic!("invalid usize size")
        }
    }
}

impl TryFrom<Numeric> for isize {
    type Error = NumericTryFromError;

    #[inline]
    fn try_from(value: Numeric) -> Result<Self, Self::Error> {
        if std::mem::size_of::<isize>() == 8 {
            let val = TryInto::<i64>::try_into(value)?;
            Ok(val as isize)
        } else if std::mem::size_of::<isize>() == 4 {
            let val = TryInto::<i32>::try_into(value)?;
            Ok(val as isize)
        } else {
            panic!("invalid usize size")
        }
    }
}

impl TryFrom<Numeric> for f32 {
    type Error = NumericTryFromError;

    #[inline]
    fn try_from(value: Numeric) -> Result<Self, Self::Error> {
        TryFrom::try_from(&value)
    }
}

impl TryFrom<Numeric> for f64 {
    type Error = NumericTryFromError;

    #[inline]
    fn try_from(value: Numeric) -> Result<Self, Self::Error> {
        TryFrom::try_from(&value)
    }
}

impl TryFrom<&Numeric> for f32 {
    type Error = NumericTryFromError;

    #[inline]
    fn try_from(value: &Numeric) -> Result<Self, Self::Error> {
        let s = value.to_string();
        let f = s.parse::<f32>()?;
        Ok(f)
    }
}

impl TryFrom<&Numeric> for f64 {
    type Error = NumericTryFromError;

    #[inline]
    fn try_from(value: &Numeric) -> Result<Self, Self::Error> {
        let s = value.to_string();
        let f = s.parse::<f64>()?;
        Ok(f)
    }
}

macro_rules! impl_try_from_numeric_ref {
    ($t: ty) => {
        impl TryFrom<&Numeric> for $t {
            type Error = NumericTryFromError;

            #[inline]
            fn try_from(value: &Numeric) -> Result<Self, Self::Error> {
                let mut new_value = Numeric::nan();
                new_value.set_from_var(&value);
                new_value.try_into()
            }
        }
    };
}

impl_try_from_numeric_ref!(i8);
impl_try_from_numeric_ref!(i16);
impl_try_from_numeric_ref!(i32);
impl_try_from_numeric_ref!(i64);
impl_try_from_numeric_ref!(i128);
impl_try_from_numeric_ref!(u8);
impl_try_from_numeric_ref!(u16);
impl_try_from_numeric_ref!(u32);
impl_try_from_numeric_ref!(u64);
impl_try_from_numeric_ref!(u128);
impl_try_from_numeric_ref!(isize);
impl_try_from_numeric_ref!(usize);

/// Simple and safe type conversions that may fail in a controlled way under some circumstances.
/// Used to do reference-to-value conversions while not consuming the input value.
pub trait TryFromRef<T>: Sized {
    /// The type returned in the event of a conversion error.
    type Error;

    /// Performs the conversion.
    fn try_from_ref(value: &T) -> Result<Self, Self::Error>;
}

macro_rules! impl_try_from_ref_numeric {
    ($t: ty) => {
        impl TryFromRef<Numeric> for $t {
            type Error = NumericTryFromError;

            #[inline]
            fn try_from_ref(value: &Numeric) -> Result<Self, Self::Error> {
                TryFrom::try_from(value)
            }
        }
    };
}

impl_try_from_ref_numeric!(i8);
impl_try_from_ref_numeric!(i16);
impl_try_from_ref_numeric!(i32);
impl_try_from_ref_numeric!(i64);
impl_try_from_ref_numeric!(i128);
impl_try_from_ref_numeric!(u8);
impl_try_from_ref_numeric!(u16);
impl_try_from_ref_numeric!(u32);
impl_try_from_ref_numeric!(u64);
impl_try_from_ref_numeric!(u128);
impl_try_from_ref_numeric!(f32);
impl_try_from_ref_numeric!(f64);
impl_try_from_ref_numeric!(isize);
impl_try_from_ref_numeric!(usize);

#[cfg(test)]
mod tests {
    use super::*;
    use std::convert::TryInto;
    use std::fmt::Debug;

    // use this function to test `as_bytes` in convert functions.
    fn transform(val: &Numeric) -> Numeric {
        let bytes = val.as_bytes();
        let result = unsafe {
            Numeric::from_raw_parts(bytes.as_ptr() as *mut u8, bytes.len() as u32, 0, false)
        };
        result
    }

    fn assert_from<V: Into<Numeric>, E: AsRef<str>>(val: V, expected: E) {
        let numeric = val.into();
        assert_eq!(transform(&numeric).to_string(), expected.as_ref());
    }

    #[test]
    fn from_i8() {
        assert_from(0i8, "0");
        assert_from(1i8, "1");
        assert_from(-1i8, "-1");
        assert_from(127i8, "127");
        assert_from(-128i8, "-128");
    }

    #[test]
    fn from_i16() {
        assert_from(0i16, "0");
        assert_from(1i16, "1");
        assert_from(-1i16, "-1");
        assert_from(32767i16, "32767");
        assert_from(-32768i16, "-32768");
    }

    #[test]
    fn from_i32() {
        assert_from(0i32, "0");
        assert_from(1i32, "1");
        assert_from(-1i32, "-1");
        assert_from(2147483647i32, "2147483647");
        assert_from(-2147483647i32, "-2147483647");
    }

    #[test]
    fn from_i64() {
        assert_from(0i64, "0");
        assert_from(1i64, "1");
        assert_from(-1i64, "-1");
        assert_from(9223372036854775807i64, "9223372036854775807");
        assert_from(-9223372036854775808i64, "-9223372036854775808");
    }

    #[test]
    fn from_i128() {
        assert_from(0i128, "0");
        assert_from(1i128, "1");
        assert_from(-1i128, "-1");
        assert_from(
            170141183460469231731687303715884105727i128,
            "170141183460469231731687303715884105727",
        );
        assert_from(
            -170141183460469231731687303715884105728i128,
            "-170141183460469231731687303715884105728",
        );
    }

    #[test]
    fn from_u8() {
        assert_from(0u8, "0");
        assert_from(1u8, "1");
        assert_from(255u8, "255");
    }

    #[test]
    fn from_u16() {
        assert_from(0u16, "0");
        assert_from(1u16, "1");
        assert_from(65535u16, "65535");
    }

    #[test]
    fn from_u32() {
        assert_from(0u32, "0");
        assert_from(1u32, "1");
        assert_from(4294967295u32, "4294967295");
    }

    #[test]
    fn from_u64() {
        assert_from(0u64, "0");
        assert_from(1u64, "1");
        assert_from(18446744073709551615u64, "18446744073709551615");
    }

    #[test]
    fn from_u128() {
        assert_from(0u128, "0");
        assert_from(1u128, "1");
        assert_from(
            340282366920938463463374607431768211455u128,
            "340282366920938463463374607431768211455",
        );
    }

    #[test]
    fn from_bool() {
        assert_from(true, "1");
        assert_from(false, "0");
    }

    #[test]
    fn from_usize() {
        assert_from(0usize, "0");
        assert_from(1usize, "1");
        if std::mem::size_of::<usize>() == 8 {
            assert_from(18446744073709551615usize, "18446744073709551615");
        } else if std::mem::size_of::<usize>() == 4 {
            assert_from(4294967295usize, "4294967295u32");
        }
    }

    #[test]
    fn from_isize() {
        assert_from(0isize, "0");
        assert_from(1isize, "1");
        if std::mem::size_of::<isize>() == 8 {
            assert_from(9223372036854775807isize, "9223372036854775807");
            assert_from(-9223372036854775808isize, "-9223372036854775808");
        } else if std::mem::size_of::<isize>() == 4 {
            assert_from(2147483647isize, "2147483647");
            assert_from(-2147483648isize, "-2147483648");
        }
    }

    fn assert_try_from<V: TryInto<Numeric, Error = NumericTryFromError>, E: AsRef<str>>(
        val: V,
        expected: E,
    ) {
        let numeric = val.try_into().unwrap();
        assert_eq!(transform(&numeric).to_string(), expected.as_ref());
    }

    fn assert_try_from_invalid<V: TryInto<Numeric, Error = NumericTryFromError>>(val: V) {
        let result = val.try_into();
        assert_eq!(result.unwrap_err(), NumericTryFromError::invalid());
    }

    #[test]
    fn try_from_f32() {
        assert_try_from_invalid(std::f32::INFINITY);
        assert_try_from_invalid(std::f32::NEG_INFINITY);
        assert_try_from(std::f32::NAN, "NaN");
        assert_try_from(0.0f32, "0");
        assert_try_from(-0.0f32, "0");
        assert_try_from(0.000001f32, "0.000001");
        assert_try_from(0.0000001f32, "0.0000001");
        assert_try_from(0.555555f32, "0.555555");
        assert_try_from(0.5555555f32, "0.555556");
        assert_try_from(0.999999f32, "0.999999");
        assert_try_from(0.9999999f32, "1");
        assert_try_from(1.0f32, "1");
        assert_try_from(1.00001f32, "1.00001");
        assert_try_from(1.000001f32, "1");
        assert_try_from(1.555555f32, "1.55555");
        assert_try_from(1.5555555f32, "1.55556");
        assert_try_from(1.99999f32, "1.99999");
        assert_try_from(1.999999f32, "2");
        assert_try_from(1e-6f32, "0.000001");
        assert_try_from(1e-10f32, "0.0000000001");
        assert_try_from(1.23456789e10f32, "12345700000");
        assert_try_from(1.23456789e-10f32, "0.000000000123457");
    }

    #[test]
    fn try_from_f64() {
        assert_try_from_invalid(std::f64::INFINITY);
        assert_try_from_invalid(std::f64::NEG_INFINITY);
        assert_try_from(std::f64::NAN, "NaN");
        assert_try_from(0.0f64, "0");
        assert_try_from(-0.0f64, "0");
        assert_try_from(0.000000000000001f64, "0.000000000000001");
        assert_try_from(0.0000000000000001f64, "0.0000000000000001");
        assert_try_from(0.555555555555555f64, "0.555555555555555");
        assert_try_from(0.5555555555555556f64, "0.555555555555556");
        assert_try_from(0.999999999999999f64, "0.999999999999999");
        assert_try_from(0.9999999999999999f64, "1");
        assert_try_from(1.0f64, "1");
        assert_try_from(1.00000000000001f64, "1.00000000000001");
        assert_try_from(1.000000000000001f64, "1");
        assert_try_from(1.55555555555555f64, "1.55555555555555");
        assert_try_from(1.555555555555556f64, "1.55555555555556");
        assert_try_from(1.99999999999999f64, "1.99999999999999");
        assert_try_from(1.999999999999999f64, "2");
        assert_try_from(1e-6f64, "0.000001");
        assert_try_from(1e-20f64, "0.00000000000000000001");
        assert_try_from(1.234567890123456789e20f64, "123456789012346000000");
        assert_try_from(
            1.234567890123456789e-20f64,
            "0.0000000000000000000123456789012346",
        );
    }

    fn try_into<S: AsRef<str>, T: TryFrom<Numeric, Error = NumericTryFromError>>(s: S) -> T {
        let n = s.as_ref().parse::<Numeric>().unwrap();
        let val = TryInto::<T>::try_into(n).unwrap();
        val
    }

    fn assert_try_into<
        S: AsRef<str>,
        T: TryFrom<Numeric, Error = NumericTryFromError> + PartialEq + Debug,
    >(
        s: S,
        expected: T,
    ) {
        let val = try_into::<S, T>(s);
        assert_eq!(val, expected);
    }

    fn assert_try_into_overflow<T: TryFrom<Numeric, Error = NumericTryFromError> + Debug>(s: &str) {
        let n = s.parse::<Numeric>().unwrap();
        let result = TryInto::<T>::try_into(n);
        assert_eq!(result.unwrap_err(), NumericTryFromError::overflow());
    }

    fn assert_try_into_invalid<T: TryFrom<Numeric, Error = NumericTryFromError> + Debug>(s: &str) {
        let n = s.parse::<Numeric>().unwrap();
        let result = TryInto::<T>::try_into(n);
        assert_eq!(result.unwrap_err(), NumericTryFromError::invalid());
    }

    #[test]
    fn into_i8() {
        assert_try_into("0", 0i8);
        assert_try_into("1", 1i8);
        assert_try_into("-1", -1i8);
        assert_try_into("127", 127i8);
        assert_try_into("-128", -128);
        assert_try_into_overflow::<i8>("128");
        assert_try_into_overflow::<i8>("-129");
        assert_try_into_invalid::<i8>("NaN");
    }

    #[test]
    fn into_i16() {
        assert_try_into("0", 0i16);
        assert_try_into("1", 1i16);
        assert_try_into("-1", -1i16);
        assert_try_into("32767", 32767i16);
        assert_try_into("-32768", -32768i16);
        assert_try_into_overflow::<i16>("32768");
        assert_try_into_overflow::<i16>("-32769");
        assert_try_into_invalid::<i16>("NaN");
    }

    #[test]
    fn into_i32() {
        assert_try_into("0", 0i32);
        assert_try_into("1", 1i32);
        assert_try_into("-1", -1i32);
        assert_try_into("2147483647", 2147483647i32);
        assert_try_into("-2147483648", -2147483648i32);
        assert_try_into_overflow::<i32>("2147483648");
        assert_try_into_overflow::<i32>("-2147483649");
        assert_try_into_invalid::<i32>("NaN");
    }

    #[test]
    fn into_i64() {
        assert_try_into("0", 0i64);
        assert_try_into("1", 1i64);
        assert_try_into("-1", -1i64);
        assert_try_into("9223372036854775807", 9223372036854775807i64);
        assert_try_into("-9223372036854775808", -9223372036854775808i64);
        assert_try_into_overflow::<i64>("9223372036854775808");
        assert_try_into_overflow::<i64>("-9223372036854775809");
        assert_try_into_invalid::<i64>("NaN");
    }

    #[test]
    fn into_i128() {
        assert_try_into("0", 0i128);
        assert_try_into("1", 1i128);
        assert_try_into("-1", -1i128);
        assert_try_into(
            "170141183460469231731687303715884105727",
            170141183460469231731687303715884105727i128,
        );
        assert_try_into(
            "-170141183460469231731687303715884105728",
            -170141183460469231731687303715884105728i128,
        );
        assert_try_into_overflow::<i128>("170141183460469231731687303715884105728");
        assert_try_into_overflow::<i128>("-170141183460469231731687303715884105729");
        assert_try_into_invalid::<i128>("NaN");
    }

    #[test]
    fn into_u8() {
        assert_try_into("0", 0u8);
        assert_try_into("1", 1u8);
        assert_try_into("255", 255u8);
        assert_try_into_overflow::<u8>("256");
        assert_try_into_overflow::<u8>("-1");
        assert_try_into_invalid::<u8>("NaN");
    }

    #[test]
    fn into_u16() {
        assert_try_into("0", 0u16);
        assert_try_into("1", 1u16);
        assert_try_into("65535", 65535u16);
        assert_try_into_overflow::<u16>("65536");
        assert_try_into_overflow::<u16>("-1");
        assert_try_into_invalid::<u16>("NaN");
    }

    #[test]
    fn into_u32() {
        assert_try_into("0", 0u32);
        assert_try_into("1", 1u32);
        assert_try_into("4294967295", 4294967295u32);
        assert_try_into_overflow::<u32>("4294967296");
        assert_try_into_overflow::<u32>("-1");
        assert_try_into_invalid::<u32>("NaN");
    }

    #[test]
    fn into_u64() {
        assert_try_into("0", 0u64);
        assert_try_into("1", 1u64);
        assert_try_into("18446744073709551615", 18446744073709551615u64);
        assert_try_into_overflow::<u64>("18446744073709551616");
        assert_try_into_overflow::<u64>("-1");
        assert_try_into_invalid::<u64>("NaN");
    }

    #[test]
    fn into_u128() {
        assert_try_into("0", 0u128);
        assert_try_into("1", 1u128);
        assert_try_into(
            "340282366920938463463374607431768211455",
            340282366920938463463374607431768211455u128,
        );
        assert_try_into_overflow::<u128>("340282366920938463463374607431768211456");
        assert_try_into_overflow::<u128>("-1");
        assert_try_into_invalid::<u128>("NaN");
    }

    #[test]
    fn into_usize() {
        assert_try_into("0", 0usize);
        assert_try_into("1", 1usize);
        if std::mem::size_of::<usize>() == 8 {
            assert_try_into("18446744073709551615", 18446744073709551615usize);
            assert_try_into_overflow::<usize>("18446744073709551616");
            assert_try_into_overflow::<usize>("-1");
        } else if std::mem::size_of::<usize>() == 4 {
            assert_try_into("4294967295", 4294967295usize);
            assert_try_into_overflow::<usize>("4294967296");
            assert_try_into_overflow::<usize>("-1");
        }
        assert_try_into_invalid::<usize>("NaN");
    }

    #[test]
    fn into_isize() {
        assert_try_into("0", 0isize);
        assert_try_into("1", 1isize);
        assert_try_into("-1", -1isize);
        if std::mem::size_of::<isize>() == 8 {
            assert_try_into("9223372036854775807", 9223372036854775807isize);
            assert_try_into("-9223372036854775808", -9223372036854775808isize);
            assert_try_into_overflow::<isize>("9223372036854775808");
            assert_try_into_overflow::<isize>("-9223372036854775809");
        } else if std::mem::size_of::<isize>() == 4 {
            assert_try_into("2147483647", 2147483647isize);
            assert_try_into("-2147483648", -2147483648isize);
            assert_try_into_overflow::<isize>("2147483648");
            assert_try_into_overflow::<isize>("-2147483649");
        }
        assert_try_into_invalid::<isize>("NaN");
    }

    #[test]
    fn into_f32() {
        assert_try_into("0", 0f32);
        assert_try_into("1", 1f32);
        assert_try_into("0.000001", 0.000001f32);
        assert_try_into("0.0000001", 0.0000001f32);
        assert_try_into("0.555555", 0.555555f32);
        assert_try_into("0.55555599", 0.555556f32);
        assert_try_into("0.999999", 0.999999f32);
        assert_try_into("0.99999999", 1.0f32);
        assert_try_into("1.00001", 1.00001f32);
        assert_try_into("1.00000001", 1.0f32);
        assert_try_into("1.23456789e10", 1.23456789e10f32);
        assert_try_into("1.23456789e-10", 1.23456789e-10f32);
        assert_try_into("3.40282347e+38", std::f32::MAX);
        assert_try_into("-3.40282347e+38", std::f32::MIN);
        assert_try_into("1e39", std::f32::INFINITY);
        assert_try_into("1.17549435e-38", std::f32::MIN_POSITIVE);
        assert!(try_into::<&str, f32>("NaN").is_nan());
    }

    #[test]
    fn into_f64() {
        assert_try_into("0", 0f64);
        assert_try_into("1", 1f64);
        assert_try_into("0.000000000000001", 0.000000000000001f64);
        assert_try_into("0.555555555555555", 0.555555555555555f64);
        assert_try_into("0.55555555555555599", 0.555555555555556f64);
        assert_try_into("0.999999999999999", 0.999999999999999f64);
        assert_try_into("0.99999999999999999", 1.0f64);
        assert_try_into("1.00000000000001", 1.00000000000001f64);
        assert_try_into("1.0000000000000001", 1.0f64);
        assert_try_into("1.7976931348623157e+308", std::f64::MAX);
        assert_try_into("-1.7976931348623157e+308", std::f64::MIN);
        assert_try_into("1e309", std::f64::INFINITY);
        assert_try_into("2.2250738585072014e-308", std::f64::MIN_POSITIVE);
        assert!(try_into::<&str, f64>("NaN").is_nan());
    }

    fn try_into_ref<S: AsRef<str>, T: TryFromRef<Numeric, Error = NumericTryFromError>>(s: S) -> T {
        let n = s.as_ref().parse::<Numeric>().unwrap();
        let val = TryFromRef::try_from_ref(&n).unwrap();
        val
    }

    fn assert_try_into_ref<
        S: AsRef<str>,
        T: TryFromRef<Numeric, Error = NumericTryFromError> + PartialEq + Debug,
    >(
        s: S,
        expected: T,
    ) {
        let val = try_into_ref::<S, T>(s);
        assert_eq!(val, expected);
    }

    fn assert_try_into_ref_overflow<T: TryFromRef<Numeric, Error = NumericTryFromError> + Debug>(
        s: &str,
    ) {
        let n = s.parse::<Numeric>().unwrap();
        let result: Result<T, NumericTryFromError> = TryFromRef::try_from_ref(&n);
        assert_eq!(result.unwrap_err(), NumericTryFromError::overflow());
    }

    fn assert_try_into_ref_invalid<T: TryFromRef<Numeric, Error = NumericTryFromError> + Debug>(
        s: &str,
    ) {
        let n = s.parse::<Numeric>().unwrap();
        let result: Result<T, NumericTryFromError> = TryFromRef::try_from_ref(&n);
        assert_eq!(result.unwrap_err(), NumericTryFromError::invalid());
    }

    #[test]
    fn into_i8_ref() {
        assert_try_into_ref("0", 0i8);
        assert_try_into_ref("1", 1i8);
        assert_try_into_ref("-1", -1i8);
        assert_try_into_ref("127", 127i8);
        assert_try_into_ref("-128", -128);
        assert_try_into_ref_overflow::<i8>("128");
        assert_try_into_ref_overflow::<i8>("-129");
        assert_try_into_ref_invalid::<i8>("NaN");
    }

    #[test]
    fn into_i16_ref() {
        assert_try_into_ref("0", 0i16);
        assert_try_into_ref("1", 1i16);
        assert_try_into_ref("-1", -1i16);
        assert_try_into_ref("32767", 32767i16);
        assert_try_into_ref("-32768", -32768i16);
        assert_try_into_ref_overflow::<i16>("32768");
        assert_try_into_ref_overflow::<i16>("-32769");
        assert_try_into_ref_invalid::<i16>("NaN");
    }

    #[test]
    fn into_i32_ref() {
        assert_try_into_ref("0", 0i32);
        assert_try_into_ref("1", 1i32);
        assert_try_into_ref("-1", -1i32);
        assert_try_into_ref("2147483647", 2147483647i32);
        assert_try_into_ref("-2147483648", -2147483648i32);
        assert_try_into_ref_overflow::<i32>("2147483648");
        assert_try_into_ref_overflow::<i32>("-2147483649");
        assert_try_into_ref_invalid::<i32>("NaN");
    }

    #[test]
    fn into_i64_ref() {
        assert_try_into_ref("0", 0i64);
        assert_try_into_ref("1", 1i64);
        assert_try_into_ref("-1", -1i64);
        assert_try_into_ref("9223372036854775807", 9223372036854775807i64);
        assert_try_into_ref("-9223372036854775808", -9223372036854775808i64);
        assert_try_into_ref_overflow::<i64>("9223372036854775808");
        assert_try_into_ref_overflow::<i64>("-9223372036854775809");
        assert_try_into_ref_invalid::<i64>("NaN");
    }

    #[test]
    fn into_i128_ref() {
        assert_try_into_ref("0", 0i128);
        assert_try_into_ref("1", 1i128);
        assert_try_into_ref("-1", -1i128);
        assert_try_into_ref(
            "170141183460469231731687303715884105727",
            170141183460469231731687303715884105727i128,
        );
        assert_try_into_ref(
            "-170141183460469231731687303715884105728",
            -170141183460469231731687303715884105728i128,
        );
        assert_try_into_ref_overflow::<i128>("170141183460469231731687303715884105728");
        assert_try_into_ref_overflow::<i128>("-170141183460469231731687303715884105729");
        assert_try_into_ref_invalid::<i128>("NaN");
    }

    #[test]
    fn into_u8_ref() {
        assert_try_into_ref("0", 0u8);
        assert_try_into_ref("1", 1u8);
        assert_try_into_ref("255", 255u8);
        assert_try_into_ref_overflow::<u8>("256");
        assert_try_into_ref_overflow::<u8>("-1");
        assert_try_into_ref_invalid::<u8>("NaN");
    }

    #[test]
    fn into_u16_ref() {
        assert_try_into_ref("0", 0u16);
        assert_try_into_ref("1", 1u16);
        assert_try_into_ref("65535", 65535u16);
        assert_try_into_ref_overflow::<u16>("65536");
        assert_try_into_ref_overflow::<u16>("-1");
        assert_try_into_ref_invalid::<u16>("NaN");
    }

    #[test]
    fn into_u32_ref() {
        assert_try_into_ref("0", 0u32);
        assert_try_into_ref("1", 1u32);
        assert_try_into_ref("4294967295", 4294967295u32);
        assert_try_into_ref_overflow::<u32>("4294967296");
        assert_try_into_ref_overflow::<u32>("-1");
        assert_try_into_ref_invalid::<u32>("NaN");
    }

    #[test]
    fn into_u64_ref() {
        assert_try_into_ref("0", 0u64);
        assert_try_into_ref("1", 1u64);
        assert_try_into_ref("18446744073709551615", 18446744073709551615u64);
        assert_try_into_ref_overflow::<u64>("18446744073709551616");
        assert_try_into_ref_overflow::<u64>("-1");
        assert_try_into_ref_invalid::<u64>("NaN");
    }

    #[test]
    fn into_u128_ref() {
        assert_try_into_ref("0", 0u128);
        assert_try_into_ref("1", 1u128);
        assert_try_into_ref(
            "340282366920938463463374607431768211455",
            340282366920938463463374607431768211455u128,
        );
        assert_try_into_ref_overflow::<u128>("340282366920938463463374607431768211456");
        assert_try_into_ref_overflow::<u128>("-1");
        assert_try_into_ref_invalid::<u128>("NaN");
    }

    #[test]
    fn into_usize_ref() {
        assert_try_into_ref("0", 0usize);
        assert_try_into_ref("1", 1usize);
        if std::mem::size_of::<usize>() == 8 {
            assert_try_into_ref("18446744073709551615", 18446744073709551615usize);
            assert_try_into_ref_overflow::<usize>("18446744073709551616");
            assert_try_into_ref_overflow::<usize>("-1");
        } else if std::mem::size_of::<usize>() == 4 {
            assert_try_into_ref("4294967295", 4294967295usize);
            assert_try_into_ref_overflow::<usize>("4294967296");
            assert_try_into_ref_overflow::<usize>("-1");
        }
        assert_try_into_ref_invalid::<usize>("NaN");
    }

    #[test]
    fn into_isize_ref() {
        assert_try_into_ref("0", 0isize);
        assert_try_into_ref("1", 1isize);
        assert_try_into_ref("-1", -1isize);
        if std::mem::size_of::<isize>() == 8 {
            assert_try_into_ref("9223372036854775807", 9223372036854775807isize);
            assert_try_into_ref("-9223372036854775808", -9223372036854775808isize);
            assert_try_into_ref_overflow::<isize>("9223372036854775808");
            assert_try_into_ref_overflow::<isize>("-9223372036854775809");
        } else if std::mem::size_of::<isize>() == 4 {
            assert_try_into_ref("2147483647", 2147483647isize);
            assert_try_into_ref("-2147483648", -2147483648isize);
            assert_try_into_ref_overflow::<isize>("2147483648");
            assert_try_into_ref_overflow::<isize>("-2147483649");
        }
        assert_try_into_ref_invalid::<isize>("NaN");
    }

    #[test]
    fn into_f32_ref() {
        assert_try_into_ref("0", 0f32);
        assert_try_into_ref("1", 1f32);
        assert_try_into_ref("0.000001", 0.000001f32);
        assert_try_into_ref("0.0000001", 0.0000001f32);
        assert_try_into_ref("0.555555", 0.555555f32);
        assert_try_into_ref("0.55555599", 0.555556f32);
        assert_try_into_ref("0.999999", 0.999999f32);
        assert_try_into_ref("0.99999999", 1.0f32);
        assert_try_into_ref("1.00001", 1.00001f32);
        assert_try_into_ref("1.00000001", 1.0f32);
        assert_try_into_ref("1.23456789e10", 1.23456789e10f32);
        assert_try_into_ref("1.23456789e-10", 1.23456789e-10f32);
        assert_try_into_ref("3.40282347e+38", std::f32::MAX);
        assert_try_into_ref("-3.40282347e+38", std::f32::MIN);
        assert_try_into_ref("1e39", std::f32::INFINITY);
        assert_try_into_ref("1.17549435e-38", std::f32::MIN_POSITIVE);
        assert!(try_into_ref::<&str, f32>("NaN").is_nan());
    }

    #[test]
    fn into_f64_ref() {
        assert_try_into_ref("0", 0f64);
        assert_try_into_ref("1", 1f64);
        assert_try_into_ref("0.000000000000001", 0.000000000000001f64);
        assert_try_into_ref("0.555555555555555", 0.555555555555555f64);
        assert_try_into_ref("0.55555555555555599", 0.555555555555556f64);
        assert_try_into_ref("0.999999999999999", 0.999999999999999f64);
        assert_try_into_ref("0.99999999999999999", 1.0f64);
        assert_try_into_ref("1.00000000000001", 1.00000000000001f64);
        assert_try_into_ref("1.0000000000000001", 1.0f64);
        assert_try_into_ref("1.7976931348623157e+308", std::f64::MAX);
        assert_try_into_ref("-1.7976931348623157e+308", std::f64::MIN);
        assert_try_into_ref("1e309", std::f64::INFINITY);
        assert_try_into_ref("2.2250738585072014e-308", std::f64::MIN_POSITIVE);
        assert!(try_into_ref::<&str, f64>("NaN").is_nan());
    }
}
