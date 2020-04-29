// Copyright 2020 CoD Team

//! Numeric

use crate::binary::{NumericBinary, NUMERIC_DIGIT_SIZE};
use crate::data::*;
use crate::typmod::Typmod;
use crate::var::NumericVar;
use std::borrow::{Borrow, Cow};
use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops::Deref;

pub const DIVIDE_BY_ZERO_MSG: &str = "attempt to divide by zero";
pub const VALUE_OVERFLOW_MSG: &str = "value overflows numeric format";

/// An owned, mutable numeric.
#[derive(Debug)]
pub struct NumericBuf {
    // data buffer
    buf: *const u8,
    // total length of buffer
    len: u32,
    // start position of numeric header
    offset: u32,
}

unsafe impl Send for NumericBuf {}
unsafe impl Sync for NumericBuf {}

impl NumericBuf {
    /// Creates a `NumericBuf` from raw pointer.
    ///
    /// # Safety
    ///
    #[inline]
    pub(crate) unsafe fn from_raw_parts(buf: *const u8, len: u32, offset: u32) -> Self {
        debug_assert!(!buf.is_null());
        debug_assert!(offset < len);
        NumericBuf { buf, len, offset }
    }

    /// Creates a `NaN` numeric.
    #[inline]
    pub fn nan() -> Self {
        NumericVar::nan().into_numeric_buf()
    }

    /// Creates a zero numeric.
    #[inline]
    pub fn zero() -> Self {
        NumericVar::zero().into_numeric_buf()
    }

    /// Negate this value.
    #[inline]
    pub fn negate_mut(&mut self) {
        if self.is_nan() {
            return;
        }

        let mut var = self.as_var_owned();
        var.negate();
        // no need to make result
        *self = var.into_numeric_buf();
    }

    /// Compute the absolute value of `self`.
    #[inline]
    pub fn abs_mut(&mut self) {
        if self.is_nan() {
            return;
        }

        if self.is_negative() {
            let mut var = self.as_var_owned();
            var.abs();
            // no need to make result
            *self = var.into_numeric_buf();
        }
    }

    /// Round a value to have `scale` digits after the decimal point.
    /// We allow negative `scale`, implying rounding before the decimal
    /// point --- Oracle interprets rounding that way.
    ///
    /// # Panics
    /// Panics if overflows.
    #[inline]
    pub fn round_mut(&mut self, scale: i32) {
        if self.is_nan() {
            return;
        }

        let mut var = self.as_var_owned();
        var.round(scale);
        match var.make_result() {
            Some(result) => *self = result,
            None => panic!(VALUE_OVERFLOW_MSG),
        }
    }

    /// Truncate a value to have `scale` digits after the decimal point.
    /// We allow negative `scale`, implying a truncation before the decimal
    /// point --- Oracle interprets truncation that way.
    #[inline]
    pub fn trunc_mut(&mut self, scale: i32) {
        if self.is_nan() {
            return;
        }

        let mut var = self.as_var_owned();
        var.trunc(scale);
        *self = var.make_result_no_overflow();
    }

    /// Compute factorial.
    ///
    /// Returns `None` if overflows.
    pub fn factorial(num: i64) -> Option<Self> {
        NumericVar::factorial(num).and_then(|var| var.make_result())
    }

    /// Do bounds checking and rounding according to `typmod`.
    ///
    /// Returns true if overflows.
    ///
    /// Notes that no matter whether overflows, `self` will be rounded.
    pub fn apply_typmod(&mut self, typmod: Typmod) -> bool {
        let mut var = self.as_var_owned();
        let mut overflow = var.apply_typmod(typmod);

        match var.make_result() {
            Some(result) => *self = result,
            None => overflow = true,
        }

        overflow
    }

    /// Extracts a byte slice contains the entire numeric.
    #[allow(clippy::cast_ptr_alignment)]
    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        unsafe {
            let ptr = self.buf.add(self.offset as usize);
            let bin = &*(ptr as *const NumericBinary);
            debug_assert!(bin.len() + self.offset <= self.len);
            std::slice::from_raw_parts(ptr, bin.len() as usize)
        }
    }

    /// Gets a `Numeric` reference by doing a cheap reference-to-reference conversion.
    #[inline]
    pub fn as_numeric(&self) -> &Numeric {
        unsafe { Numeric::from_bytes_unchecked(self.as_bytes()) }
    }

    /// Creates a owned `NumericVar`, leaving a null pointer in `self.buf`.
    ///
    /// After calling this method, the `NumericVar` must be converted into `NumericBuf`
    /// to give back the `self.buf`.
    #[inline]
    fn as_var_owned(&mut self) -> NumericVar {
        let buf = std::mem::replace(&mut self.buf, std::ptr::null());
        unsafe { NumericBuf::from_raw_parts(buf, self.len, self.offset).into_var() }
    }

    /// Creates a owned `NumericVar`. The `NumericBuf` cannot be used after calling this method.
    #[allow(clippy::cast_ptr_alignment)]
    #[inline]
    pub(crate) fn into_var(self) -> NumericVar<'static> {
        let me = std::mem::ManuallyDrop::new(self);
        let bin = me.as_binary();

        let len = me.len / NUMERIC_DIGIT_SIZE as u32;
        let offset = (me.offset + bin.header_size()) / NUMERIC_DIGIT_SIZE as u32;
        let data = unsafe { NumericData::from_raw_parts(me.buf as *mut _, len, offset) };

        NumericVar::owned(
            bin.ndigits(),
            bin.weight() as i32,
            bin.dscale() as i32,
            bin.sign(),
            data,
        )
    }
}

impl Drop for NumericBuf {
    #[inline]
    fn drop(&mut self) {
        if !self.buf.is_null() {
            unsafe {
                let _vec = Vec::<u8>::from_raw_parts(self.buf as *mut u8, 0, self.len as usize);
            }
            self.buf = std::ptr::null();
        }
    }
}

impl Clone for NumericBuf {
    #[inline]
    fn clone(&self) -> Self {
        self.as_var().into_numeric_buf()
    }
}

impl fmt::Display for NumericBuf {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        self.as_var().write(f)
    }
}

impl fmt::LowerExp for NumericBuf {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let var = self.as_var();
        let rscale = var.select_sci_scale();
        var.write_sci(f, rscale, true)
    }
}

impl fmt::UpperExp for NumericBuf {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let var = self.as_var();
        let rscale = var.select_sci_scale();
        var.write_sci(f, rscale, false)
    }
}

impl Hash for NumericBuf {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        Numeric::hash(self, state)
    }
}

impl Deref for NumericBuf {
    type Target = Numeric;

    #[inline]
    fn deref(&self) -> &Numeric {
        self.as_numeric()
    }
}

impl AsRef<Numeric> for NumericBuf {
    #[inline]
    fn as_ref(&self) -> &Numeric {
        self.as_numeric()
    }
}

impl Borrow<Numeric> for NumericBuf {
    #[inline]
    fn borrow(&self) -> &Numeric {
        self.as_numeric()
    }
}

impl<'a> From<NumericBuf> for Cow<'a, Numeric> {
    #[inline]
    fn from(var: NumericBuf) -> Cow<'a, Numeric> {
        Cow::Owned(var)
    }
}

impl<'a> From<&'a NumericBuf> for Cow<'a, Numeric> {
    #[inline]
    fn from(var: &'a NumericBuf) -> Cow<'a, Numeric> {
        Cow::Borrowed(var.as_numeric())
    }
}

/// A slice of a numeric.
///
/// This is an *unsized* type, meaning that it must always be used behind a
/// pointer like `&` or [`Box`]. For an owned version of this type,
/// see [`NumericBuf`].
#[derive(Debug)]
#[repr(transparent)]
pub struct Numeric {
    bytes: [u8],
}

impl Numeric {
    /// Creates a `Numeric` from bytes slice.
    ///
    /// # Safety
    /// Caller have to guaranteed the `value` bytes slice is a valid `Numeric`.
    #[inline]
    pub unsafe fn from_bytes_unchecked(value: &[u8]) -> &Numeric {
        &*(value as *const [u8] as *const Numeric)
    }

    /// Creates a `NaN` numeric.
    #[inline]
    pub fn nan() -> &'static Numeric {
        const NAN_BINARY: NumericBinary = NumericBinary::nan();
        unsafe { Numeric::from_bytes_unchecked(NAN_BINARY.as_bytes()) }
    }

    /// Creates a `zero` numeric.
    #[inline]
    pub fn zero() -> &'static Numeric {
        const ZERO_BINARY: NumericBinary = NumericBinary::zero();
        unsafe { Numeric::from_bytes_unchecked(ZERO_BINARY.as_bytes()) }
    }

    /// Extracts a byte slice contains the entire numeric.
    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes
    }

    /// Extracts a `NumericBinary` contains the entire numeric.
    #[allow(clippy::cast_ptr_alignment)]
    #[inline]
    fn as_binary(&self) -> &NumericBinary {
        let bin = unsafe { &*(self.bytes.as_ptr() as *const NumericBinary) };
        debug_assert_eq!(bin.len() as usize, self.bytes.len());
        bin
    }

    /// Creates a borrowed `NumericVar`.
    #[inline]
    pub(crate) fn as_var(&self) -> NumericVar {
        self.as_binary().as_var()
    }

    /// Checks if `self` is `NaN`.
    #[inline]
    pub fn is_nan(&self) -> bool {
        self.as_binary().is_nan()
    }

    /// Checks if `self` is negative.
    #[inline]
    pub fn is_negative(&self) -> bool {
        self.as_binary().is_negative()
    }

    /// Checks if `self` is positive.
    #[inline]
    pub fn is_positive(&self) -> bool {
        self.as_binary().is_positive()
    }

    /// Returns the scale, i.e. the count of decimal digits in the fractional part.
    ///
    /// Returns `None` if `self` is `NaN`.
    #[inline]
    pub fn scale(&self) -> Option<i32> {
        let bin = self.as_binary();
        if bin.is_nan() {
            None
        } else {
            Some(bin.dscale() as i32)
        }
    }

    /// Negate this value.
    #[inline]
    pub fn negate(&self) -> NumericBuf {
        let bin = self.as_binary();

        if bin.is_nan() {
            return NumericBuf::nan();
        }

        let mut var = bin.as_var();
        var.negate();
        var.make_result_no_overflow()
    }

    /// Returns a numeric that represents the sign of self.
    /// * -1 if `self` is less than 0
    /// * 0 if `self` is equal to 0
    /// * 1 if `self` is greater than zero
    /// * `NaN` if `self` is `NaN`
    #[inline]
    pub fn signum(&self) -> NumericBuf {
        let bin = self.as_binary();

        if bin.is_nan() {
            NumericBuf::nan()
        } else {
            bin.as_var().signum().make_result_no_overflow()
        }
    }

    /// Increment `self` by one.
    ///
    /// # Panics
    /// Panics if overflows.
    #[inline]
    pub fn inc(&self) -> NumericBuf {
        let bin = self.as_binary();

        if bin.is_nan() {
            return NumericBuf::nan();
        }

        // Compute the result and return it
        match bin.as_var().inc().make_result() {
            Some(result) => result,
            None => panic!(VALUE_OVERFLOW_MSG),
        }
    }

    /// Add two numerics,
    /// returning `None` if overflow occurred.
    #[inline]
    pub fn checked_add(&self, other: &Self) -> Option<NumericBuf> {
        let bin_self = self.as_binary();
        let bin_other = other.as_binary();

        if bin_self.is_nan() || bin_other.is_nan() {
            return Some(NumericBuf::nan());
        }

        bin_self
            .as_var()
            .add_common(&bin_other.as_var())
            .make_result()
    }

    /// Subtract one numeric from another,
    /// returning `None` if overflow occurred.
    #[inline]
    pub fn checked_sub(&self, other: &Self) -> Option<NumericBuf> {
        let bin_self = self.as_binary();
        let bin_other = other.as_binary();

        if bin_self.is_nan() || bin_other.is_nan() {
            return Some(NumericBuf::nan());
        }

        bin_self
            .as_var()
            .sub_common(&bin_other.as_var())
            .make_result()
    }

    /// Calculate the product of two numerics,
    /// returning `None` if overflow occurred.
    #[inline]
    pub fn checked_mul(&self, other: &Self) -> Option<NumericBuf> {
        let bin_self = self.as_binary();
        let bin_other = other.as_binary();

        if bin_self.is_nan() || bin_other.is_nan() {
            return Some(NumericBuf::nan());
        }

        let var_self = bin_self.as_var();
        let var_other = bin_other.as_var();

        // we request exact representation for the product,
        // rscale = sum(dscale of self, dscale of other)
        let rscale = var_self.dscale() + var_other.dscale();
        var_self.mul_common(&var_other, rscale).make_result()
    }

    /// Computes `self / other`.
    ///
    /// Returns a tuple of the divisor along with a boolean indicating whether an arithmetic overflow would occur.
    /// If an overflow would occur then `NaN` is returned.
    ///
    /// # Panics
    /// This function will panic if `other` is 0.
    #[inline]
    pub(crate) fn overflowing_div(&self, other: &Self) -> (NumericBuf, bool) {
        let bin_left = self.as_binary();
        let bin_right = other.as_binary();

        // Handle NaN
        if bin_left.is_nan() || bin_right.is_nan() {
            return (NumericBuf::nan(), false);
        }

        let result = bin_left
            .as_var()
            .checked_div(&bin_right.as_var())
            .expect(DIVIDE_BY_ZERO_MSG)
            .make_result();

        match result {
            Some(result) => (result, false),
            None => (NumericBuf::nan(), true),
        }
    }

    /// Checked numeric division.
    /// Computes `self / other`, returning `None` if `other == 0` or the division results in overflow.
    #[inline]
    pub fn checked_div(&self, other: &Self) -> Option<NumericBuf> {
        let bin_left = self.as_binary();
        let bin_right = other.as_binary();

        // Handle NaN
        if bin_left.is_nan() || bin_right.is_nan() {
            return Some(NumericBuf::nan());
        }

        bin_left
            .as_var()
            .checked_div(&bin_right.as_var())
            .and_then(|var| var.make_result())
    }

    /// Computes `self / other`, truncating the result to an integer.
    ///
    /// Returns `None` if `other == 0` or the division results in overflow.
    #[inline]
    pub fn checked_div_trunc(&self, other: &Self) -> Option<NumericBuf> {
        let bin_self = self.as_binary();
        let bin_other = other.as_binary();

        // Handle NaN
        if bin_self.is_nan() || bin_other.is_nan() {
            return Some(NumericBuf::nan());
        }

        bin_self
            .as_var()
            .checked_div_trunc(&bin_other.as_var())
            .and_then(|var| var.make_result())
    }

    /// Computes `self % other`.
    ///
    /// Returns a tuple of the remainder after dividing along with a boolean indicating whether an arithmetic overflow would occur.
    /// If an overflow would occur then 0 is returned.
    ///
    /// # Panics
    /// This function will panic if `other` is 0.
    #[inline]
    pub(crate) fn overflowing_rem(&self, other: &Self) -> (NumericBuf, bool) {
        let bin_self = self.as_binary();
        let bin_other = other.as_binary();

        if bin_self.is_nan() || bin_other.is_nan() {
            return (NumericBuf::nan(), false);
        }

        let result = bin_self
            .as_var()
            .mod_common(&bin_other.as_var())
            .expect(DIVIDE_BY_ZERO_MSG)
            .make_result();

        match result {
            Some(result) => (result, false),
            None => (NumericBuf::zero(), true),
        }
    }

    /// Checked numeric remainder.
    /// Computes `self % other`, returning None if rhs == 0 or the division results in overflow.
    #[inline]
    pub fn checked_rem(&self, other: &Self) -> Option<NumericBuf> {
        let bin_self = self.as_binary();
        let bin_other = other.as_binary();

        if bin_self.is_nan() || bin_other.is_nan() {
            return Some(NumericBuf::nan());
        }

        bin_self
            .as_var()
            .mod_common(&bin_other.as_var())
            .and_then(|var| var.make_result())
    }

    /// Round a value to have `scale` digits after the decimal point.
    /// We allow negative `scale`, implying rounding before the decimal
    /// point --- Oracle interprets rounding that way.
    ///
    /// # Panics
    /// Panics if overflows.
    #[inline]
    pub fn round(&self, scale: i32) -> NumericBuf {
        let bin = self.as_binary();

        if bin.is_nan() {
            return NumericBuf::nan();
        }

        let mut var = bin.as_var();
        var.round(scale);
        match var.make_result() {
            Some(result) => result,
            None => panic!(VALUE_OVERFLOW_MSG),
        }
    }

    /// Truncate a value to have `scale` digits after the decimal point.
    /// We allow negative `scale`, implying a truncation before the decimal
    /// point --- Oracle interprets truncation that way.
    #[inline]
    pub fn trunc(&self, scale: i32) -> NumericBuf {
        let bin = self.as_binary();

        if bin.is_nan() {
            return NumericBuf::nan();
        }

        let mut var = self.as_var();
        var.trunc(scale);
        var.make_result_no_overflow()
    }

    /// Return the smallest integer greater than or equal to the argument.
    ///
    /// # Panics
    /// Panics if overflows.
    #[inline]
    pub fn ceil(&self) -> NumericBuf {
        let bin = self.as_binary();

        if bin.is_nan() {
            return NumericBuf::nan();
        }

        match bin.as_var().ceil().make_result() {
            Some(result) => result,
            None => panic!(VALUE_OVERFLOW_MSG),
        }
    }

    /// Return the largest integer equal to or less than the argument.
    ///
    /// # Panics
    /// Panics if overflows.
    #[inline]
    pub fn floor(&self) -> NumericBuf {
        let bin = self.as_binary();

        if bin.is_nan() {
            return NumericBuf::nan();
        }

        match bin.as_var().floor().make_result() {
            Some(result) => result,
            None => panic!(VALUE_OVERFLOW_MSG),
        }
    }

    /// Compute the absolute value of `self`.
    #[inline]
    pub fn abs(&self) -> NumericBuf {
        let bin = self.as_binary();

        if bin.is_nan() {
            return NumericBuf::nan();
        }

        let mut var = bin.as_var();
        var.abs();
        var.into_numeric_buf()
    }

    /// Compute the square root of a numeric.
    ///
    /// # Panics
    /// Panics if `self` is negative.
    #[inline]
    pub fn sqrt(&self) -> NumericBuf {
        let bin = self.as_binary();

        if bin.is_nan() {
            return NumericBuf::nan();
        }

        let var = bin.as_var();

        assert!(
            !var.is_negative(),
            "cannot take square root of a negative number"
        );

        var.sqrt().make_result_no_overflow()
    }

    /// Compute the natural logarithm of `self`.
    ///
    /// # Panics
    /// Panics if `self <= 0`.
    #[inline]
    pub fn ln(&self) -> NumericBuf {
        let bin = self.as_binary();

        if bin.is_nan() {
            return NumericBuf::nan();
        }

        bin.as_var().ln().make_result_no_overflow()
    }

    /// Compute the logarithm of `self` in a given base.
    ///
    /// # Panics
    /// Panics if `self <= 0` or `base <= 0`.
    #[inline]
    pub fn log(&self, base: &Self) -> NumericBuf {
        let bin_self = self.as_binary();
        let bin_base = base.as_binary();

        if bin_self.is_nan() || bin_base.is_nan() {
            return NumericBuf::nan();
        }

        bin_self
            .as_var()
            .log(&bin_base.as_var())
            .make_result_no_overflow()
    }

    /// Compute the base 2 logarithm of `self`.
    ///
    /// # Panics
    /// Panics if `self <= 0`.
    #[inline]
    pub fn log2(&self) -> NumericBuf {
        let bin = self.as_binary();

        if bin.is_nan() {
            return NumericBuf::nan();
        }

        bin.as_var().log2().make_result_no_overflow()
    }

    /// Compute the base 10 logarithm of `self`.
    ///
    /// # Panics
    /// Panics if `self <= 0`.
    #[inline]
    pub fn log10(&self) -> NumericBuf {
        let bin = self.as_binary();

        if bin.is_nan() {
            return NumericBuf::nan();
        }

        bin.as_var().log10().make_result_no_overflow()
    }

    /// Raise e to the power of `self` (`e^(self)`).
    ///
    /// Returns `None` if overflows.
    ///
    #[inline]
    pub fn exp(&self) -> Option<NumericBuf> {
        let bin = self.as_binary();

        if bin.is_nan() {
            return Some(NumericBuf::nan());
        }

        bin.as_var().exp().and_then(|var| var.make_result())
    }

    /// Raise `self` to the power of `exp`.
    ///
    /// Returns `None` if overflows.
    ///
    /// # Panics
    /// if arguments are invalid:
    ///   - `self` is zero and `exp` is less than zero
    ///   - `self` is less than zero and `exp` is not a integer.
    #[inline]
    pub fn pow(&self, exp: &Self) -> Option<NumericBuf> {
        self.as_var().pow(&exp.as_var()).and_then(|var| {
            if var.is_nan() {
                Some(NumericBuf::nan())
            } else {
                var.make_result()
            }
        })
    }

    /// Returns a normalized string, suppressing insignificant
    /// trailing zeroes and then any trailing decimal point.
    ///
    /// The intent of this is to produce strings that are equal
    /// if and only if the input numeric values compare equal.
    #[inline]
    pub fn normalize(&self) -> String {
        self.as_var().normalize()
    }

    #[inline]
    pub(crate) fn cmp(&self, other: &Self) -> Ordering {
        let bin_self = self.as_binary();
        let bin_other = other.as_binary();

        // We consider all NANs to be equal and larger than any non-NAN. This is
        // somewhat arbitrary; the important thing is to have a consistent sort
        // order.
        if bin_self.is_nan() {
            if bin_other.is_nan() {
                Ordering::Equal // NAN == NAN
            } else {
                Ordering::Greater // NAN > non-NAN
            }
        } else if bin_other.is_nan() {
            Ordering::Less // non-NAN < NAN
        } else {
            let cmp = bin_self.as_var().cmp_common(&bin_other.as_var());
            match cmp {
                _ if cmp > 0 => Ordering::Greater,
                _ if cmp < 0 => Ordering::Less,
                _ => Ordering::Equal,
            }
        }
    }

    /// Feeds this value into the given [`Hasher`].
    fn hash<H: Hasher>(&self, state: &mut H) {
        let var = self.as_var();

        // If it's NaN, don't try to hash the rest of the fields
        if var.is_nan() {
            return;
        }

        let mut weight = var.weight();
        let mut start_offset = 0usize;

        // Omit any leading or trailing zeros from the input to the hash. The
        // numeric implementation *should* guarantee that leading and trailing
        // zeros are suppressed, but we're paranoid. Note that we measure the
        // starting and ending offsets in units of NumericDigits, not bytes.
        let digits = var.digits();
        digits.iter().take_while(|n| **n == 0).for_each(|_| {
            start_offset += 1;

            // The weight is effectively the # of digits before the decimal point,
            // so decrement it for each leading zero we skip.
            weight -= 1;
        });

        // If there are no non-zero digits, then the value of the number is zero,
        // regardless of any other fields.
        if var.ndigits() == start_offset as i32 {
            state.write_u8(0);
            return;
        }

        let mut end_offset = 0usize;
        digits
            .iter()
            .rev()
            .take_while(|n| **n == 0)
            .for_each(|_| end_offset += 1);

        // If we get here, there should be at least one non-zero digit
        debug_assert!(start_offset + end_offset < var.ndigits() as usize);

        // Note that we don't hash on the Numeric's scale, since two numerics can
        // compare equal but have different scales.
        digits[start_offset..var.ndigits() as usize - end_offset].hash(state);

        // Mix in the weight
        state.write_i32(weight);

        // Mix in the sign
        state.write_i8(if var.is_positive() { 1 } else { -1 });
    }
}

impl ToOwned for Numeric {
    type Owned = NumericBuf;

    #[inline]
    fn to_owned(&self) -> NumericBuf {
        let var = self.as_var();
        if var.is_nan() {
            NumericBuf::nan()
        } else {
            var.into_numeric_buf()
        }
    }
}

impl<'a> From<&'a Numeric> for Cow<'a, Numeric> {
    #[inline]
    fn from(n: &'a Numeric) -> Cow<'a, Numeric> {
        Cow::Borrowed(n)
    }
}

impl fmt::Display for Numeric {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        self.as_var().write(f)
    }
}

impl fmt::LowerExp for Numeric {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let var = self.as_var();
        let rscale = var.select_sci_scale();
        var.write_sci(f, rscale, true)
    }
}

impl fmt::UpperExp for Numeric {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let var = self.as_var();
        let rscale = var.select_sci_scale();
        var.write_sci(f, rscale, false)
    }
}

impl Hash for Numeric {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        Numeric::hash(self, state)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // use this function to test `as_bytes` in other functions.
    fn transform(val: &NumericBuf) -> &Numeric {
        val.deref()
    }

    fn assert_signum(val: &str, expected: &str) {
        let val = val.parse::<NumericBuf>().unwrap();
        let result = val.signum();
        assert_eq!(transform(&result).to_string(), expected);
    }

    #[test]
    fn signum() {
        assert_signum("NaN", "NaN");
        assert_signum("0", "0");
        assert_signum("31", "1");
        assert_signum("-47", "-1");
    }

    fn assert_inc(val: &str, expected: &str) {
        let val = val.parse::<NumericBuf>().unwrap();
        let result = val.inc();
        assert_eq!(transform(&result).to_string(), expected);
    }

    #[test]
    fn inc() {
        assert_inc("NaN", "NaN");
        assert_inc("-1", "0");
        assert_inc("0", "1");
        assert_inc("1", "2");
        assert_inc(
            "170141183460469231731687303715884105727",
            "170141183460469231731687303715884105728",
        );
        assert_inc(
            "-170141183460469231731687303715884105727",
            "-170141183460469231731687303715884105726",
        );
        assert_inc("1.00001", "2.00001");
    }

    fn assert_checked_div_trunc(val: &str, other: &str, expected: Option<&str>) {
        let val = val.parse::<NumericBuf>().unwrap();
        let other = other.parse::<NumericBuf>().unwrap();

        let result = val
            .checked_div_trunc(&other)
            .map(|n| transform(&n).to_string());
        let expected = expected.map(|s| s.to_owned());

        assert_eq!(result, expected);
    }

    #[test]
    fn checked_div_trunc() {
        assert_checked_div_trunc("NaN", "1", Some("NaN"));
        assert_checked_div_trunc("1", "NaN", Some("NaN"));
        assert_checked_div_trunc("1", "0", None);
        assert_checked_div_trunc("10.00000", "2", Some("5"));
        assert_checked_div_trunc("10.00001", "2", Some("5"));
        assert_checked_div_trunc("10.00000", "3", Some("3"));
        assert_checked_div_trunc("10.00001", "3", Some("3"));
    }

    fn assert_round(val: &str, rscale: i32, expected: &str) {
        let numeric = val.parse::<NumericBuf>().unwrap().round(rscale);
        assert_eq!(transform(&numeric).to_string(), expected);
    }

    #[test]
    fn round() {
        assert_round("NaN", 0, "NaN");
        assert_round("123456", 0, "123456");
        assert_round("123456.123456", 6, "123456.123456");
        assert_round("123456.123456", 5, "123456.12346");
        assert_round("123456.123456", 4, "123456.1235");
        assert_round("123456.123456", 3, "123456.123");
        assert_round("123456.123456", 2, "123456.12");
        assert_round("123456.123456", 1, "123456.1");
        assert_round("123456.123456", 0, "123456");
        assert_round("123456.123456", -1, "123460");
        assert_round("123456.123456", -2, "123500");
        assert_round("123456.123456", -3, "123000");
        assert_round("123456.123456", -4, "120000");
        assert_round("123456.123456", -5, "100000");
        assert_round("9999.9", 1, "9999.9");
        assert_round("9999.9", -2, "10000");
        assert_round("9999.9", -4, "10000");
    }

    fn assert_trunc(val: &str, rscale: i32, expected: &str) {
        let numeric = val.parse::<NumericBuf>().unwrap().trunc(rscale);
        assert_eq!(transform(&numeric).to_string(), expected);
    }

    #[test]
    fn trunc() {
        assert_trunc("NaN", 0, "NaN");
        assert_trunc("123456", 0, "123456");
        assert_trunc("123456.123456", 6, "123456.123456");
        assert_trunc("123456.123456", 5, "123456.12345");
        assert_trunc("123456.123456", 4, "123456.1234");
        assert_trunc("123456.123456", 3, "123456.123");
        assert_trunc("123456.123456", 2, "123456.12");
        assert_trunc("123456.123456", 1, "123456.1");
        assert_trunc("123456.123456", 0, "123456");
        assert_trunc("123456.123456", -1, "123450");
        assert_trunc("123456.123456", -2, "123400");
        assert_trunc("123456.123456", -3, "123000");
        assert_trunc("123456.123456", -4, "120000");
        assert_trunc("123456.123456", -5, "100000");
        assert_trunc("9999.9", 1, "9999.9");
        assert_trunc("9999.9", -2, "9900");
        assert_trunc("9999.9", -4, "0");
    }

    fn assert_sqrt(val: &str, expected: &str) {
        let var = val.parse::<NumericBuf>().unwrap();
        let result = var.sqrt();
        assert_eq!(transform(&result).to_string(), expected);
    }

    #[test]
    fn sqrt() {
        assert_sqrt("NaN", "NaN");
        assert_sqrt("0", "0.000000000000000");
        assert_sqrt("0.00000", "0.000000000000000");
        assert_sqrt("1", "1.000000000000000");
        assert_sqrt("1.00000", "1.000000000000000");
        assert_sqrt("1.44", "1.200000000000000");
        assert_sqrt("2", "1.414213562373095");
        assert_sqrt("100", "10.000000000000000");
        assert_sqrt(
            "170141183460469231731687303715884105727",
            "13043817825332782212",
        );
        assert_sqrt(
            "0.170141183460469231731687303715884105727",
            "0.412481737123559485879032211752436138996",
        );
        assert_sqrt(
            "1e100",
            "100000000000000000000000000000000000000000000000000",
        );
        assert_sqrt(
            "1.01e100",
            "100498756211208902702192649127595761869450234700264",
        );
    }

    #[test]
    #[should_panic(expected = "cannot take square root of a negative number")]
    fn sqrt_negative() {
        let var = "-1".parse::<NumericBuf>().unwrap();
        let _ = var.sqrt();
    }

    fn assert_ceil(val: &str, expected: &str) {
        let var = val.parse::<NumericBuf>().unwrap();
        let result = var.ceil();
        assert_eq!(transform(&result).to_string(), expected);
    }

    #[test]
    fn ceil() {
        assert_ceil("NaN", "NaN");
        assert_ceil("00000.00000", "0");
        assert_ceil("10000", "10000");
        assert_ceil("-10000", "-10000");
        assert_ceil("123456.123456", "123457");
        assert_ceil("-123456.123456", "-123456");
    }

    fn assert_floor(val: &str, expected: &str) {
        let var = val.parse::<NumericBuf>().unwrap();
        let result = var.floor();
        assert_eq!(transform(&result).to_string(), expected);
    }

    #[test]
    fn floor() {
        assert_floor("NaN", "NaN");
        assert_floor("00000.00000", "0");
        assert_floor("10000", "10000");
        assert_floor("-10000", "-10000");
        assert_floor("123456.123456", "123456");
        assert_floor("-123456.123456", "-123457");
    }

    fn assert_abs(val: &str, expected: &str) {
        let var = val.parse::<NumericBuf>().unwrap().abs();
        assert_eq!(transform(&var).to_string(), expected);
    }

    #[test]
    fn abs() {
        assert_abs("NaN", "NaN");
        assert_abs("0.0", "0.0");
        assert_abs("123456.123456", "123456.123456");
        assert_abs("-123456.123456", "123456.123456");
    }

    fn assert_write_sci(val: &str, scale: i32, expected: &str) {
        let var = val.parse::<NumericBuf>().unwrap();
        let mut s = String::new();
        transform(&var)
            .as_var()
            .write_sci(&mut s, scale, true)
            .unwrap();
        assert_eq!(s, expected);
    }

    #[test]
    fn write_sci() {
        assert_write_sci("123456789", 9, "1.234567890e+08");
        assert_write_sci("123456789", 8, "1.23456789e+08");
        assert_write_sci("123456789", 7, "1.2345679e+08");
        assert_write_sci("123456789", 6, "1.234568e+08");
        assert_write_sci("123456789", 5, "1.23457e+08");
        assert_write_sci("123456789", 4, "1.2346e+08");
        assert_write_sci("123456789", 3, "1.235e+08");
        assert_write_sci("123456789", 2, "1.23e+08");
        assert_write_sci("123456789", 1, "1.2e+08");
        assert_write_sci("123456789", 0, "1e+08");
        assert_write_sci("123456789", -1, "1e+08");
        assert_write_sci("0.123456789", 9, "1.234567890e-01");
        assert_write_sci("0.123456789", 8, "1.23456789e-01");
        assert_write_sci("0.123456789", 7, "1.2345679e-01");
        assert_write_sci("0.123456789", 6, "1.234568e-01");
        assert_write_sci("0.123456789", 5, "1.23457e-01");
        assert_write_sci("0.123456789", 4, "1.2346e-01");
        assert_write_sci("0.123456789", 3, "1.235e-01");
        assert_write_sci("0.123456789", 2, "1.23e-01");
        assert_write_sci("0.123456789", 1, "1.2e-01");
        assert_write_sci("0.123456789", 0, "1e-01");
        assert_write_sci("0.123456789", -1, "1e-01");
        assert_write_sci("0.0", 0, "0e+00");
        assert_write_sci("0.0", 1, "0.0e+00");
        assert_write_sci("0.0", 2, "0.00e+00");
        assert_write_sci("12345.6789e100", 9, "1.234567890e+104");
        assert_write_sci("12345.6789e-100", 9, "1.234567890e-96");
    }

    fn assert_sci(val: &str, expected: &str) {
        let var = val.parse::<NumericBuf>().unwrap();
        let s = format!("{:E}", transform(&var));
        assert_eq!(s, expected);
    }

    #[test]
    fn sci() {
        assert_sci("1234567890", "1.23456789E+09");
        assert_sci("123456789", "1.23456789E+08");
        assert_sci("12345678.9", "1.23456789E+07");
        assert_sci("1234567.89", "1.23456789E+06");
        assert_sci("123456.789", "1.23456789E+05");
        assert_sci("12345.6789", "1.23456789E+04");
        assert_sci("1234.56789", "1.23456789E+03");
        assert_sci("123.456789", "1.23456789E+02");
        assert_sci("12.3456789", "1.23456789E+01");
        assert_sci("1.23456789", "1.23456789E+00");
        assert_sci("0.123456789", "1.23456789E-01");

        assert_sci("1", "1E+00");
        assert_sci("10", "1E+01");
        assert_sci("100", "1E+02");
        assert_sci("1000", "1E+03");
        assert_sci("10000", "1E+04");
        assert_sci("100000", "1E+05");
        assert_sci("1000000", "1E+06");
        assert_sci("10000000", "1E+07");
        assert_sci("100000000", "1E+08");
        assert_sci("1000000000", "1E+09");
        assert_sci("10000000000", "1E+10");
        assert_sci("100000000000", "1E+11");

        assert_sci("1e100", "1E+100");
        assert_sci("1e1000", "1E+1000");
        assert_sci("1e10000", "1E+10000");
        assert_sci("1e100000", "1E+100000");

        assert_sci("11", "1.1E+01");
        assert_sci("101", "1.01E+02");
        assert_sci("1001", "1.001E+03");
        assert_sci("10001", "1.0001E+04");
        assert_sci("100001", "1.00001E+05");
        assert_sci("1000001", "1.000001E+06");
        assert_sci("10000001", "1.0000001E+07");
        assert_sci("100000001", "1.00000001E+08");
        assert_sci("1000000001", "1.000000001E+09");
        assert_sci("10000000001", "1.0000000001E+10");
        assert_sci("100000000001", "1.00000000001E+11");

        assert_sci("1.1", "1.1E+00");
        assert_sci("1.01", "1.01E+00");
        assert_sci("1.001", "1.001E+00");
        assert_sci("1.0001", "1.0001E+00");
        assert_sci("1.00001", "1.00001E+00");
        assert_sci("1.000001", "1.000001E+00");
        assert_sci("1.0000001", "1.0000001E+00");
        assert_sci("1.00000001", "1.00000001E+00");
        assert_sci("1.000000001", "1.000000001E+00");
        assert_sci("1.0000000001", "1.0000000001E+00");
        assert_sci("1.00000000001", "1.00000000001E+00");
    }

    fn assert_ln(val: &str, expected: &str) {
        let var = val.parse::<NumericBuf>().unwrap();
        let ln = var.ln();
        assert_eq!(transform(&ln).to_string(), expected);
    }

    #[test]
    fn ln() {
        assert_ln("0.1", "-2.3025850929940457");
        assert_ln("0.01", "-4.6051701859880914");
        assert_ln("0.001", "-6.9077552789821371");
        assert_ln("0.0001", "-9.2103403719761827");
        assert_ln("0.00001", "-11.512925464970228");
        assert_ln("1e-100", "-230.2585092994045684017991454684364207601101488628772976033327900967572609677352480235997205089598298342");
        assert_ln("1e-1000", "-2302.5850929940456840179914546843642076011014886287729760333279009675726096773524802359972050895982983419677840422862486334095254650828067566662873690987816894829072083255546808437998948262331985283935053089653777326288461633662222876982198867465436674744042432743651550489343149393914796194044002221051017141748003688084012647080685567743216228355220114804663715659121373450747856947683463616792101806445070648000277502684916746550586856935673420670581136429224554405758925724208241314695689016758940256776311356919292033376587141660230105703089634572075440370847469940168269282808481184289314848524948644871927809676271275775397027668605952496716674183485704422507197965004714951050492214776567636938662976979522110718264549734772662425709429322582798502585509785265383207606726317164309505995087807523710333101197857547331541421808427543863591778117054309827482385045648019095610299291824318237525357709750539565187697510374970888692180205189339507238539205144634197265287286965110862571492198849978749");
        assert_ln("1", "0.0000000000000000");
        assert_ln("1.1", "0.09531017980432486");
        assert_ln("1.01", "0.009950330853168083");
        assert_ln("1.001", "0.0009995003330835332");
        assert_ln("1.0001", "0.00009999500033330834");
        assert_ln("1.00001", "0.000009999950000333331");
        assert_ln("10", "2.3025850929940457");
        assert_ln("255", "5.5412635451584261");
        assert_ln("65535", "11.090339630053646");
        assert_ln("4294967295", "22.180709777685419");
        assert_ln("18446744073709551615", "44.361419555836500");
        assert_ln(
            "340282366920938463463374607431768211455",
            "88.722839111673000",
        );
        assert_ln("1e100", "230.25850929940457");
        assert_ln("1e1001", "2304.8876780870397");
        assert_ln("1e10001", "23028.153515033451");
    }

    #[test]
    #[should_panic(expected = "cannot take logarithm of zero")]
    fn ln_0() {
        assert_ln("0", "0");
    }

    #[test]
    #[should_panic(expected = "cannot take logarithm of a negative number")]
    fn ln_neg() {
        assert_ln("-1", "0");
    }

    fn assert_log(val: &str, base: &str, expected: &str) {
        let var = val.parse::<NumericBuf>().unwrap();
        let base = base.parse::<NumericBuf>().unwrap();
        let log = var.log(&base);
        assert_eq!(transform(&log).to_string(), expected);
    }

    fn assert_log2(val: &str, expected: &str) {
        let var = val.parse::<NumericBuf>().unwrap();
        let log2 = var.log2();
        assert_eq!(transform(&log2).to_string(), expected);
    }

    fn assert_log10(val: &str, expected: &str) {
        let var = val.parse::<NumericBuf>().unwrap();
        let log2 = var.log10();
        assert_eq!(transform(&log2).to_string(), expected);
    }

    #[test]
    fn log() {
        assert_log("123456789", "0.1", "-8.091514977169270");
        assert_log("123456789", "0.01", "-4.045757488584635");
        assert_log("123456789", "0.001", "-2.697171659056423");
        assert_log("123456789", "0.0001", "-2.022878744292318");
        assert_log("123456789", "0.00001", "-1.6183029954338541");
        assert_log("123456789", "1e-100", "-0.0809151497716927044751833362305954725851507333894466643029235223096383572364268409654249033542824907");
        assert_log("123456789", "1e-1000", "-0.0080915149771692704475183336230595472585150733389446664302923522309638357236426840965424903354282490714591977064292483065730693861907022223547607755491396888409765838403429233742455780032387482532982483730949256827998472796480203130971398558667948371549217283245362947607635167242507474630341758812157681310192340391795065372673100186376370557220664797321285789377736680121228136432735567035676397169530123991016761597669812656343071910099944110121223021293791969828583567943015017403000731019269674207303912897923421346036243583629643713841067462728296494607774007896800993663103166139287683355421131471317722252919551931858458150486112888168828352759557201100071905150932496234120660723567674094677213384931190497902151138415034533326948426138261992881890187246162824877548439693953630541552707646627425641627097402213257495139809203524531816818006021543108125322974626627517043467787486226245595396381375078350380205164747109070113983331132398425840431723176948689874499109975748440690776601319442");
        assert_log("123456789", "1.1", "195.48176075649987");
        assert_log("123456789", "1.01", "1872.4404284743931");
        assert_log("123456789", "1.001", "18640.715915210105");
        assert_log("123456789", "1.0001", "186323.33320730935");
        assert_log("123456789", "1.00001", "1863149.4923021588");
        assert_log("123456789", "10", "8.091514977169270");
        assert_log("123456789", "255", "3.362302047959233");
        assert_log("123456789", "65535", "1.6799667447224873");
        assert_log("123456789", "4294967295", "0.8399822166607071");
        assert_log("123456789", "18446744073709551615", "0.4199911083259449");
        assert_log(
            "123456789",
            "340282366920938463463374607431768211455",
            "0.2099955541629725",
        );
        assert_log("123456789", "1e100", "0.08091514977169270");
        assert_log("123456789", "1e1001", "0.008083431545623647");
        assert_log("123456789", "1e10001", "0.0008090705906578613");
    }

    #[test]
    fn log2() {
        assert_log2("0.1", "-3.3219280948873623");
        assert_log2("0.01", "-6.6438561897747247");
        assert_log2("0.001", "-9.9657842846620870");
        assert_log2("0.0001", "-13.2877123795494494");
        assert_log2("0.00001", "-16.609640474436812");
        assert_log2("1e-100", "-332.1928094887362347870319429489390175864831393024580612054756395815934776608625215850139743359370155100");
        assert_log2("1e-1000", "-3321.9280948873623478703194294893901758648313930245806120547563958159347766086252158501397433593701550996573717102502518268240969842635268882753027729986553938519513526575055686430176091900248916669414333740119031241873751097158664675401791896558067358307796884327258832749925224489023835599764173941379280097727566863554779014867450578458847802710422545609722346579569554153701915764117177924716513500239211271473393614407233972115748510070949878916588808313221948067932982323259311950671399507837003367342480706635275008406917626386253546880153686216184188608589948353813214998930270441792078659226018229653715753672396606951164868368466238585084860629905426994692791162732061340064467048476340704373523367422128308967036457909216772190902142196214245744465852453594844881548345925142954093735390654944863277929842429159118113116329812576945019815750379218553848782035516019737827728888175987433286607271239382520221333280525512488274344488424531654650612414891822867932526642928116599228516273450818601");
        assert_log2("1", "0.0000000000000000");
        assert_log2("1.1", "0.13750352374993491");
        assert_log2("1.01", "0.014355292977070041");
        assert_log2("1.001", "0.0014419741739064804");
        assert_log2("1.0001", "0.00014426229109455418");
        assert_log2("1.00001", "0.000014426878274618484");
        assert_log2("10", "3.3219280948873623");
        assert_log2("255", "7.9943534368588579");
        assert_log2("65535", "15.999977986052736");
        assert_log2("4294967295", "31.999999999664096");
        assert_log2("18446744073709551615", "64.000000000000000");
        assert_log2(
            "340282366920938463463374607431768211455",
            "128.000000000000000",
        );
        assert_log2("1e100", "332.19280948873623");
        assert_log2("1e1001", "3325.2500229822497");
        assert_log2("1e10001", "33222.602876968511");
    }

    #[test]
    fn log10() {
        assert_log10("0.1", "-1.0000000000000000");
        assert_log10("0.01", "-2.0000000000000000");
        assert_log10("0.001", "-3.0000000000000000");
        assert_log10("0.0001", "-4.0000000000000000");
        assert_log10("0.00001", "-5.000000000000000");
        assert_log10("1e-100", "-100.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000");
        assert_log10("1e-1000", "-1000.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000");
        assert_log10("1", "0.0000000000000000");
        assert_log10("1.1", "0.04139268515822504");
        assert_log10("1.01", "0.004321373782642574");
        assert_log10("1.001", "0.0004340774793186407");
        assert_log10("1.0001", "0.00004342727686266964");
        assert_log10("1.00001", "0.000004342923104453187");
        assert_log10("10", "1.0000000000000000");
        assert_log10("255", "2.4065401804339552");
        assert_log10("65535", "4.816473303765250");
        assert_log10("4294967295", "9.632959861146281");
        assert_log10("18446744073709551615", "19.265919722494796");
        assert_log10(
            "340282366920938463463374607431768211455",
            "38.531839444989593",
        );
        assert_log10("1e100", "100.00000000000000");
        assert_log10("1e1001", "1001.0000000000000");
        assert_log10("1e10001", "10001.000000000000");
    }

    #[test]
    #[should_panic(expected = "cannot take logarithm of zero")]
    fn log_base_0() {
        assert_log("10", "0", "0");
    }

    #[test]
    #[should_panic(expected = "attempt to divide by zero")]
    fn log_base_1() {
        assert_log("10", "1", "0");
    }

    #[test]
    #[should_panic(expected = "cannot take logarithm of a negative number")]
    fn log_base_neg_1() {
        assert_log("10", "-1", "0");
    }

    #[test]
    #[should_panic(expected = "cannot take logarithm of zero")]
    fn log_num_0() {
        assert_log("0", "10", "0");
    }

    #[test]
    #[should_panic(expected = "cannot take logarithm of a negative number")]
    fn log_num_neg_1() {
        assert_log("-1", "10", "0");
    }

    fn assert_exp(val: &str, expected: &str) {
        let var = val.parse::<NumericBuf>().unwrap();
        let exp = var.exp().expect("value overflows numeric format");
        assert_eq!(transform(&exp).to_string(), expected);
    }

    #[test]
    fn exp() {
        assert_exp("0", "1.0000000000000000");
        assert_exp("0.1", "1.1051709180756476");
        assert_exp("0.01", "1.0100501670841681");
        assert_exp("0.001", "1.0010005001667083");
        assert_exp("0.0001", "1.0001000050001667");
        assert_exp("0.00001", "1.0000100000500002");
        assert_exp("1e-100", "1.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001");
        assert_exp("1e-1000", "1.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001");
        assert_exp("1", "2.7182818284590452");
        assert_exp("1.1", "3.0041660239464331");
        assert_exp("1.01", "2.7456010150169165");
        assert_exp("1.001", "2.7210014698815788");
        assert_exp("1.0001", "2.7185536702337533");
        assert_exp("1.00001", "2.7183090114132444");
        assert_exp("10", "22026.465794806717");
        assert_exp("255", "556023164772767541740415404733817020410288002933349011832940579210218980410286121348409867767563330379509903336");
        assert_exp("5999.999999999", "58464389506556757742715682851263106984990895452953711502777054938315137728104094125478144855336563923564281410378196154837236343240109841971159642484545559612611128647986259537540727353082499422700393929169827819041939252594884839161212795670055894767163888788184387613017614459698475310469619130499814731681989658146262916619167035501425184502323844634271011541953092428732126328023453358582978752470327506908693268718502357867363092455106132928091382150563817366709225115521117190047360758302028682705552400878085311034011231294597769272846046775674287290152145374793488068827634452352405597355488923029084902647764663196349252603304677370336647863858075588382598948524281978372343351085060254307652438605308214270096283081893825083180493768679562358476693836638008385378061245701508039491391879420562026970223125599076042263730534975647429694757513145171368563659319752781865442093650739192207002970980074043418610481253817552600962271055482977200284701607349312702177608048188541620346349548482127761279655872395042381075457933320176908063069553594172181193457097946205381872791790644260070035259427324717441847960984608195646987454601336676375525767557868063972876830777253979389799583406394551344280775671765435775897568382724761893322190602488207718643755694028266436505641226451741026060492701526187835753652683565982399187896342117234617221899953092578493405217993759660539549383872656462104189250842676046692504289269251423674619056485082368905645250889578407194353102948526426581766379648008920764834768764364872731373700624376078929072768252178062174216702702801828383650559270461403215754469430115494314193699275090187914862453038418743764553528438020181845501635956759547697935523373496722611661019071604185240280527726468028660889077057714306078534974604195185576289897954357969447343296598295410693276121223867978177890352477701434300899431514252609491821252534059091233456146368620517352440540900587351341408738397051174690879867849306131046790932174757037267260337223162867162374119959916496073570647879538157088301970172038929912103966085788319330091094745247277695299334000338180946080361241241124758981923071961206161725063074212210489255220747257883962391024921866608831907098808592146582520457868857200712124856395305081342687313512455877965026840959577970775949087729274692676456540063053256564799429190781653924007097066873119931409150613916978108748027081147184793669904493015626249718310229384539061224910670686840217422236155115366165185984046105273026635939342007802825021902587737997227083332780575193314890637233989920481370988725657393481074811891089959431164094660573947849.692732630");

        assert_exp("-0.1", "0.9048374180359596");
        assert_exp("-0.01", "0.9900498337491681");
        assert_exp("-0.001", "0.9990004998333750");
        assert_exp("-0.0001", "0.9999000049998333");
        assert_exp("-0.00001", "0.9999900000499998");
        assert_exp("-1e-100", "0.9999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999");
        assert_exp("-1e-1000", "0.9999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999");
        assert_exp("-1", "0.3678794411714423");
        assert_exp("-1.1", "0.3328710836980796");
        assert_exp("-1.01", "0.3642189795715233");
        assert_exp("-1.001", "0.3675117456086936");
        assert_exp("-1.0001", "0.3678426550666611");
        assert_exp("-1.00001", "0.3678757623954245");
        assert_exp("-10", "0.00004539992976248485");
        assert_exp("-255", "0.000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001798486220279463");
        assert_exp("-5999.999999999", "0.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000");
    }

    #[test]
    #[should_panic(expected = "value overflows numeric format")]
    fn exp_overflow() {
        assert_exp("6000", "0");
    }

    #[test]
    #[should_panic(expected = "value overflows numeric format")]
    fn exp_neg_overflow() {
        assert_exp("-6000", "0");
    }

    fn assert_pow(base: &str, exp: &str, expected: &str) {
        let base = base.parse::<NumericBuf>().unwrap();
        let exp = exp.parse::<NumericBuf>().unwrap();
        let pow = base.pow(&exp).expect("value overflows numeric format");
        assert_eq!(transform(&pow).to_string(), expected);
    }

    #[test]
    fn pow() {
        assert_pow("NaN", "1", "NaN");
        assert_pow("NaN", "0", "1");
        assert_pow("1", "NaN", "1");
        assert_pow("0", "NaN", "NaN");
        assert_pow("NaN", "NaN", "NaN");
        assert_pow("0", "0", "1.0000000000000000");
        assert_pow("0", "10", "0.0000000000000000");

        assert_pow("123456789", "0.1", "6.4439401439085569");
        assert_pow("123456789", "0.01", "1.2048005296280134");
        assert_pow("123456789", "0.001", "1.0188060492886508");
        assert_pow("123456789", "0.0001", "1.0018648769006950");
        assert_pow("123456789", "0.00001", "1.0001863313751962");
        assert_pow("123456789", "1e-100", "1.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000019");
        assert_pow("123456789", "1e-1000", "1.0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000019");
        assert_pow("123456789", "1", "123456789.0000000000000000");
        assert_pow("123456789", "1.1", "795548158.67514835");
        assert_pow("123456789", "1.01", "148740804.77337390");
        assert_pow("123456789", "1.001", "125778523.45895257");
        assert_pow("123456789", "1.0001", "123687020.71404007");
        assert_pow("123456789", "1.00001", "123479792.87327168");
        assert_pow("123456789", "10", "822526259147102579504761143661535547764137892295514168093701699676416207799736601.0000000000000000");
        assert_pow("123456789", "255", "216929781174461821388367666119175157169938542864074993568028863236046669912753293208802976771031409046864548133115649294182044010058591851531837033337835679841767892070274770277868749483818013305285905060329514903884877149685804720683917181205777073480247443735762066473655121471621645116398610052324003795298544411034745024926184383550962416015406976843234210530709586956946862466110804199396061525889783174621841738622966368769874560220721500032713429175819739905290386453410064126713059573756325000969245459701640077495814361230015097947208908795490239117471776895631231053289968931911989870158206004989969613455166163928737596171873979515655853161156286380977360294398153216992843783190721368124338469472689538148935868767200678253204222794938332124895228777344744454071512463400710371236141045461531007290554767005553575537944399875674337162101445771641184823025789684604969956657463908283309449470800425002965493487606638252059578081685558240996538088939830188686338557149853613611005068214428766568120315602939862899695755875432967207290990648347468058241874465889661761353099701946372162903719440192647916430865413433504306185054971492337971305019519602985580438511837326587981168979556186227179718135531349784150277071110624924251199185754907026697812377391040821499213464952042381477402003622712494113758262048978201435514346605424491993300797966018009517167181887154848745258773104350199286221886727223789863369590280870272721571257967462490747728535943373856664579009626012602436100242446214989207697160453995334946773906008163326359315014755593055838224071907756213069725926315258387327153833525481998775189642248752131480229805597718639668260054666991806343443582854885582631381476686123461945656381929987873151196561904828115518934973277835325916997148843185136986883240053373132207164087978743532145770605856214073864918097215450694772454582505585554056071496704049576620172369337789259744634828922801712829398927007793828021339079404195942664467916140594209871045592125099540583503200848470540776734770953501268857553769239507978662658907433317949.0000000000000000");

        assert_pow("123456789", "-0.1", "0.1551845575327539");
        assert_pow("123456789", "-0.01", "0.8300129153402295");
        assert_pow("123456789", "-0.001", "0.9815410898847906");
        assert_pow("123456789", "-0.0001", "0.9981385943916269");
        assert_pow("123456789", "-0.00001", "0.9998137033377170");
        assert_pow("123456789", "-1e-100", "0.9999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999981");
        assert_pow("123456789", "-1e-1000", "0.9999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999981");
        assert_pow("123456789", "-1", "0.0000000081000001");
        assert_pow("123456789", "-1.1", "0.000000001256994927453961");
        assert_pow("123456789", "-1.01", "0.000000006723104675436112");
        assert_pow("123456789", "-1.001", "0.000000007950482900416198");
        assert_pow("123456789", "-1.0001", "0.000000008084922688144974");
        assert_pow("123456789", "-1.00001", "0.000000008098491070731777");
        assert_pow("123456789", "-10", "0.0000000000000000");
        assert_pow("123456789", "-255", "0.0000000000000000");

        assert_pow("-123456789", "1", "-123456789.0000000000000000");
        assert_pow("-123456789", "10", "822526259147102579504761143661535547764137892295514168093701699676416207799736601.0000000000000000");
        assert_pow("-123456789", "255", "-216929781174461821388367666119175157169938542864074993568028863236046669912753293208802976771031409046864548133115649294182044010058591851531837033337835679841767892070274770277868749483818013305285905060329514903884877149685804720683917181205777073480247443735762066473655121471621645116398610052324003795298544411034745024926184383550962416015406976843234210530709586956946862466110804199396061525889783174621841738622966368769874560220721500032713429175819739905290386453410064126713059573756325000969245459701640077495814361230015097947208908795490239117471776895631231053289968931911989870158206004989969613455166163928737596171873979515655853161156286380977360294398153216992843783190721368124338469472689538148935868767200678253204222794938332124895228777344744454071512463400710371236141045461531007290554767005553575537944399875674337162101445771641184823025789684604969956657463908283309449470800425002965493487606638252059578081685558240996538088939830188686338557149853613611005068214428766568120315602939862899695755875432967207290990648347468058241874465889661761353099701946372162903719440192647916430865413433504306185054971492337971305019519602985580438511837326587981168979556186227179718135531349784150277071110624924251199185754907026697812377391040821499213464952042381477402003622712494113758262048978201435514346605424491993300797966018009517167181887154848745258773104350199286221886727223789863369590280870272721571257967462490747728535943373856664579009626012602436100242446214989207697160453995334946773906008163326359315014755593055838224071907756213069725926315258387327153833525481998775189642248752131480229805597718639668260054666991806343443582854885582631381476686123461945656381929987873151196561904828115518934973277835325916997148843185136986883240053373132207164087978743532145770605856214073864918097215450694772454582505585554056071496704049576620172369337789259744634828922801712829398927007793828021339079404195942664467916140594209871045592125099540583503200848470540776734770953501268857553769239507978662658907433317949.0000000000000000");
        assert_pow("-123456789", "-1", "-0.0000000081000001");
        assert_pow("-123456789", "-10", "0.0000000000000000");
        assert_pow("-123456789", "-255", "0.0000000000000000");
    }

    #[test]
    #[should_panic(expected = "value overflows numeric format")]
    fn pow_overflow() {
        assert_pow("123456789", "1e100", "0");
    }

    #[test]
    #[should_panic(expected = "zero raised to a negative power is undefined")]
    fn pow_base_0_exp_neg() {
        assert_pow("0", "-1", "0");
    }

    #[test]
    #[should_panic(
        expected = "a negative number raised to a non-integer power yields a complex result"
    )]
    fn pow_base_neg_exp_non_integer() {
        assert_pow("-1", "0.1", "0");
    }

    fn assert_fac(num: i64, expected: Option<&str>) {
        let expected = expected.map(|s| s.to_owned());
        let result = NumericBuf::factorial(num).map(|n| transform(&n).to_string());
        assert_eq!(result, expected);
    }

    #[test]
    fn factorial() {
        assert_fac(-1, Some("1"));
        assert_fac(0, Some("1"));
        assert_fac(1, Some("1"));
        assert_fac(2, Some("2"));
        assert_fac(3, Some("6"));
        assert_fac(4, Some("24"));
        assert_fac(5, Some("120"));
        assert_fac(6, Some("720"));
        assert_fac(7, Some("5040"));
        assert_fac(8, Some("40320"));
        assert_fac(9, Some("362880"));
        assert_fac(10, Some("3628800"));
        assert_fac(101, Some("9425947759838359420851623124482936749562312794702543768327889353416977599316221476503087861591808346911623490003549599583369706302603264000000000000000000000000"));
        assert_fac(1001, Some("402789647337170867317246136356926989705094239074925347176343710340368450911027649612636252695456374205280468598807393254690298539867803367460225153499614535588421928591160833678742451354915921252299285456946271396995850437959540645019696372741142787347450281325324373824456300226871609431497826989489109522725791691167945698509282421538632966523376679891823696900982075223188279465194065489111498586522997573307838057934994706212934291477882221464914058745808179795130018969175605739824237247684512790169648013778158661520384916357285547219660337504067910087936301580874662367543921288988208261944834178369169805682489420504038334529389177845089679546075023305854006141256288633820079940395329251563788399404652902154519302928365169452383531030755684578503851488154092323576150311569325891190105926118761607100286827930472944913272420825078912158741589850136017030887975452922434889688775883386977825215904423682478943313806072144097432418695807412571292308739802481089407002523955080148184062810447564594783139830113821372260474145316521647368313934670783858482781506915288378941348078689691815657785305896912277993200639858696294199549107738635599538328374931258525869323348477334798827676297868823693023377418942304272267800509765805435653787530370118261219994752588866451072715583785495394684524593296728611334955079882857173250037068541860372512693170819259309411027837176612444692649174536429745421086287708588130082168792750697158901737130221751430550976429258055277255676893874108456870904122902259417224707137723406125811549952159629766771063079472679280213882978523785424760309678138268708239764925768714349554665438389311198715040908077757086900159389712443987670244241787904585093011546861502058550090914877900852701619648229332192401075747543562989953271508977501771085759521631427816116191761031257454497039673414248149210836002497114107565960458576525212556159634975715552638678172137468172843066451093984443636560722213668172225585711566558134467392654185460222589723312097599987253417831473939565071006344352518096564427781204200068323913056897090916602712260306869786107237077572445866572945760977721639408338430009976028970539150822336553856613962747814621747092348996915755983464741082000337526945990059365493439921937093368896754791416759604324895514660325913157843796039917819613717350380997781225472000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"));
        assert_fac(32178, None);
    }

    fn assert_apply_typmod(val: &str, typmod: Typmod, overflow: bool, expected: &str) {
        let mut val = val.parse::<NumericBuf>().unwrap();
        let of = val.apply_typmod(typmod);
        assert_eq!(of, overflow);
        if !of {
            assert_eq!(transform(&val).to_string(), expected);
        }
    }

    #[test]
    fn apply_typmod() {
        assert_apply_typmod(
            "123456789.123456789",
            Typmod::new(20, 0).unwrap(),
            false,
            "123456789",
        );

        assert_apply_typmod(
            "123456789.123456789",
            Typmod::new(20, 5).unwrap(),
            false,
            "123456789.12346",
        );

        assert_apply_typmod(
            "123456789.123456789",
            Typmod::new(20, 10).unwrap(),
            false,
            "123456789.1234567890",
        );

        assert_apply_typmod(
            "123456789.123456789",
            Typmod::new(15, 0).unwrap(),
            false,
            "123456789",
        );

        assert_apply_typmod(
            "123456789.123456789",
            Typmod::new(15, 6).unwrap(),
            false,
            "123456789.123457",
        );

        assert_apply_typmod(
            "123456789.123456789",
            Typmod::new(15, 7).unwrap(),
            true,
            "overflow",
        );

        assert_apply_typmod(
            "123456789.123456789",
            Typmod::new(10, 0).unwrap(),
            false,
            "123456789",
        );

        assert_apply_typmod(
            "123456789.123456789",
            Typmod::new(10, 1).unwrap(),
            false,
            "123456789.1",
        );

        assert_apply_typmod(
            "123456789.123456789",
            Typmod::new(10, 2).unwrap(),
            true,
            "overflow",
        );

        assert_apply_typmod(
            "123456789.123456789",
            Typmod::new(9, 0).unwrap(),
            false,
            "123456789",
        );

        assert_apply_typmod(
            "123456789.123456789",
            Typmod::new(9, 1).unwrap(),
            true,
            "overflow",
        );

        assert_apply_typmod(
            "123456789.123456789",
            Typmod::new(8, 0).unwrap(),
            true,
            "overflow",
        );
    }

    fn assert_normalize(val: &str, expected: &str) {
        let n = val.parse::<NumericBuf>().unwrap();
        assert_eq!(transform(&n).to_string(), val);
        assert_eq!(transform(&n).normalize(), expected);
    }

    #[test]
    fn normalize() {
        assert_normalize("NaN", "NaN");
        assert_normalize("0", "0");
        assert_normalize("0.0", "0");
        assert_normalize("0.00001", "0.00001");
        assert_normalize("0.00001000", "0.00001");
        assert_normalize("1.0", "1");
        assert_normalize("1.00000", "1");
        assert_normalize("1.000001", "1.000001");
        assert_normalize("-1.0", "-1");
        assert_normalize("-1.00000", "-1");
        assert_normalize("-1.000001", "-1.000001");
        assert_normalize("100000000", "100000000");
        assert_normalize("100000000.00000000", "100000000");
        assert_normalize("1234.5678", "1234.5678");
    }

    fn assert_hash(val1: &str, val2: &str, eq: bool) {
        use std::collections::hash_map::DefaultHasher;

        let n1 = val1.parse::<NumericBuf>().unwrap();
        let n2 = val2.parse::<NumericBuf>().unwrap();

        let mut hasher1 = DefaultHasher::new();
        let mut hasher2 = DefaultHasher::new();
        transform(&n1).hash(&mut hasher1);
        transform(&n2).hash(&mut hasher2);

        if eq {
            assert_eq!(n1, n2);
            assert_eq!(hasher1.finish(), hasher2.finish());
        } else {
            assert_ne!(n1, n2);
            assert_ne!(hasher1.finish(), hasher2.finish());
        }
    }

    #[test]
    fn hash() {
        assert_hash("NaN", "NaN", true);
        assert_hash("12340.00000", "12340", true);
        assert_hash("10000000000.00000", "1e10", true);
        assert_hash("1.234560e10", "0.123456e11", true);

        assert_hash("NaN", "0", false);
        assert_hash("1", "0", false);
        assert_hash("1", "-1", false);
        assert_hash("12", "21", false);
        assert_hash("10002000", "20001000", false);
        assert_hash("1000.2000", "2000.1000", false);
        assert_hash("1.0002", "2.0001", false);
    }

    fn assert_bytes(val: &str) {
        let n = val.parse::<NumericBuf>().unwrap();
        let bytes = n.as_bytes();
        let n2 = unsafe { Numeric::from_bytes_unchecked(bytes).to_owned() };
        assert_eq!(n2, n);

        let bytes = n.as_binary().as_bytes();
        let n3 = unsafe { Numeric::from_bytes_unchecked(bytes).to_owned() };
        assert_eq!(n3, n);
    }

    #[test]
    fn bytes() {
        assert_bytes("NaN");
        assert_bytes("0");
        assert_bytes("0.00000");
        assert_bytes("123456789.987654321");
        assert_bytes("170141183460469231731687303715884105727");
        assert_bytes("-170141183460469231731687303715884105728");
        assert_bytes("1e100");
        assert_bytes("1e-100");
    }

    #[test]
    fn owned() {
        // negate
        {
            let n = "123.456".parse().unwrap();
            let mut n2 = transform(&n).to_owned();
            n2.negate_mut();
            assert_eq!(n2.to_string(), "-123.456");
        }

        // round
        {
            let n = "123.456".parse().unwrap();
            let n2 = transform(&n).round(2);
            assert_eq!(n2.to_string(), "123.46");
        }

        // trunc
        {
            let n = "123.456".parse().unwrap();
            let n2 = transform(&n).trunc(2);
            assert_eq!(n2.to_string(), "123.45");
        }

        // abs
        {
            let n = "-123.456".parse().unwrap();
            let mut n2 = transform(&n).to_owned();
            n2.abs_mut();
            assert_eq!(n2.to_string(), "123.456");
        }

        // apply typmod
        {
            let typmod = Typmod::new(6, 2).unwrap();

            let n = "123.456".parse().unwrap();
            let mut n2 = transform(&n).to_owned();
            n2.apply_typmod(typmod);
            assert_eq!(n2.to_string(), "123.46");
        }
    }

    #[test]
    fn constant() {
        let zero = NumericBuf::from(0);
        assert_eq!(Numeric::zero(), zero);

        let nan = "NaN".parse::<NumericBuf>().unwrap();
        assert_eq!(Numeric::nan(), nan);
    }
}
