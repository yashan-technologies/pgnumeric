// Copyright 2020 CoD Technologies Corp.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! NumericVar.

use crate::binary::{
    NumericDigit, NUMERIC_DIGIT_SIZE, NUMERIC_DSCALE_MAX, NUMERIC_HEADER_NDIGITS, NUMERIC_NAN,
    NUMERIC_NEG, NUMERIC_POS, NUMERIC_WEIGHT_MAX, NUMERIC_WEIGHT_MIN, VAR_HEADER_SIZE,
};
use crate::data::{NumericData, NumericDigits};
use crate::num::{NumericBuf, DIVIDE_BY_ZERO_MSG};
use crate::typmod::Typmod;
use lazy_static::lazy_static;
use std::borrow::Cow;
use std::convert::{TryFrom, TryInto};
use std::f64::consts::{LN_10, LOG10_2, LOG10_E};
use std::fmt;

/// Limit on the precision (and hence scale) specifiable in a NUMERIC typmod.
/// Note that the implementation limit on the length of a numeric value is
/// much larger --- beware of what you use this for!
pub const NUMERIC_MAX_PRECISION: i32 = 1000;

// Internal limits on the scales chosen for calculation results
const NUMERIC_MAX_DISPLAY_SCALE: i32 = NUMERIC_MAX_PRECISION;
const NUMERIC_MIN_DISPLAY_SCALE: i32 = 0;

const NUMERIC_MAX_RESULT_SCALE: i32 = NUMERIC_MAX_PRECISION * 2;

/// For inherently inexact calculations such as division and square root,
/// we try to get at least this many significant digits; the idea is to
/// deliver a result no worse than f64 would.
const NUMERIC_MIN_SIG_DIGITS: i32 = 16;

pub const NBASE: i32 = 10000;
const HALF_NBASE: NumericDigit = 5000;
pub const DEC_DIGITS: i32 = 4;
const MUL_GUARD_DIGITS: i32 = 2;
const DIV_GUARD_DIGITS: i32 = 4;

const ROUND_POWERS: [NumericDigit; 4] = [0, 1000, 100, 10];

lazy_static! {
    // 0
    static ref ZERO: NumericVar<'static> = NumericVar::zero();
    // 1
    static ref ONE: NumericVar<'static> = NumericVar::borrowed(1, 0, 0, NUMERIC_POS, &[1]);
    // 2
    static ref TWO: NumericVar<'static> = NumericVar::borrowed(1, 0, 0, NUMERIC_POS, &[2]);
    // 10
    static ref TEN: NumericVar<'static> = NumericVar::borrowed(1, 0, 0, NUMERIC_POS, &[10]);

    // 0.5
    static ref ZERO_POINT_FIVE: NumericVar<'static> = NumericVar::borrowed(1, -1, 1, NUMERIC_POS, &[5000]);
    // 0.9
    static ref ZERO_POINT_NINE: NumericVar<'static> = NumericVar::borrowed(1, -1, 1, NUMERIC_POS, &[9000]);
    // 1.1
    static ref ONE_POINT_ONE: NumericVar<'static> = NumericVar::borrowed(2, 0, 1, NUMERIC_POS, &[1, 1000]);
}

/// `NumericVar` is the format we use for arithmetic.  The `digits`-array part
/// is the same as the `NumericBinary` storage format, but the header is more
/// complex.
///
/// The value represented by a `Numeric` is determined by the `sign`, `weight`,
/// `ndigits`, and `digits[]` array.
///
/// Note: the first digit of a Numeric's value is assumed to be multiplied
/// by NBASE ** weight.  Another way to say it is that there are weight+1
/// digits before the decimal point.  It is possible to have weight < 0.
///
/// `data.buf` points at the physical start of the digit buffer for the
/// Numeric. `data.offset` points at the first digit in actual use (the one
/// with the specified weight).  We normally leave an unused digit or two
/// (preset to zeroes) between buf and digits, so that there is room to store
/// a carry out of the top digit without reallocating space.  We just need to
/// decrement digits (and increment weight) to make room for the carry digit.
/// (There is no such extra space in a numeric value stored in the database,
/// only in a Numeric in memory.)
///
/// `dscale`, or display scale, is the nominal precision expressed as number
/// of digits after the decimal point (it must always be >= 0 at present).
/// dscale may be more than the number of physically stored fractional digits,
/// implying that we have suppressed storage of significant trailing zeroes.
/// It should never be less than the number of stored digits, since that would
/// imply hiding digits that are present.  NOTE that dscale is always expressed
/// in *decimal* digits, and so it may correspond to a fractional number of
/// base-NBASE digits --- divide by DEC_DIGITS to convert to NBASE digits.
///
/// While we consistently use `weight` to refer to the base-NBASE weight of
/// a numeric value, it is convenient in some scale-related calculations to
/// make use of the base-10 weight (ie, the approximate log10 of the value).
/// To avoid confusion, such a decimal-units weight is called a "dweight".
///
#[derive(Debug, Clone)]
pub(crate) struct NumericVar<'a> {
    ndigits: i32,
    weight: i32,
    dscale: i32,
    sign: u16,
    digits: Cow<'a, NumericDigits>,
}

impl<'a> NumericVar<'a> {
    /// Creates a `NumericVar` with `ndigits` data space.
    #[inline]
    fn with_ndigits(ndigits: i32) -> Self {
        debug_assert!(ndigits >= 0);
        NumericVar {
            ndigits,
            weight: 0,
            dscale: 0,
            sign: 0,
            digits: Cow::Owned(NumericData::with_ndigits(ndigits)),
        }
    }

    /// Creates a `NumericVar` of `NaN`, which has no data space.
    #[inline]
    pub fn nan() -> Self {
        NumericVar::borrowed(0, 0, 0, NUMERIC_NAN, &[])
    }

    /// Creates a `NumericVar` of zero with given scale.
    #[inline]
    fn zero_scaled(scale: i32) -> NumericVar<'a> {
        debug_assert!(scale >= 0 && scale <= NUMERIC_DSCALE_MAX as i32);
        Self::borrowed(0, 0, scale, NUMERIC_POS, &[])
    }

    /// Creates a `NumericVar` with borrowed data space.
    #[inline]
    pub fn borrowed(
        ndigits: i32,
        weight: i32,
        dscale: i32,
        sign: u16,
        digits: &'a [NumericDigit],
    ) -> Self {
        debug_assert_eq!(ndigits as usize, digits.len());
        let digits = Cow::Borrowed(unsafe { NumericDigits::from_slice_unchecked(digits) });
        NumericVar {
            ndigits,
            weight,
            dscale,
            sign,
            digits,
        }
    }

    /// Creates a `NumericVar` with given data space.
    #[inline]
    pub fn owned(ndigits: i32, weight: i32, dscale: i32, sign: u16, digits: NumericData) -> Self {
        debug_assert!(digits.offset() + ndigits as u32 <= digits.len());
        NumericVar {
            ndigits,
            weight,
            dscale,
            sign,
            digits: Cow::Owned(digits),
        }
    }

    /// Creates a `NumericVar` of zero.
    #[inline]
    pub fn zero() -> Self {
        NumericVar::borrowed(0, 0, 0, NUMERIC_POS, &[])
    }

    #[inline]
    pub fn ndigits(&self) -> i32 {
        self.ndigits
    }

    #[inline]
    pub fn weight(&self) -> i32 {
        self.weight
    }

    #[inline]
    pub fn dscale(&self) -> i32 {
        self.dscale
    }

    /// Checks if `self` is `NaN`.
    #[inline]
    pub const fn is_nan(&self) -> bool {
        self.sign == NUMERIC_NAN
    }

    /// Checks if `self` is positive.
    #[inline]
    pub const fn is_positive(&self) -> bool {
        self.sign == NUMERIC_POS
    }

    /// Checks if `self` is negative.
    #[inline]
    pub const fn is_negative(&self) -> bool {
        self.sign == NUMERIC_NEG
    }

    #[inline]
    pub fn digits(&self) -> &[NumericDigit] {
        &self.digits.as_slice()[0..self.ndigits as usize]
    }

    #[inline]
    pub fn into_numeric_buf(self) -> NumericBuf {
        let mut data = self.digits.into_owned();
        let header_offset = data.set_header(
            self.weight as i16,
            self.dscale as u16,
            self.sign as u16,
            self.ndigits,
        );

        let (buf, len, _) = data.into_raw_parts();

        unsafe {
            NumericBuf::from_raw_parts(buf as *const u8, len * NUMERIC_DIGIT_SIZE, header_offset)
        }
    }

    /// Round the value of a variable to no more than rscale decimal digits
    /// after the decimal point.
    ///
    /// NOTE: we allow rscale < 0 here, implying rounding before the decimal point.
    pub fn round_common(&mut self, rscale: i32) {
        debug_assert!(!self.is_nan());

        // decimal digits wanted
        let di = (self.weight + 1) * DEC_DIGITS + rscale;

        // If di = 0, the value loses all digits, but could round up to 1 if its
        // first extra digit is >= 5.  If di < 0 the result must be 0.
        if di < 0 {
            self.ndigits = 0;
            self.weight = 0;
            self.sign = NUMERIC_POS;
        } else {
            // NBASE digits wanted
            let mut ndigits = (di + DEC_DIGITS - 1) / DEC_DIGITS;
            // 0, or number of decimal digits to keep in last NBASE digit
            let di = di % DEC_DIGITS;

            if ndigits < self.ndigits || (ndigits == self.ndigits && di > 0) {
                let data = self.digits.to_mut();

                if self.ndigits > 0 {
                    data.reserve_rounding_digit(self.ndigits);
                }

                // Carry may need one additional digit
                debug_assert!(data.offset() > NUMERIC_HEADER_NDIGITS || self.ndigits == 0);

                let digits = data.digits_mut(self.ndigits);

                self.ndigits = ndigits;

                let mut carry: i32 = 0;

                if di == 0 {
                    if digits[ndigits as usize] >= HALF_NBASE {
                        carry = 1;
                    }
                } else {
                    // Must round within last NBASE digit
                    let mut pow10 = ROUND_POWERS[di as usize];
                    ndigits -= 1;
                    debug_assert!((ndigits as usize) < digits.len());
                    let digit = unsafe { digits.get_unchecked_mut(ndigits as usize) };
                    let extra = *digit % pow10;
                    *digit -= extra;

                    if extra >= pow10 / 2 {
                        pow10 += *digit;
                        if pow10 >= NBASE as NumericDigit {
                            pow10 -= NBASE as NumericDigit;
                            carry = 1;
                        }
                        *digit = pow10;
                    }
                }

                let offset = data.offset();
                // Carry may need one additional digit, so we use buf from start.
                let digits = data.as_mut_slice();
                digits[offset as usize - 1] = 0;

                // Propagate carry if needed
                while carry > 0 {
                    ndigits -= 1;
                    let i = (offset as i32 + ndigits) as usize;
                    debug_assert!(i < digits.len());
                    let digit = unsafe { digits.get_unchecked_mut(i) };
                    carry += *digit as i32;

                    if carry >= NBASE as i32 {
                        *digit = (carry - NBASE as i32) as NumericDigit;
                        carry = 1;
                    } else {
                        *digit = carry as NumericDigit;
                        carry = 0;
                    }
                }

                if ndigits < 0 {
                    debug_assert_eq!(ndigits, -1);
                    debug_assert!(data.offset() > 0);
                    data.offset_sub(1);
                    self.ndigits += 1;
                    self.weight += 1;
                }
            }
        }

        self.dscale = rscale;
    }

    /// Truncate (towards zero) the value of a variable at rscale decimal digits
    /// after the decimal point.
    ///
    /// NOTE: we allow rscale < 0 here, implying truncation before the decimal point.
    pub fn trunc_common(&mut self, rscale: i32) {
        debug_assert!(!self.is_nan());

        // decimal digits wanted
        let di = (self.weight + 1) * DEC_DIGITS + rscale;

        // If di <= 0, the value loses all digits.
        if di <= 0 {
            self.ndigits = 0;
            self.weight = 0;
            self.sign = NUMERIC_POS;
        } else {
            // NBASE digits wanted
            let mut ndigits = (di + DEC_DIGITS - 1) / DEC_DIGITS;

            if ndigits <= self.ndigits {
                self.ndigits = ndigits;

                // 0, or number of decimal digits to keep in last NBASE digit
                let di = di % DEC_DIGITS;

                if di > 0 {
                    let data = self.digits.to_mut();
                    let digits = data.digits_mut(self.ndigits);
                    let pow10 = ROUND_POWERS[di as usize];
                    ndigits -= 1;

                    let extra = digits[ndigits as usize] % pow10;
                    digits[ndigits as usize] -= extra;
                }
            }
        }

        self.dscale = rscale;
    }

    /// Return the smallest integer greater than or equal to the argument
    /// on variable level
    #[inline]
    pub fn ceil_common(&self) -> Self {
        debug_assert!(!self.is_nan());

        let mut result = self.clone();
        result.trunc_common(0);

        if self.is_positive() && self.cmp_common(&result) != 0 {
            result = result.add_common(&ONE);
        }

        result
    }

    /// Return the largest integer equal to or less than the argument
    /// on variable level
    #[inline]
    pub fn floor_common(&self) -> Self {
        debug_assert!(!self.is_nan());

        let mut result = self.clone();
        result.trunc_common(0);

        if self.is_negative() && self.cmp_common(&result) != 0 {
            result = result.sub_common(&ONE);
        }

        result
    }

    /// Strips the leading and trailing zeroes, and normalize zero.
    pub fn strip(&mut self) {
        let data = self.digits.to_mut();

        let digits = data.digits(self.ndigits);
        let mut ndigits = self.ndigits;
        let mut i = 0;

        // strip leading zeroes
        while ndigits > 0 && unsafe { *digits.get_unchecked(i) } == 0 {
            i += 1;
            self.weight -= 1;
            ndigits -= 1;
        }

        // strip trailing zeroes
        while ndigits > 0 && unsafe { *digits.get_unchecked(i + ndigits as usize - 1) } == 0 {
            ndigits -= 1;
        }

        // if it's zero, normalize the sign and weight
        if ndigits == 0 {
            self.sign = NUMERIC_POS;
            self.weight = 0;
        }

        data.offset_add(i as u32);
        self.ndigits = ndigits;
    }

    /// Add the absolute values of two variables into result.
    pub fn add_abs(&self, other: &Self) -> Self {
        debug_assert!(!self.is_nan());
        debug_assert!(!other.is_nan());

        // copy these values into local vars for speed in inner loop
        let var1_ndigits = self.ndigits;
        let var2_ndigits = other.ndigits;
        let var1_digits = self.digits();
        let var2_digits = other.digits();

        let res_weight = self.weight.max(other.weight) + 1;
        let res_dscale = self.dscale.max(other.dscale);

        // Note: here we are figuring rscale in base-NBASE digits
        let res_rscale = {
            let rscale1 = self.ndigits - self.weight - 1;
            let rscale2 = other.ndigits - other.weight - 1;
            rscale1.max(rscale2)
        };

        let res_ndigits = {
            let ndigits = res_rscale + res_weight + 1;
            if ndigits > 0 {
                ndigits
            } else {
                1
            }
        };

        let mut res = Self::with_ndigits(res_ndigits);
        let data = res.digits.to_mut();
        let res_digits = data.digits_mut(res_ndigits);

        let mut carry: NumericDigit = 0;
        let mut i1 = res_rscale + self.weight + 1;
        let mut i2 = res_rscale + other.weight + 1;
        for i in (0..res_ndigits as usize).rev() {
            i1 -= 1;
            i2 -= 1;

            if i1 >= 0 && i1 < var1_ndigits {
                carry += unsafe { *var1_digits.get_unchecked(i1 as usize) };
            }
            if i2 >= 0 && i2 < var2_ndigits {
                carry += unsafe { *var2_digits.get_unchecked(i2 as usize) };
            }

            let digit = unsafe { res_digits.get_unchecked_mut(i) };
            if carry >= NBASE as NumericDigit {
                *digit = carry - NBASE as NumericDigit;
                carry = 1;
            } else {
                *digit = carry;
                carry = 0;
            }
        }

        debug_assert_eq!(carry, 0); // else we failed to allow for carry out

        res.weight = res_weight;
        res.dscale = res_dscale;

        // Remove leading/trailing zeroes
        res.strip();

        res
    }

    /// Subtract the absolute value of `other` from the absolute value of `self`
    /// and store in result.
    ///
    /// NOTE: ABS(`self`) MUST BE GREATER OR EQUAL ABS(`other`) !!!
    pub fn sub_abs(&self, other: &Self) -> Self {
        debug_assert!(!self.is_nan());
        debug_assert!(!other.is_nan());

        // copy these values into local vars for speed in inner loop
        let var1_ndigits = self.ndigits;
        let var2_ndigits = other.ndigits;
        let var1_digits = self.digits();
        let var2_digits = other.digits();

        let res_weight = self.weight;
        let res_dscale = self.dscale.max(other.dscale);

        // Note: here we are figuring rscale in base-NBASE digits
        let res_rscale = {
            let rscale1 = self.ndigits - self.weight - 1;
            let rscale2 = other.ndigits - other.weight - 1;
            rscale1.max(rscale2)
        };

        let res_ndigits = {
            let ndigits = res_rscale + res_weight + 1;
            if ndigits <= 0 {
                1
            } else {
                ndigits
            }
        };

        let mut res = Self::with_ndigits(res_ndigits);
        let data = res.digits.to_mut();
        let res_digits = data.digits_mut(res_ndigits);

        let mut borrow: NumericDigit = 0;
        let mut i1 = res_rscale + self.weight + 1;
        let mut i2 = res_rscale + other.weight + 1;
        for i in (0..res_ndigits as usize).rev() {
            i1 -= 1;
            i2 -= 1;

            if i1 >= 0 && i1 < var1_ndigits {
                borrow += unsafe { *var1_digits.get_unchecked(i1 as usize) };
            }
            if i2 >= 0 && i2 < var2_ndigits {
                borrow -= unsafe { *var2_digits.get_unchecked(i2 as usize) };
            }

            let digit = unsafe { res_digits.get_unchecked_mut(i) };
            if borrow < 0 {
                *digit = borrow + NBASE as NumericDigit;
                borrow = -1;
            } else {
                *digit = borrow;
                borrow = 0;
            }
        }

        debug_assert_eq!(borrow, 0); // else caller gave us self < other

        res.weight = res_weight;
        res.dscale = res_dscale;

        // Remove leading/trailing zeroes
        res.strip();

        res
    }

    /// Compare the absolute values of `self` and `other`
    ///
    /// * -1 for ABS(`self`) < ABS(`other`)
    /// * 0 for ABS(`self`) == ABS(`other`)
    /// * 1 for ABS(`self`) > ABS(`other`)
    pub fn cmp_abs(&self, other: &Self) -> i32 {
        debug_assert!(!self.is_nan());
        debug_assert!(!other.is_nan());

        let var1_ndigits = self.ndigits;
        let var1_digits = self.digits();
        let mut var1_weight = self.weight;

        let var2_ndigits = other.ndigits;
        let var2_digits = other.digits();
        let mut var2_weight = other.weight;

        let mut i1 = 0;
        let mut i2 = 0;

        // Check any digits before the first common digit

        while var1_weight > var2_weight && i1 < var1_ndigits {
            if unsafe { *var1_digits.get_unchecked(i1 as usize) } != 0 {
                return 1;
            }

            i1 += 1;
            var1_weight -= 1;
        }
        while var2_weight > var1_weight && i2 < var2_ndigits {
            if unsafe { *var2_digits.get_unchecked(i2 as usize) } != 0 {
                return -1;
            }

            i2 += 1;
            var2_weight -= 1;
        }

        // At this point, either var1_weight == var2_weight or we've run out of digits

        if var1_weight == var2_weight {
            while i1 < var1_ndigits && i2 < var2_ndigits {
                let stat = unsafe {
                    *var1_digits.get_unchecked(i1 as usize)
                        - *var2_digits.get_unchecked(i2 as usize)
                };
                if stat != 0 {
                    return if stat > 0 { 1 } else { -1 };
                } else {
                    i1 += 1;
                    i2 += 1;
                }
            }
        }

        // At this point, we've run out of digits on one side or the other; so any
        // remaining nonzero digits imply that side is larger
        while i1 < var1_ndigits {
            if unsafe { *var1_digits.get_unchecked(i1 as usize) } != 0 {
                return 1;
            }

            i1 += 1;
        }
        while i2 < var2_ndigits {
            if unsafe { *var2_digits.get_unchecked(i2 as usize) } != 0 {
                return -1;
            }

            i2 += 1;
        }

        0
    }

    /// Full version of add functionality on variable level (handling signs).
    pub fn add_common(&self, other: &Self) -> Self {
        debug_assert!(!self.is_nan());
        debug_assert!(!other.is_nan());

        // Decide on the signs of the two variables what to do
        if self.is_positive() {
            if other.is_positive() {
                // Both are positive
                // result = +(ABS(self) + ABS(other))
                let mut result = self.add_abs(other);
                result.sign = NUMERIC_POS;
                result
            } else {
                let cmp = self.cmp_abs(other);
                match cmp {
                    0 => {
                        // ABS(self) == ABS(other)
                        // result = ZERO
                        Self::zero_scaled(self.dscale.max(other.dscale))
                    }
                    1 => {
                        // ABS(self) > ABS(other)
                        // result = +(ABS(self) - ABS(other))
                        let mut result = self.sub_abs(other);
                        result.sign = NUMERIC_POS;
                        result
                    }
                    -1 => {
                        // ABS(self) < ABS(other)
                        // result = -(ABS(other) - ABS(self))
                        let mut result = other.sub_abs(self);
                        result.sign = NUMERIC_NEG;
                        result
                    }
                    _ => panic!("invalid comparison result"),
                }
            }
        } else if other.is_positive() {
            // self is negative, other is positive
            // Must compare absolute values
            let cmp = self.cmp_abs(other);
            match cmp {
                0 => {
                    // ABS(self) == ABS(other)
                    // result = ZERO
                    Self::zero_scaled(self.dscale.max(other.dscale))
                }
                1 => {
                    // ABS(self) > ABS(other)
                    // result = -(ABS(self) - ABS(other))
                    let mut result = self.sub_abs(other);
                    result.sign = NUMERIC_NEG;
                    result
                }
                -1 => {
                    // ABS(self) < ABS(other)
                    // result = +(ABS(other) - ABS(self))
                    let mut result = other.sub_abs(self);
                    result.sign = NUMERIC_POS;
                    result
                }
                _ => panic!("invalid comparison result"),
            }
        } else {
            // Both are negative
            // result = -(ABS(self) + ABS(other))
            let mut result = self.add_abs(other);
            result.sign = NUMERIC_NEG;
            result
        }
    }

    /// Full version of sub functionality on variable level (handling signs).
    pub fn sub_common(&self, other: &Self) -> Self {
        debug_assert!(!self.is_nan());
        debug_assert!(!other.is_nan());

        // Decide on the signs of the two variables what to do
        if self.is_positive() {
            if other.is_negative() {
                // self is positive, other is negative
                // result = +(ABS(self) + ABS(other))
                let mut result = self.add_abs(other);
                result.sign = NUMERIC_POS;
                result
            } else {
                // Both are positive
                // Must compare absolute values
                let cmp = self.cmp_abs(other);
                match cmp {
                    0 => {
                        // ABS(self) == ABS(other)
                        // result = ZERO
                        Self::zero_scaled(self.dscale.max(other.dscale))
                    }
                    1 => {
                        // ABS(self) > ABS(other)
                        // result = +(ABS(self) - ABS(other))
                        let mut result = self.sub_abs(other);
                        result.sign = NUMERIC_POS;
                        result
                    }
                    -1 => {
                        // ABS(self) < ABS(other)
                        // result = -(ABS(other) - ABS(self))
                        let mut result = other.sub_abs(self);
                        result.sign = NUMERIC_NEG;
                        result
                    }
                    _ => panic!("invalid comparison result"),
                }
            }
        } else if other.is_negative() {
            // Both are negative
            // Must compare absolute values
            let cmp = self.cmp_abs(other);
            match cmp {
                0 => {
                    // ABS(self) == ABS(other)
                    // result = ZERO
                    Self::zero_scaled(self.dscale.max(other.dscale))
                }
                1 => {
                    // ABS(self) > ABS(other)
                    // result = -(ABS(self) - ABS(other))
                    let mut result = self.sub_abs(other);
                    result.sign = NUMERIC_NEG;
                    result
                }
                -1 => {
                    // ABS(self) < ABS(other)
                    // result = +(ABS(other) - ABS(self))
                    let mut result = other.sub_abs(self);
                    result.sign = NUMERIC_POS;
                    result
                }
                _ => panic!("invalid comparison result"),
            }
        } else {
            // var1 is negative, var2 is positive
            // result = -(ABS(self) + ABS(other))
            let mut result = self.add_abs(other);
            result.sign = NUMERIC_NEG;
            result
        }
    }

    /// Multiplication on variable level.
    /// Product of self * other is returned.
    /// Result is rounded to no more than rscale fractional digits.
    pub fn mul_common(&self, other: &Self, rscale: i32) -> Self {
        debug_assert!(!self.is_nan());
        debug_assert!(!other.is_nan());

        // Arrange for var1 to be the shorter of the two numbers.  This improves
        // performance because the inner multiplication loop is much simpler than
        // the outer loop, so it's better to have a smaller number of iterations
        // of the outer loop.  This also reduces the number of times that the
        // accumulator array needs to be normalized.
        let (var1, var2) = if self.ndigits > other.ndigits {
            (other, self)
        } else {
            (self, other)
        };

        // copy these values into local vars for speed in inner loop
        let var1_ndigits = var1.ndigits;
        let var1_digits = var1.digits();
        let var2_ndigits = var2.ndigits;
        let var2_digits = var2.digits();

        if var1_ndigits == 0 || var2_ndigits == 0 {
            // one or both inputs is zero; so is result
            return Self::zero_scaled(rscale);
        }

        // Determine result sign and (maximum possible) weight
        let res_sign = if var1.sign == var2.sign {
            NUMERIC_POS
        } else {
            NUMERIC_NEG
        };
        let res_weight = var1.weight + var2.weight + 2;

        // Determine the number of result digits to compute.  If the exact result
        // would have more than rscale fractional digits, truncate the computation
        // with MUL_GUARD_DIGITS guard digits, i.e., ignore input digits that
        // would only contribute to the right of that.  (This will give the exact
        // rounded-to-rscale answer unless carries out of the ignored positions
        // would have propagated through more than MUL_GUARD_DIGITS digits.)
        //
        // Note: an exact computation could not produce more than var1ndigits +
        // var2ndigits digits, but we allocate one extra output digit in case
        // rscale-driven rounding produces a carry out of the highest exact digit.
        let res_ndigits = {
            let ndigits = var1.ndigits + var2.ndigits + 1;
            let max_digits =
                res_weight + 1 + (rscale + DEC_DIGITS - 1) / DEC_DIGITS + MUL_GUARD_DIGITS;
            ndigits.min(max_digits)
        };

        if res_ndigits < 3 {
            // All input digits will be ignored; so result is zero
            return Self::zero_scaled(rscale);
        }

        // We do the arithmetic in an array "dig[]" of signed int32's.  Since
        // INT32_MAX is noticeably larger than NBASE*NBASE, this gives us headroom
        // to avoid normalizing carries immediately.
        //
        // max_dig tracks the maximum possible value of any dig[] entry; when this
        // threatens to exceed INT32_MAX, we take the time to propagate carries.
        // Furthermore, we need to ensure that overflow doesn't occur during the
        // carry propagation passes either.  The carry values could be as much as
        // INT32_MAX/NBASE, so really we must normalize when digits threaten to
        // exceed INT32_MAX - INT32_MAX/NBASE.
        //
        // To avoid overflow in max_dig itself, it actually represents the max
        // possible value divided by NBASE-1, ie, at the top of the loop it is
        // known that no dig[] entry exceeds max_dig * (NBASE-1).
        let mut dig = vec![0; res_ndigits as usize * std::mem::size_of::<i32>()];
        let mut max_dig = 0i32;

        // The least significant digits of var1 should be ignored if they don't
        // contribute directly to the first res_ndigits digits of the result that
        // we are computing.
        //
        // Digit i1 of var1 and digit i2 of var2 are multiplied and added to digit
        // i1+i2+2 of the accumulator array, so we need only consider digits of
        // var1 for which i1 <= res_ndigits - 3.
        let bound = (var1_ndigits - 1).min(res_ndigits - 3);
        for i1 in (0..=bound).rev() {
            let var1_digit = unsafe { *var1_digits.get_unchecked(i1 as usize) } as i32;
            if var1_digit == 0 {
                continue;
            }

            // Time to normalize?
            max_dig += var1_digit;
            if max_dig > ((i32::max_value() - i32::max_value() / NBASE) / (NBASE - 1)) {
                // Yes, do it
                let mut carry = 0;
                for i in (0..res_ndigits).rev() {
                    let d = unsafe { dig.get_unchecked_mut(i as usize) };
                    let mut new_dig = *d + carry;
                    if new_dig >= NBASE {
                        carry = new_dig / NBASE;
                        new_dig -= carry * NBASE;
                    } else {
                        carry = 0;
                    }
                    *d = new_dig;
                }
                debug_assert_eq!(carry, 0);
                // Reset max_dig to indicate new worst-case
                max_dig = 1 + var1_digit;
            }

            // Add the appropriate multiple of var2 into the accumulator.
            //
            // As above, digits of var2 can be ignored if they don't contribute,
            // so we only include digits for which i1+i2+2 <= res_ndigits - 1.
            let bound = (var2_ndigits - 1).min(res_ndigits - i1 - 3);
            let mut i = i1 + bound + 2;
            for i2 in (0..=bound).rev() {
                let d = unsafe { dig.get_unchecked_mut(i as usize) };
                *d += var1_digit * unsafe { *var2_digits.get_unchecked(i2 as usize) } as i32;
                i -= 1;
            }
        }

        // Now we do a final carry propagation pass to normalize the result, which
        // we combine with storing the result digits into the output. Note that
        // this is still done at full precision w/guard digits.
        let mut result = Self::with_ndigits(res_ndigits);
        let data = result.digits.to_mut();
        let res_digits = data.digits_mut(res_ndigits);
        let mut carry = 0;
        for i in (0..res_ndigits).rev() {
            let mut new_dig = unsafe { dig.get_unchecked(i as usize) } + carry;
            if new_dig >= NBASE {
                carry = new_dig / NBASE;
                new_dig -= carry * NBASE;
            } else {
                carry = 0;
            }
            let res_digit = unsafe { res_digits.get_unchecked_mut(i as usize) };
            *res_digit = new_dig as NumericDigit;
        }
        debug_assert_eq!(carry, 0);

        // Finally, round the result to the requested precision.

        result.weight = res_weight;
        result.sign = res_sign;

        // Round to target rscale (and set result->dscale)
        result.round_common(rscale);

        // Strip leading and trailing zeroes
        result.strip();

        result
    }

    /// Default scale selection for division
    ///
    /// Returns the appropriate result scale for the division result.
    pub fn select_div_scale(&self, other: &Self) -> i32 {
        // The result scale of a division isn't specified in any SQL standard. For
        // PostgreSQL we select a result scale that will give at least
        // NUMERIC_MIN_SIG_DIGITS significant digits, so that numeric gives a
        // result no less accurate than f64; but use a scale not less than
        // either input's display scale.

        // Get the actual (normalized) weight and first digit of each input.

        let mut weight1 = 0; // values to use if self is zero
        let mut first_digit1 = 0;
        let var1_digits = self.digits();
        for i in 0..self.ndigits {
            first_digit1 = unsafe { *var1_digits.get_unchecked(i as usize) };
            if first_digit1 != 0 {
                weight1 = self.weight - i;
                break;
            }
        }

        let mut weight2 = 0; // values to use if other is zero
        let mut first_digit2 = 0;
        let var2_digits = other.digits();
        for i in 0..other.ndigits {
            first_digit2 = unsafe { *var2_digits.get_unchecked(i as usize) };
            if first_digit2 != 0 {
                weight2 = other.weight - i;
                break;
            }
        }

        // Estimate weight of quotient.  If the two first digits are equal, we
        // can't be sure, but assume that self is less than other.
        let qweight = {
            let mut w = weight1 - weight2;
            if first_digit1 <= first_digit2 {
                w -= 1;
            }
            w
        };

        // Select result scale
        (NUMERIC_MIN_SIG_DIGITS - qweight * DEC_DIGITS)
            .max(self.dscale)
            .max(other.dscale)
            .max(NUMERIC_MIN_DISPLAY_SCALE)
            .min(NUMERIC_MAX_DISPLAY_SCALE)
    }

    /// Division on variable level. Quotient of `self` / `other` is returned.
    /// The quotient is figured to exactly rscale fractional digits.
    /// If round is true, it is rounded at the rscale'th digit; if false, it
    /// is truncated (towards zero) at that digit.
    ///
    /// Returns `None` if `other == 0`.
    #[allow(clippy::cognitive_complexity)]
    pub fn div_common(&self, other: &Self, rscale: i32, round: bool) -> Option<Self> {
        debug_assert!(!self.is_nan());
        debug_assert!(!other.is_nan());

        // copy these values into local vars for speed in inner loop
        let var1_ndigits = self.ndigits;
        let var2_ndigits = other.ndigits;

        // First of all division by zero check; we must not be handed an
        // unnormalized divisor.
        if var2_ndigits == 0 || other.digits[0] == 0 {
            return None;
        }

        // Now result zero check
        if var1_ndigits == 0 {
            return Some(Self::zero_scaled(rscale));
        }

        // Determine the result sign, weight and number of digits to calculate.
        // The weight figured here is correct if the emitted quotient has no
        // leading zero digits; otherwise strip() will fix things up.
        let res_sign = if self.sign == other.sign {
            NUMERIC_POS
        } else {
            NUMERIC_NEG
        };
        let res_weight = self.weight - other.weight;
        let res_ndigits = {
            // The number of accurate result digits we need to produce
            let mut ndigits = res_weight + 1 + (rscale + DEC_DIGITS - 1) / DEC_DIGITS;
            // ... but always at least 1
            ndigits = ndigits.max(1);
            // If rounding needed, figure one more digit to ensure correct result
            if round {
                ndigits += 1;
            }
            ndigits
        };

        // The working dividend normally requires res_ndigits + var2_ndigits
        // digits, but make it at least var1_ndigits so we can load all of var1
        // into it.  (There will be an additional digit dividend[0] in the
        // dividend space, but for consistency with Knuth's notation we don't
        // count that in div_ndigits.)
        let div_ndigits = {
            let ndigits = res_ndigits + var2_ndigits;
            ndigits.max(var1_ndigits)
        };

        // We need a workspace with room for the working dividend (div_ndigits+1
        // digits) plus room for the possibly-normalized divisor (var2_ndigits
        // digits).  It is convenient also to have a zero at divisor[0] with the
        // actual divisor data in divisor[1 .. var2_ndigits].  Transferring the
        // digits into the workspace also allows us to realloc the result (which
        // might be the same as either input var) before we begin the main loop.
        // Note that we use palloc0 to ensure that divisor[0], dividend[0], and
        // any additional dividend positions beyond var1_ndigits, start out 0.
        let mut workspace = vec![0 as NumericDigit; (div_ndigits + var2_ndigits + 2) as usize];
        let (dividend, divisor) = workspace.split_at_mut(div_ndigits as usize + 1);
        dividend[1..=var1_ndigits as usize].copy_from_slice(self.digits());
        divisor[1..=var2_ndigits as usize].copy_from_slice(other.digits());

        // Now we can alloc the result to hold the generated quotient digits.
        let mut result = Self::with_ndigits(res_ndigits);
        let data = result.digits.to_mut();
        let res_digits = data.digits_mut(res_ndigits);

        if var2_ndigits == 1 {
            // If there's only a single divisor digit, we can use a fast path (cf.
            // Knuth section 4.3.1 exercise 16).
            let divisor1 = divisor[1] as i32;
            let mut carry = 0i32;
            for i in 0..res_ndigits as usize {
                carry = carry * NBASE + unsafe { *dividend.get_unchecked(i + 1) } as i32;
                let res_digit = unsafe { res_digits.get_unchecked_mut(i) };
                *res_digit = (carry / divisor1) as NumericDigit;
                carry %= divisor1;
            }
        } else {
            // The full multiple-place algorithm is taken from Knuth volume 2,
            // Algorithm 4.3.1D.
            //
            // We need the first divisor digit to be >= NBASE/2.  If it isn't,
            // make it so by scaling up both the divisor and dividend by the
            // factor "d".  (The reason for allocating dividend[0] above is to
            // leave room for possible carry here.)
            if divisor[1] < HALF_NBASE {
                let d = NBASE / (divisor[1] + 1) as i32;

                let mut carry = 0i32;
                for i in (1..=var2_ndigits as usize).rev() {
                    let div = unsafe { divisor.get_unchecked_mut(i) };
                    carry += *div as i32 * d;
                    *div = (carry % NBASE) as NumericDigit;
                    carry /= NBASE;
                }
                debug_assert_eq!(carry, 0);

                carry = 0;
                // at this point only var1_ndigits of dividend can be nonzero
                for i in (0..=var1_ndigits as usize).rev() {
                    let div = unsafe { dividend.get_unchecked_mut(i) };
                    carry += *div as i32 * d;
                    *div = (carry % NBASE) as NumericDigit;
                    carry /= NBASE;
                }
                debug_assert_eq!(carry, 0);
                debug_assert!(divisor[1] >= HALF_NBASE);
            }

            // First 2 divisor digits are used repeatedly in main loop
            let divisor1 = divisor[1];
            let divisor2 = divisor[2];

            // Begin the main loop.  Each iteration of this loop produces the j'th
            // quotient digit by dividing dividend[j .. j + var2ndigits] by the
            // divisor; this is essentially the same as the common manual
            // procedure for long division.
            for (j, res_digit) in res_digits.iter_mut().enumerate() {
                // Estimate quotient digit from the first two dividend digits
                let next2digits = unsafe {
                    *dividend.get_unchecked(j) as i32 * NBASE
                        + *dividend.get_unchecked(j + 1) as i32
                };

                // If next2digits are 0, then quotient digit must be 0 and there's
                // no need to adjust the working dividend.  It's worth testing
                // here to fall out ASAP when processing trailing zeroes in a
                // dividend.
                if next2digits == 0 {
                    *res_digit = 0;
                    continue;
                }

                let mut qhat = if unsafe { *dividend.get_unchecked(j) } == divisor1 {
                    NBASE - 1
                } else {
                    next2digits / divisor1 as i32
                };

                // Adjust quotient digit if it's too large.  Knuth proves that
                // after this step, the quotient digit will be either correct or
                // just one too large.  (Note: it's OK to use dividend[j+2] here
                // because we know the divisor length is at least 2.)
                while divisor2 as i32 * qhat
                    > (next2digits - qhat * divisor1 as i32) * NBASE
                        + unsafe { *dividend.get_unchecked(j + 2) } as i32
                {
                    qhat -= 1;
                }

                // As above, need do nothing more when quotient digit is 0
                if qhat > 0 {
                    // Multiply the divisor by qhat, and subtract that from the
                    // working dividend.  "carry" tracks the multiplication,
                    // "borrow" the subtraction (could we fold these together?)
                    let mut carry = 0;
                    let mut borrow = 0;
                    for i in (0..=var2_ndigits as usize).rev() {
                        carry += unsafe { *divisor.get_unchecked(i) } as i32 * qhat;
                        borrow -= carry % NBASE;
                        carry /= NBASE;
                        let div = unsafe { dividend.get_unchecked_mut(j + i) };
                        borrow += *div as i32;
                        if borrow < 0 {
                            *div = (borrow + NBASE) as NumericDigit;
                            borrow = -1;
                        } else {
                            *div = borrow as NumericDigit;
                            borrow = 0;
                        }
                    }
                    debug_assert_eq!(carry, 0);

                    // If we got a borrow out of the top dividend digit, then
                    // indeed qhat was one too large.  Fix it, and add back the
                    // divisor to correct the working dividend.  (Knuth proves
                    // that this will occur only about 3/NBASE of the time; hence,
                    // it's a good idea to test this code with small NBASE to be
                    // sure this section gets exercised.)
                    if borrow != 0 {
                        qhat -= 1;
                        carry = 0;
                        for i in (0..=var2_ndigits as usize).rev() {
                            let div = unsafe { dividend.get_unchecked_mut(j + i) };
                            carry += *div as i32 + unsafe { *divisor.get_unchecked(i) } as i32;
                            if carry >= NBASE {
                                *div = (carry - NBASE) as NumericDigit;
                                carry = 1;
                            } else {
                                *div = carry as NumericDigit;
                                carry = 0;
                            }
                        }
                        // A carry should occur here to cancel the borrow above
                        debug_assert_eq!(carry, 1);
                    }
                }

                // And we're done with this quotient digit
                *res_digit = qhat as NumericDigit;
            }
        }

        // Finally, round or truncate the result to the requested precision.

        result.weight = res_weight;
        result.sign = res_sign;

        // Round or truncate to target rscale (and set result->dscale)
        if round {
            result.round_common(rscale);
        } else {
            result.trunc_common(rscale);
        }

        // Strip leading and trailing zeroes
        result.strip();

        Some(result)
    }

    /// This has the same API as `div_common()`, but is implemented using the division
    /// algorithm from the "FM" library, rather than Knuth's schoolbook-division
    /// approach.  This is significantly faster but can produce inaccurate
    /// results, because it sometimes has to propagate rounding to the left,
    /// and so we can never be entirely sure that we know the requested digits
    /// exactly.  We compute DIV_GUARD_DIGITS extra digits, but there is
    /// no certainty that that's enough.  We use this only in the transcendental
    /// function calculation routines, where everything is approximate anyway.
    ///
    /// Although we provide a "round" argument for consistency with `div()`,
    /// it is unwise to use this function with round=false.  In truncation mode
    /// it is possible to get a result with no significant digits, for example
    /// with rscale=0 we might compute 0.99999... and truncate that to 0 when
    /// the correct answer is 1.
    ///
    /// Returns `None` if `other == 0`.
    #[allow(clippy::cognitive_complexity)]
    pub fn div_fast_common(&self, other: &Self, rscale: i32, round: bool) -> Option<Self> {
        debug_assert!(!self.is_nan());
        debug_assert!(!other.is_nan());

        // copy these values into local vars for speed in inner loop
        let var1_ndigits = self.ndigits;
        let var1_digits = self.digits();
        let var2_ndigits = other.ndigits;
        let var2_digits = other.digits();

        // First of all division by zero check; we must not be handed an
        // unnormalized divisor.
        if var2_ndigits == 0 || var2_digits[0] == 0 {
            return None;
        }

        // Now result zero check
        if var1_ndigits == 0 {
            return Some(Self::zero_scaled(rscale));
        }

        // Determine the result sign, weight and number of digits to calculate
        let res_sign = if self.sign == other.sign {
            NUMERIC_POS
        } else {
            NUMERIC_NEG
        };
        let res_weight = self.weight - other.weight + 1;
        let div_ndigits = {
            // The number of accurate result digits we need to produce
            let mut ndigits = res_weight + 1 + (rscale + DEC_DIGITS - 1) / DEC_DIGITS;
            // Add guard digits for roundoff error
            ndigits += DIV_GUARD_DIGITS;
            if ndigits < DIV_GUARD_DIGITS {
                ndigits = DIV_GUARD_DIGITS;
            }
            // Must be at least var1_ndigits, too, to simplify data-loading loop
            if ndigits < var1_ndigits {
                ndigits = var1_ndigits;
            }
            ndigits
        };

        // We do the arithmetic in an array "div[]" of signed int32's.  Since
        // INT32_MAX is noticeably larger than NBASE*NBASE, this gives us headroom
        // to avoid normalizing carries immediately.
        //
        // We start with div[] containing one zero digit followed by the
        // dividend's digits (plus appended zeroes to reach the desired precision
        // including guard digits).  Each step of the main loop computes an
        // (approximate) quotient digit and stores it into div[], removing one
        // position of dividend space.  A final pass of carry propagation takes
        // care of any mistaken quotient digits.
        let mut div = vec![0i32; div_ndigits as usize + 1];
        for i in 0..var1_ndigits as usize {
            let d = unsafe { div.get_unchecked_mut(i + 1) };
            *d = unsafe { *var1_digits.get_unchecked(i) } as i32;
        }

        // We estimate each quotient digit using floating-point arithmetic, taking
        // the first four digits of the (current) dividend and divisor.  This must
        // be float to avoid overflow.  The quotient digits will generally be off
        // by no more than one from the exact answer.
        let mut fdivisor = var2_digits[0] as f64;
        for i in 1..4 {
            fdivisor *= NBASE as f64;
            if i < var2_ndigits {
                fdivisor += unsafe { *var2_digits.get_unchecked(i as usize) } as f64;
            }
        }
        let fdivisor_inverse = 1.0 / fdivisor;

        // max_div tracks the maximum possible absolute value of any div[] entry;
        // when this threatens to exceed INT_MAX, we take the time to propagate
        // carries.  Furthermore, we need to ensure that overflow doesn't occur
        // during the carry propagation passes either.  The carry values may have
        // an absolute value as high as INT_MAX/NBASE + 1, so really we must
        // normalize when digits threaten to exceed INT_MAX - INT_MAX/NBASE - 1.
        //
        // To avoid overflow in max_div itself, it represents the max absolute
        // value divided by NBASE-1, ie, at the top of the loop it is known that
        // no div[] entry has an absolute value exceeding max_div * (NBASE-1).
        //
        // Actually, though, that holds good only for div[] entries after div[qi];
        // the adjustment done at the bottom of the loop may cause div[qi + 1] to
        // exceed the max_div limit, so that div[qi] in the next iteration is
        // beyond the limit.  This does not cause problems, as explained below.
        let mut max_div = 1;

        // Outer loop computes next quotient digit, which will go into div[qi]
        for qi in 0..div_ndigits as usize {
            // Approximate the current dividend value
            let mut fdividend = unsafe { *div.get_unchecked(qi) } as f64;
            for i in 1..4usize {
                fdividend *= NBASE as f64;
                if (qi + i) as i32 <= div_ndigits {
                    fdividend += unsafe { *div.get_unchecked(qi + i) } as f64;
                }
            }
            // Compute the (approximate) quotient digit
            let mut fquotient = fdividend * fdivisor_inverse;
            let mut qdigit = if fquotient >= 0.0 {
                fquotient as i32
            } else {
                // truncate towards -infinity
                fquotient as i32 - 1
            };

            if qdigit != 0 {
                // Do we need to normalize now?
                max_div += qdigit.abs();
                if max_div > (i32::max_value() - i32::max_value() / NBASE - 1) / (NBASE - 1) {
                    // Yes, do it
                    let mut carry = 0;
                    let mut new_dig;
                    for i in (qi + 1..=div_ndigits as usize).rev() {
                        let div_i = unsafe { div.get_unchecked_mut(i) };
                        new_dig = *div_i + carry;
                        if new_dig < 0 {
                            carry = -((-new_dig - 1) / NBASE) - 1;
                            new_dig -= carry * NBASE;
                        } else if new_dig >= NBASE {
                            carry = new_dig / NBASE;
                            new_dig -= carry * NBASE;
                        } else {
                            carry = 0;
                        }
                        *div_i = new_dig;
                    }
                    let div_qi = unsafe { div.get_unchecked_mut(qi) };
                    new_dig = *div_qi + carry;
                    *div_qi = new_dig;

                    // All the div[] digits except possibly div[qi] are now in the
                    // range 0..NBASE-1.  We do not need to consider div[qi] in
                    // the max_div value anymore, so we can reset max_div to 1.
                    max_div = 1;

                    // Recompute the quotient digit since new info may have
                    // propagated into the top four dividend digits
                    fdividend = *div_qi as f64;
                    for i in 1..4usize {
                        fdividend *= NBASE as f64;
                        if (qi + i) as i32 <= div_ndigits {
                            fdividend += unsafe { *div.get_unchecked(qi + i) } as f64;
                        }
                    }
                    // Compute the (approximate) quotient digit
                    fquotient = fdividend * fdivisor_inverse;
                    qdigit = if fquotient >= 0.0 {
                        fquotient as i32
                    } else {
                        // truncate towards -infinity
                        fquotient as i32 - 1
                    };
                    max_div += qdigit.abs();
                }

                // Subtract off the appropriate multiple of the divisor.
                //
                // The digits beyond div[qi] cannot overflow, because we know they
                // will fall within the max_div limit.  As for div[qi] itself, note
                // that qdigit is approximately trunc(div[qi] / vardigits[0]),
                // which would make the new value simply div[qi] mod vardigits[0].
                // The lower-order terms in qdigit can change this result by not
                // more than about twice INT_MAX/NBASE, so overflow is impossible.
                if qdigit != 0 {
                    let istop = var2_ndigits.min(div_ndigits - qi as i32 + 1);
                    for i in 0..istop as usize {
                        let div_qi_i = unsafe { div.get_unchecked_mut(qi + i) };
                        *div_qi_i -= qdigit * unsafe { *var2_digits.get_unchecked(i) } as i32;
                    }
                }
            }

            // The dividend digit we are about to replace might still be nonzero.
            // Fold it into the next digit position.
            //
            // There is no risk of overflow here, although proving that requires
            // some care.  Much as with the argument for div[qi] not overflowing,
            // if we consider the first two terms in the numerator and denominator
            // of qdigit, we can see that the final value of div[qi + 1] will be
            // approximately a remainder mod (vardigits[0]*NBASE + vardigits[1]).
            // Accounting for the lower-order terms is a bit complicated but ends
            // up adding not much more than INT_MAX/NBASE to the possible range.
            // Thus, div[qi + 1] cannot overflow here, and in its role as div[qi]
            // in the next loop iteration, it can't be large enough to cause
            // overflow in the carry propagation step (if any), either.
            //
            // But having said that: div[qi] can be more than INT_MAX/NBASE, as
            // noted above, which means that the product div[qi] * NBASE *can*
            // overflow.  When that happens, adding it to div[qi + 1] will always
            // cause a canceling overflow so that the end result is correct.  We
            // could avoid the intermediate overflow by doing the multiplication
            // and addition in int64 arithmetic, but so far there appears no need.
            let div_qi = unsafe { *div.get_unchecked(qi) };
            let div_qi_1 = unsafe { div.get_unchecked_mut(qi + 1) };
            *div_qi_1 += div_qi * NBASE;

            let div_qi = unsafe { div.get_unchecked_mut(qi) };
            *div_qi = qdigit;
        }

        // Approximate and store the last quotient digit (div[div_ndigits])
        let mut fdividend = div[div_ndigits as usize] as f64;
        for _ in 1..4usize {
            fdividend *= NBASE as f64;
        }
        let fquotient = fdividend * fdivisor_inverse;
        let qdigit = if fquotient >= 0.0 {
            fquotient as i32
        } else {
            // truncate towards -infinity
            fquotient as i32 - 1
        };
        div[div_ndigits as usize] = qdigit;

        // Because the quotient digits might be off by one, some of them might be
        // -1 or NBASE at this point.  The represented value is correct in a
        // mathematical sense, but it doesn't look right.  We do a final carry
        // propagation pass to normalize the digits, which we combine with storing
        // the result digits into the output.  Note that this is still done at
        // full precision w/guard digits.
        let mut result = Self::with_ndigits(div_ndigits + 1);
        let data = result.digits.to_mut();
        let res_digits = data.digits_mut(result.ndigits);

        let mut carry = 0;
        for i in (0..=div_ndigits as usize).rev() {
            let mut new_dig = unsafe { *div.get_unchecked(i) } + carry;
            if new_dig < 0 {
                carry = -((-new_dig - 1) / NBASE) - 1;
                new_dig -= carry * NBASE;
            } else if new_dig >= NBASE {
                carry = new_dig / NBASE;
                new_dig -= carry * NBASE;
            } else {
                carry = 0;
            }
            let res_digit_i = unsafe { res_digits.get_unchecked_mut(i) };
            *res_digit_i = new_dig as NumericDigit;
        }
        debug_assert_eq!(carry, 0);

        // Finally, round the result to the requested precision.

        result.weight = res_weight;
        result.sign = res_sign;

        // Round to target rscale (and set result->dscale)
        if round {
            result.round_common(rscale);
        } else {
            result.trunc_common(rscale);
        }

        // Strip leading and trailing zeroes
        result.strip();

        Some(result)
    }

    /// Calculate the modulo of two numerics at variable level.
    #[inline]
    pub fn mod_common(&self, other: &Self) -> Option<Self> {
        debug_assert!(!self.is_nan());
        debug_assert!(!other.is_nan());

        // We do this using the equation
        // mod(x,y) = x - trunc(x/y)*y
        // div() can be persuaded to give us trunc(x/y) directly.
        let mut result = self.div_common(other, 0, false)?;
        result = result.mul_common(other, other.dscale);
        result = self.sub_common(&result);

        Some(result)
    }

    /// Compare two values on variable level.
    /// We assume zeroes have been truncated to no digits.
    #[inline]
    pub fn cmp_common(&self, other: &Self) -> i32 {
        debug_assert!(!self.is_nan());
        debug_assert!(!other.is_nan());

        if self.ndigits == 0 {
            if other.ndigits == 0 {
                0
            } else if other.is_negative() {
                1
            } else {
                -1
            }
        } else if other.ndigits == 0 {
            if self.is_positive() {
                1
            } else {
                -1
            }
        } else if self.is_positive() {
            if other.is_negative() {
                1
            } else {
                self.cmp_abs(other)
            }
        } else if other.is_positive() {
            -1
        } else {
            other.cmp_abs(self)
        }
    }

    /// Compute the square root of x using Newton's algorithm.
    pub fn sqrt_common(&self, rscale: i32) -> Self {
        debug_assert!(self.is_positive());

        let local_rscale = rscale + 8;

        if self.ndigits == 0 {
            return Self::zero_scaled(rscale);
        }

        // Initialize the result to the first guess
        let mut result = Self::with_ndigits(1);
        let data = result.digits.to_mut();
        data.digits_mut(1)[0] = {
            let i = self.digits[0] / 2;
            if i == 0 {
                1
            } else {
                i
            }
        };
        result.weight = self.weight / 2;

        let mut last_val = result.clone();

        loop {
            let val = self
                .div_fast_common(&result, local_rscale, true)
                .expect("should not be zero");
            result = result.add_common(&val);
            result = result.mul_common(&ZERO_POINT_FIVE, local_rscale);

            if result.cmp_common(&last_val) == 0 {
                break;
            }

            last_val = result.clone();
        }

        // Round to requested precision
        result.round_common(rscale);

        result
    }

    /// Raise `self` to the power of exp, where exp is an integer.
    ///
    /// Returns `None` if overflows.
    ///
    /// # Panics
    /// Panics if self is zero and exp is less than zero.
    pub fn power_int(&self, exp: i32, rscale: i32) -> Option<Self> {
        debug_assert!(!self.is_nan());

        // Handle some common special cases, as well as corner cases
        match exp {
            0 => {
                // While 0 ^ 0 can be either 1 or indeterminate (error), we treat
                // it as 1 because most programming languages do this. SQL:2003
                // also requires a return value of 1.
                // https://en.wikipedia.org/wiki/Exponentiation#Zero_to_the_zero_power
                let mut result = ONE.clone();
                result.dscale = rscale; // no need to round
                return Some(result);
            }
            1 => {
                let mut result = self.clone();
                result.round_common(rscale);
                return Some(result);
            }
            -1 => {
                let result = ONE
                    .div_common(self, rscale, true)
                    .expect(DIVIDE_BY_ZERO_MSG);
                return Some(result);
            }
            2 => {
                let result = self.mul_common(self, rscale);
                return Some(result);
            }
            _ => (),
        }

        // Handle the special case where the base is zero
        if self.ndigits == 0 {
            assert!(exp >= 0, DIVIDE_BY_ZERO_MSG);
            return Some(Self::zero_scaled(rscale));
        }

        // The general case repeatedly multiplies base according to the bit
        // pattern of exp.
        //
        // First we need to estimate the weight of the result so that we know how
        // many significant digits are needed.
        let digits = self.digits();
        let mut f = digits[0] as f64;
        let mut p = self.weight * DEC_DIGITS;

        for (i, &digit) in digits.iter().enumerate().skip(1) {
            if (i * DEC_DIGITS as usize) < 16 {
                break;
            }

            f = f * NBASE as f64 + digit as f64;
            p -= DEC_DIGITS;
        }

        // We have base ~= f * 10^p
        // so log10(result) = log10(base^exp) ~= exp * (log10(f) + p)
        f = exp as f64 * (f.log10() + p as f64);

        // Apply crude overflow/underflow tests so we can exit early if the result
        // certainly will overflow/underflow.
        if f > 3.0 * i16::max_value() as f64 * DEC_DIGITS as f64 {
            return None;
        }

        if f + 1.0 < (-rscale) as f64 || f + 1.0 < (-NUMERIC_MAX_DISPLAY_SCALE) as f64 {
            return Some(Self::zero_scaled(rscale));
        }

        // Approximate number of significant digits in the result.  Note that the
        // underflow test above means that this is necessarily >= 0.
        let mut sig_digits = 1 + rscale + f as i32;

        // The multiplications to produce the result may introduce an error of up
        // to around log10(abs(exp)) digits, so work with this many extra digits
        // of precision (plus a few more for good measure).
        sig_digits += (exp.abs() as f64).ln() as i32 + 8;

        // Now we can proceed with the multiplications.
        let mut neg = exp < 0;
        let mut mask = exp.abs();

        let mut base_prod = self.clone();

        let mut result = if mask & 1 != 0 {
            self.clone()
        } else {
            ONE.clone()
        };

        loop {
            mask >>= 1;
            if mask <= 0 {
                break;
            }

            // Do the multiplications using rscales large enough to hold the
            // results to the required number of significant digits, but don't
            // waste time by exceeding the scales of the numbers themselves.
            let local_rscale = (sig_digits - 2 * base_prod.weight * DEC_DIGITS)
                .min(2 * base_prod.dscale)
                .max(NUMERIC_MIN_DISPLAY_SCALE);

            base_prod = base_prod.mul_common(&base_prod, local_rscale);

            if mask & 1 != 0 {
                let local_rscale = (sig_digits - (base_prod.weight + result.weight) * DEC_DIGITS)
                    .min(base_prod.dscale + result.dscale)
                    .max(NUMERIC_MIN_DISPLAY_SCALE);

                result = base_prod.mul_common(&result, local_rscale);
            }

            // When abs(base) > 1, the number of digits to the left of the decimal
            // point in base_prod doubles at each iteration, so if exp is large we
            // could easily spend large amounts of time and memory space doing the
            // multiplications.  But once the weight exceeds what will fit in
            // int16, the final result is guaranteed to overflow (or underflow, if
            // exp < 0), so we can give up before wasting too many cycles.
            if base_prod.weight > i16::max_value() as i32 || result.weight > i16::max_value() as i32
            {
                // overflow, unless neg, in which case result should be 0
                if !neg {
                    return None;
                }
                result = ZERO.clone();
                neg = false;
                break;
            }
        }

        // Compensate for input sign, and round to requested rscale
        if neg {
            result = ONE
                .div_fast_common(&result, rscale, true)
                .expect(DIVIDE_BY_ZERO_MSG);
        } else {
            result.round_common(rscale);
        }

        Some(result)
    }

    /// Compute the natural log of `self`
    pub fn ln_common(&self, rscale: i32) -> Self {
        debug_assert!(!self.is_nan());
        debug_assert!(self.cmp_common(&ZERO) > 0);

        let mut x = self.clone();
        let mut fact = TWO.clone();

        // Reduce input into range 0.9 < x < 1.1 with repeated sqrt() operations.
        //
        // The final logarithm will have up to around rscale+6 significant digits.
        // Each sqrt() will roughly halve the weight of x, so adjust the local
        // rscale as we work so that we keep this many significant digits at each
        // step (plus a few more for good measure).
        while x.cmp_common(&ZERO_POINT_NINE) <= 0 {
            let mut local_rscale = rscale - x.weight * DEC_DIGITS / 2 + 8;
            local_rscale = local_rscale.max(NUMERIC_MIN_DISPLAY_SCALE);
            x = x.sqrt_common(local_rscale);
            fact = fact.mul_common(&TWO, 0);
        }
        while x.cmp_common(&ONE_POINT_ONE) >= 0 {
            let mut local_rscale = rscale - x.weight * DEC_DIGITS / 2 + 8;
            local_rscale = local_rscale.max(NUMERIC_MIN_DISPLAY_SCALE);
            x = x.sqrt_common(local_rscale);
            fact = fact.mul_common(&TWO, 0);
        }

        // We use the Taylor series for 0.5 * ln((1+z)/(1-z)),
        //
        // z + z^3/3 + z^5/5 + ...
        //
        // where z = (x-1)/(x+1) is in the range (approximately) -0.053 .. 0.048
        // due to the above range-reduction of x.
        //
        // The convergence of this is not as fast as one would like, but is
        // tolerable given that z is small.
        let local_rscale = rscale + 8;

        let mut result = x.sub_common(&ONE);
        let mut elem = x.add_common(&ONE);
        result = result
            .div_fast_common(&elem, local_rscale, true)
            .expect(DIVIDE_BY_ZERO_MSG);
        let mut xx = result.clone();
        x = result.mul_common(&result, local_rscale);

        let mut ni = ONE.clone();

        loop {
            ni = ni.add_common(&TWO);
            xx = xx.mul_common(&x, local_rscale);
            elem = xx
                .div_fast_common(&ni, local_rscale, true)
                .expect(DIVIDE_BY_ZERO_MSG);

            if elem.ndigits == 0 {
                break;
            }

            result = result.add_common(&elem);

            if elem.weight < (result.weight - local_rscale * 2 / DEC_DIGITS) {
                break;
            }
        }

        // Compensate for argument range reduction, round to requested rscale
        result = result.mul_common(&fact, rscale);

        result
    }

    /// Estimate the dweight of the most significant decimal digit of the natural
    /// logarithm of a number.
    ///
    /// Essentially, we're approximating `log10(abs(ln(self)))`.  This is used to
    /// determine the appropriate rscale when computing natural logarithms.
    pub fn estimate_ln_dweight(&self) -> i32 {
        debug_assert!(!self.is_nan());

        let ln_dweight: i32;

        if self.cmp_common(&ZERO_POINT_NINE) >= 0 && self.cmp_common(&ONE_POINT_ONE) <= 0 {
            // 0.9 <= self <= 1.1
            //
            // ln(self) has a negative weight (possibly very large).  To get a
            // reasonably accurate result, estimate it using ln(1+x) ~= x.
            let x = self.sub_common(&ONE);
            if x.ndigits > 0 {
                // Use weight of most significant decimal digit of x
                ln_dweight = x.weight * DEC_DIGITS + (x.digits()[0] as f64).log10() as i32;
            } else {
                // x = 0.  Since ln(1) = 0 exactly, we don't need extra digits
                ln_dweight = 0;
            }
        } else {
            // Estimate the logarithm using the first couple of digits from the
            // input number.  This will give an accurate result whenever the input
            // is not too close to 1.
            if self.ndigits > 0 {
                let d = self.digits();

                let mut digits = d[0] as i32;
                let mut dweight = self.weight * DEC_DIGITS;

                if self.ndigits > 1 {
                    digits = digits * NBASE + d[1] as i32;
                    dweight -= DEC_DIGITS;
                }

                // We have self ~= digits * 10^dweight
                // so ln(self) ~= ln(digits) + dweight * ln(10)
                let ln_var = (digits as f64).ln() + dweight as f64 * LN_10;
                ln_dweight = ln_var.abs().log10() as i32;
            } else {
                ln_dweight = 0;
            }
        }

        ln_dweight
    }

    /// Compute the logarithm of `self` in a given base.
    ///
    /// Note: this routine chooses dscale of the result.
    pub fn log_common(&self, base: &Self) -> Self {
        debug_assert!(!self.is_nan());
        debug_assert!(!base.is_nan());
        debug_assert!(self.cmp_common(&ZERO) > 0);

        // Estimated dweights of ln(base), ln(self) and the final result
        let ln_base_dweight = base.estimate_ln_dweight();
        let ln_num_dweight = self.estimate_ln_dweight();
        let result_dweight = ln_num_dweight - ln_base_dweight;

        // Select the scale of the result so that it will have at least
        // NUMERIC_MIN_SIG_DIGITS significant digits and is not less than either
        // input's display scale.
        let rscale = (NUMERIC_MIN_SIG_DIGITS - result_dweight)
            .max(base.dscale)
            .max(self.dscale)
            .max(NUMERIC_MIN_DISPLAY_SCALE)
            .min(NUMERIC_MAX_DISPLAY_SCALE);

        // Set the scales for ln(base) and ln(num) so that they each have more
        // significant digits than the final result.
        let ln_base_rscale =
            (rscale + result_dweight - ln_base_dweight + 8).max(NUMERIC_MIN_DISPLAY_SCALE);
        let ln_num_rscale =
            (rscale + result_dweight - ln_num_dweight + 8).max(NUMERIC_MIN_DISPLAY_SCALE);

        // Form natural logarithms
        let ln_base = base.ln_common(ln_base_rscale);
        let ln_num = self.ln_common(ln_num_rscale);

        // Divide and round to the required scale
        ln_num
            .div_fast_common(&ln_base, rscale, true)
            .expect(DIVIDE_BY_ZERO_MSG)
    }

    /// Raise e to the power of x, computed to rscale fractional digits.
    ///
    /// Returns `None` if overflows.
    pub fn exp_common(&self, rscale: i32) -> Option<Self> {
        debug_assert!(!self.is_nan());

        let mut x = self.clone();

        // Estimate the dweight of the result using floating point arithmetic, so
        // that we can choose an appropriate local rscale for the calculation.
        let mut val: f64 = TryFrom::try_from(&x).unwrap();

        // Guard against overflow
        // If you change this limit, see also power_common()'s limit
        if val.abs() >= NUMERIC_MAX_RESULT_SCALE as f64 * 3.0 {
            // value overflows numeric format
            return None;
        }

        // decimal weight = log10(e^x) = x * log10(e)
        let dweight = (val * LOG10_E) as i32;
        let mut ndiv2: i32;

        // Reduce x to the range -0.01 <= x <= 0.01 (approximately) by dividing by
        // 2^n, to improve the convergence rate of the Taylor series.
        if val.abs() > 0.01 {
            let mut tmp = TWO.clone();

            ndiv2 = 1;
            val /= 2.0;

            while val.abs() > 0.01 {
                ndiv2 += 1;
                val /= 2.0;
                tmp = tmp.add_common(&tmp);
            }

            let local_rscale = x.dscale + ndiv2;
            x = x
                .div_fast_common(&tmp, local_rscale, true)
                .expect(DIVIDE_BY_ZERO_MSG);
        } else {
            ndiv2 = 0;
        }

        // Set the scale for the Taylor series expansion.  The final result has
        // (dweight + rscale + 1) significant digits.  In addition, we have to
        // raise the Taylor series result to the power 2^ndiv2, which introduces
        // an error of up to around log10(2^ndiv2) digits, so work with this many
        // extra digits of precision (plus a few more for good measure).
        let mut sig_digits = 1 + dweight + rscale + (ndiv2 as f64 * LOG10_2) as i32;
        sig_digits = sig_digits.max(0) + 8;

        let local_rscale = sig_digits - 1;

        // Use the Taylor series
        //
        // exp(x) = 1 + x + x^2/2! + x^3/3! + ...
        //
        // Given the limited range of x, this should converge reasonably quickly.
        // We run the series until the terms fall below the local_rscale limit.
        let mut result = ONE.add_common(&x);

        let mut elem = x.mul_common(&x, local_rscale);
        let mut ni = TWO.clone();
        elem = elem
            .div_fast_common(&ni, local_rscale, true)
            .expect(DIVIDE_BY_ZERO_MSG);

        while elem.ndigits != 0 {
            result = result.add_common(&elem);

            elem = elem.mul_common(&x, local_rscale);
            ni = ni.add_common(&ONE);
            elem = elem
                .div_fast_common(&ni, local_rscale, true)
                .expect(DIVIDE_BY_ZERO_MSG);
        }

        // Compensate for the argument range reduction.  Since the weight of the
        // result doubles with each multiplication, we can reduce the local rscale
        // as we proceed.
        for _ in 1..=ndiv2 {
            let mut local_rscale = sig_digits - result.weight * 2 * DEC_DIGITS;
            local_rscale = local_rscale.max(NUMERIC_MIN_DISPLAY_SCALE);
            result = result.mul_common(&result, local_rscale);
        }

        // Round to requested rscale
        result.round_common(rscale);

        Some(result)
    }

    /// Raise `self` to the power of `exp`
    ///
    /// Returns `None` if overflows.
    ///
    /// Note: this routine chooses dscale of the result.
    ///
    /// # Panics
    /// Panics if self is zero and exp is less than zero.
    pub fn power_common(&self, exp: &Self) -> Option<Self> {
        debug_assert!(!self.is_nan());
        debug_assert!(!exp.is_nan());

        // If exp can be represented as an integer, use power_int()
        if exp.ndigits == 0 || exp.ndigits <= exp.weight + 1 {
            // exact integer, but does it fit in i32?
            if let Ok(exp_val) = TryInto::<i32>::try_into(exp) {
                // Okay, select rscale
                let rscale = NUMERIC_MIN_SIG_DIGITS
                    .max(self.dscale)
                    .max(NUMERIC_MIN_DISPLAY_SCALE)
                    .min(NUMERIC_MAX_DISPLAY_SCALE);

                let result = self.power_int(exp_val, rscale);
                return result;
            }
        }

        // This avoids log(0) for cases of 0 raised to a non-integer.  0 ^ 0 is
        // handled by power_int().
        if self.cmp_common(&ZERO) == 0 {
            return Some(Self::zero_scaled(NUMERIC_MIN_SIG_DIGITS));
        }

        // Decide on the scale for the ln() calculation.  For this we need an
        // estimate of the weight of the result, which we obtain by doing an
        // initial low-precision calculation of exp * ln(base).
        //
        // We want result = e ^ (exp * ln(base))
        // so result dweight = log10(result) = exp * ln(base) * log10(e)
        //
        // We also perform a crude overflow test here so that we can exit early if
        // the full-precision result is sure to overflow, and to guard against
        // integer overflow when determining the scale for the real calculation.
        // exp_common() supports inputs up to NUMERIC_MAX_RESULT_SCALE * 3, so the
        // result will overflow if exp * ln(base) >= NUMERIC_MAX_RESULT_SCALE * 3.
        // Since the values here are only approximations, we apply a small fuzz
        // factor to this overflow test and let exp_common() determine the exact
        // overflow threshold so that it is consistent for all inputs.
        let ln_dweight = self.estimate_ln_dweight();

        let local_rscale = (8 - ln_dweight)
            .max(NUMERIC_MIN_DISPLAY_SCALE)
            .min(NUMERIC_MAX_DISPLAY_SCALE);

        let mut ln_base = self.ln_common(local_rscale);
        let mut ln_num = ln_base.mul_common(exp, local_rscale);

        let mut val: f64 = TryFrom::try_from(&ln_num).unwrap();

        // initial overflow test with fuzz factor
        if val.abs() > NUMERIC_MAX_RESULT_SCALE as f64 * 3.01 {
            // value overflows numeric format
            return None;
        }

        val *= LOG10_E; // approximate decimal result weight

        // choose the result scale
        let rscale = (NUMERIC_MIN_SIG_DIGITS - val as i32)
            .max(self.dscale)
            .max(exp.dscale)
            .max(NUMERIC_MIN_DISPLAY_SCALE)
            .min(NUMERIC_MAX_DISPLAY_SCALE);

        // set the scale for the real exp * ln(base) calculation
        let local_rscale = (rscale + val as i32 - ln_dweight + 8).max(NUMERIC_MIN_DISPLAY_SCALE);

        // and do the real calculation
        ln_base = self.ln_common(local_rscale);
        ln_num = ln_base.mul_common(exp, local_rscale);
        ln_num.exp_common(rscale)
    }

    /// Convert `self` to text representation.
    /// `self` is displayed to the number of digits indicated by its dscale.
    pub fn write<W: fmt::Write>(&self, f: &mut W) -> Result<(), fmt::Error> {
        if self.is_nan() {
            return write!(f, "NaN");
        }

        // Output a dash for negative values.
        if self.sign == NUMERIC_NEG {
            write!(f, "-")?;
        }

        // Output all digits before the decimal point.
        if self.weight < 0 {
            write!(f, "0")?;
        } else {
            let digits = self.digits();
            debug_assert_eq!(digits.len(), self.ndigits as usize);

            for d in 0..=self.weight {
                let dig = if d < self.ndigits {
                    digits[d as usize]
                } else {
                    0
                };

                debug_assert!(dig >= 0);

                // In the first digit, suppress extra leading decimal zeroes.
                if d > 0 {
                    write!(f, "{:>0width$}", dig, width = DEC_DIGITS as usize)?;
                } else {
                    write!(f, "{}", dig)?;
                }
            }
        }

        // If requested, output a decimal point and all the digits that follow it.
        if self.dscale > 0 {
            write!(f, ".")?;

            let digits = self.digits();
            debug_assert_eq!(digits.len(), self.ndigits as usize);

            let mut d = self.weight + 1;

            for scale in (0..self.dscale).step_by(DEC_DIGITS as usize) {
                let dig = if d >= 0 && d < self.ndigits {
                    digits[d as usize]
                } else {
                    0
                };

                if scale + DEC_DIGITS <= self.dscale {
                    write!(f, "{:>0width$}", dig, width = DEC_DIGITS as usize)?;
                } else {
                    // truncate the last digit
                    let width = (self.dscale - scale) as usize;
                    let dig = (0..DEC_DIGITS as usize - width).fold(dig, |acc, _| acc / 10);
                    write!(f, "{:>0width$}", dig, width = width)?;
                }

                d += 1;
            }
        }

        Ok(())
    }

    /// Convert `self` to a normalised scientific notation text representation.
    ///
    /// This notation has the general form a * 10^b, where a is known as the
    /// "significand" and b is known as the "exponent".
    ///
    /// Because we can't do superscript in ASCII (and because we want to copy
    /// printf's behaviour) we display the exponent using E notation, with a
    /// minimum of two exponent digits.
    ///
    /// For example, the value 1234 could be output as 1.2e+03.
    ///
    /// We assume that the exponent can fit into an int32.
    ///
    /// `rscale` is the number of decimal digits desired after the decimal point in
    /// the output, negative values will be treated as meaning zero.
    ///
    /// `lower_exp` indicates use 'e' if true or else use 'E'.
    pub fn write_sci<W: fmt::Write>(
        &self,
        f: &mut W,
        rscale: i32,
        lower_exp: bool,
    ) -> Result<(), fmt::Error> {
        if self.is_nan() {
            return write!(f, "NaN");
        }

        let rscale = if rscale < 0 { 0 } else { rscale };

        // Determine the exponent of this number in normalised form.
        //
        // This is the exponent required to represent the number with only one
        // significant digit before the decimal place.
        let exponent = if self.ndigits > 0 {
            let mut exp = (self.weight + 1) * DEC_DIGITS;
            // Compensate for leading decimal zeroes in the first numeric digit by
            // decrementing the exponent.
            exp -= DEC_DIGITS - (self.digits[0] as f64).log10() as i32;
            exp
        } else {
            // If has no digits, then it must be zero.
            //
            // Zero doesn't technically have a meaningful exponent in normalised
            // notation, but we just display the exponent as zero for consistency
            // of output.
            0
        };

        // The denominator is set to 10 raised to the power of the exponent.
        //
        // We then divide var by the denominator to get the significand, rounding
        // to rscale decimal digits in the process.
        let denom_scale = if exponent < 0 { -exponent } else { 0 };

        let denominator = TEN
            .power_int(exponent, denom_scale)
            .expect("attempt to multiply with overflow");
        let significand = self
            .div_common(&denominator, rscale, true)
            .expect(DIVIDE_BY_ZERO_MSG);

        if lower_exp {
            write!(f, "{}e{:<+03}", significand, exponent)
        } else {
            write!(f, "{}E{:<+03}", significand, exponent)
        }
    }

    /// Returns the appropriate result scale for scientific notation representation.
    pub fn select_sci_scale(&self) -> i32 {
        // 1 => (1, 0)
        // 10 => (1, 1)
        // 11 => (2, 0)
        // 100 => (1, 2)
        // 101 => (3, 0)
        // 1010 => (3, 1)
        fn count_zeros(digit: NumericDigit) -> (i32, i32) {
            let mut val = digit;
            let mut n = 0;
            let mut zero = 0;

            for _ in 0..DEC_DIGITS {
                let d = val % 10;
                val /= 10;

                if d == 0 && n == 0 {
                    // all previous d are zeros.
                    zero += 1;
                } else {
                    n += 1;
                }

                if val == 0 {
                    break;
                }
            }

            (n, zero)
        }

        let digits = self.digits();

        // find first non-zero digit from front to end
        let (i, digit) = match digits.iter().enumerate().find(|(_, &d)| d != 0) {
            Some((i, &digit)) => (i, digit),
            None => {
                // all digits are 0
                return 0;
            }
        };

        // find first non-zero digit from end to front
        let (ri, rdigit) = match digits.iter().enumerate().rfind(|(_, &d)| d != 0) {
            Some((ri, &rdigit)) => (ri, rdigit),
            None => {
                // all digits are 0, actually unreachable!
                return 0;
            }
        };

        debug_assert!(i <= ri);

        if i == ri {
            // only one digit
            let (n, _) = count_zeros(digit);
            return n - 1;
        }

        let (n, zero) = count_zeros(digit);
        let (_, rzero) = count_zeros(rdigit);

        let front = n + zero;
        let end = DEC_DIGITS - rzero;

        front + end + (ri - i - 1) as i32 * DEC_DIGITS - 1
    }

    /// Make `self` to be a result numeric.
    /// We assume that `self` is not overflowed.
    #[inline]
    pub fn make_result_no_overflow(mut self) -> NumericBuf {
        debug_assert!(!self.is_nan());
        debug_assert!(
            self.weight <= NUMERIC_WEIGHT_MAX as i32
                || self.weight >= NUMERIC_WEIGHT_MIN as i32
                || self.dscale <= NUMERIC_DSCALE_MAX as i32
                || self.dscale >= 0
        );

        self.strip();

        self.into_numeric_buf()
    }

    /// Make `self` to be a result numeric.
    /// Returns `None` if overflows.
    #[inline]
    pub fn make_result(self) -> Option<NumericBuf> {
        debug_assert!(!self.is_nan());
        debug_assert!(self.dscale >= 0);

        if self.weight > NUMERIC_WEIGHT_MAX as i32
            || self.weight < NUMERIC_WEIGHT_MIN as i32
            || self.dscale > NUMERIC_DSCALE_MAX as i32
        {
            return None;
        }

        Some(self.make_result_no_overflow())
    }

    /// Negate this value.
    #[inline]
    pub fn negate(&mut self) {
        debug_assert!(!self.is_nan());

        if self.ndigits > 0 {
            if self.is_positive() {
                self.sign = NUMERIC_NEG;
            } else if self.is_negative() {
                self.sign = NUMERIC_POS;
            }
        }
    }

    /// Returns a numeric that represents the sign of self.
    /// * -1 if `self` is less than 0
    /// * 0 if `self` is equal to 0
    /// * 1 if `self` is greater than zero
    /// * `NaN` if `self` is `NaN`
    #[inline]
    pub fn signum(&self) -> Self {
        debug_assert!(!self.is_nan());

        if self.ndigits == 0 {
            ZERO.clone()
        } else {
            let mut result = ONE.clone();
            result.sign = self.sign;
            result
        }
    }

    /// Increment `self` by one.
    #[inline]
    pub fn inc(&self) -> Self {
        debug_assert!(!self.is_nan());

        // Compute the result and return it
        self.add_common(&ONE)
    }

    /// Checked numeric division.
    /// Computes `self / other`, returning `None` if `other == 0`.
    #[inline]
    pub fn checked_div(&self, other: &Self) -> Option<Self> {
        debug_assert!(!self.is_nan());
        debug_assert!(!other.is_nan());

        // Select scale for division result
        let rscale = self.select_div_scale(&other);

        self.div_common(&other, rscale, true)
    }

    /// Computes `self / other`, truncating the result to an integer.
    ///
    /// Returns `None` if `other == 0`.
    #[inline]
    pub fn checked_div_trunc(&self, other: &Self) -> Option<Self> {
        debug_assert!(!self.is_nan());
        debug_assert!(!other.is_nan());

        self.div_common(&other, 0, false)
    }

    /// Round a value to have `scale` digits after the decimal point.
    /// We allow negative `scale`, implying rounding before the decimal
    /// point --- Oracle interprets rounding that way.
    #[inline]
    pub fn round(&mut self, scale: i32) {
        debug_assert!(!self.is_nan());

        // Limit the scale value to avoid possible overflow in calculations
        let rscale = scale
            .max(-NUMERIC_MAX_DISPLAY_SCALE)
            .min(NUMERIC_MAX_DISPLAY_SCALE);

        self.round_common(rscale);

        // We don't allow negative output dscale
        if rscale < 0 {
            self.dscale = 0;
        }
    }

    /// Truncate a value to have `scale` digits after the decimal point.
    /// We allow negative `scale`, implying a truncation before the decimal
    /// point --- Oracle interprets truncation that way.
    #[inline]
    pub fn trunc(&mut self, scale: i32) {
        debug_assert!(!self.is_nan());

        // Limit the scale value to avoid possible overflow in calculations
        let rscale = scale
            .max(-NUMERIC_MAX_DISPLAY_SCALE)
            .min(NUMERIC_MAX_DISPLAY_SCALE);

        self.trunc_common(rscale);

        // We don't allow negative output dscale
        if rscale < 0 {
            self.dscale = 0;
        }
    }

    /// Return the smallest integer greater than or equal to the argument.
    #[inline]
    pub fn ceil(&self) -> Self {
        debug_assert!(!self.is_nan());
        self.ceil_common()
    }

    /// Return the largest integer equal to or less than the argument.
    #[inline]
    pub fn floor(&self) -> Self {
        debug_assert!(!self.is_nan());
        self.floor_common()
    }

    /// Compute the absolute value of `self`.
    #[inline]
    pub fn abs(&mut self) {
        debug_assert!(!self.is_nan());

        if self.is_negative() {
            self.sign = NUMERIC_POS;
        }
    }

    /// Compute the square root of a numeric.
    #[inline]
    pub fn sqrt(&self) -> Self {
        debug_assert!(!self.is_negative());
        debug_assert!(!self.is_nan());

        // Determine the result scale.
        // We choose a scale to give at least NUMERIC_MIN_SIG_DIGITS significant digits;
        // but in any case not less than the input's dscale.

        // Assume the input was normalized, so arg.weight is accurate
        let sweight = (self.weight + 1) * DEC_DIGITS / 2 - 1;

        let rscale = (NUMERIC_MIN_SIG_DIGITS - sweight)
            .max(self.dscale)
            .max(NUMERIC_MIN_DISPLAY_SCALE)
            .min(NUMERIC_MAX_DISPLAY_SCALE);

        self.sqrt_common(rscale)
    }

    /// Compute the natural logarithm of `self`.
    ///
    /// # Panics
    /// Panics if `self <= 0`.
    #[inline]
    pub fn ln(&self) -> Self {
        debug_assert!(!self.is_nan());

        let cmp = self.cmp_common(&ZERO);
        assert_ne!(cmp, 0, "cannot take logarithm of zero");
        assert!(cmp > 0, "cannot take logarithm of a negative number");

        // Estimated dweight of logarithm
        let ln_dweight = self.estimate_ln_dweight();

        let rscale = (NUMERIC_MIN_SIG_DIGITS - ln_dweight)
            .max(self.dscale)
            .max(NUMERIC_MIN_DISPLAY_SCALE)
            .min(NUMERIC_MAX_DISPLAY_SCALE);

        self.ln_common(rscale)
    }

    /// Compute the logarithm of `self` in a given base.
    ///
    /// # Panics
    /// Panics if `self <= 0` or `base <= 0`.
    #[inline]
    pub fn log(&self, base: &Self) -> Self {
        debug_assert!(!self.is_nan());
        debug_assert!(!base.is_nan());

        let cmp = self.cmp_common(&ZERO);
        assert_ne!(cmp, 0, "cannot take logarithm of zero");
        assert!(cmp > 0, "cannot take logarithm of a negative number");

        let cmp = base.cmp_common(&ZERO);
        assert_ne!(cmp, 0, "cannot take logarithm of zero");
        assert!(cmp > 0, "cannot take logarithm of a negative number");

        //  Call log_common() to compute and return the result;
        //	note it handles scale selection itself.
        self.log_common(&base)
    }

    /// Compute the base 2 logarithm of `self`.
    ///
    /// # Panics
    /// Panics if `self <= 0`.
    #[inline]
    pub fn log2(&self) -> Self {
        self.log(&TWO)
    }

    /// Compute the base 10 logarithm of `self`.
    ///
    /// # Panics
    /// Panics if `self <= 0`.
    #[inline]
    pub fn log10(&self) -> Self {
        self.log(&TEN)
    }

    /// Raise e to the power of `self` (`e^(self)`).
    ///
    /// Returns `None` if overflows.
    ///
    #[inline]
    pub fn exp(&self) -> Option<Self> {
        debug_assert!(!self.is_nan());

        // Determine the result scale.  We choose a scale
        // to give at least NUMERIC_MIN_SIG_DIGITS significant digits;
        // but in any case not less than the input's dscale.

        let mut val: f64 = TryFrom::try_from(self).unwrap();

        // log10(result) = num * log10(e), so this is approximately the decimal
        // weight of the result:
        val *= LOG10_E;

        // limit to something that won't cause integer overflow
        val = val
            .max(-NUMERIC_MAX_RESULT_SCALE as f64)
            .min(NUMERIC_MAX_RESULT_SCALE as f64);

        let rscale = (NUMERIC_MIN_SIG_DIGITS - val as i32)
            .max(self.dscale)
            .max(NUMERIC_MIN_DISPLAY_SCALE)
            .min(NUMERIC_MAX_DISPLAY_SCALE);

        // Let exp_common() do the calculation and return the result.
        self.exp_common(rscale)
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
    pub fn pow(&self, exp: &Self) -> Option<Self> {
        // Handle NaN cases.  We follow the POSIX spec for pow(3), which says that
        // NaN ^ 0 = 1, and 1 ^ NaN = 1, while all other cases with NaN inputs
        // yield NaN (with no error).
        if self.is_nan() {
            if !exp.is_nan() && exp.cmp_common(&ZERO) == 0 {
                return Some(ONE.clone());
            }
            return Some(Self::nan());
        } else if exp.is_nan() {
            if self.cmp_common(&ONE) == 0 {
                return Some(ONE.clone());
            }
            return Some(Self::nan());
        }

        if self.cmp_common(&ZERO) == 0 && exp.cmp_common(&ZERO) < 0 {
            panic!("zero raised to a negative power is undefined")
        }

        let mut exp_trunc = exp.clone();
        exp_trunc.trunc_common(0);

        if self.cmp_common(&ZERO) < 0 && exp.cmp_common(&exp_trunc) != 0 {
            panic!("a negative number raised to a non-integer power yields a complex result")
        }

        // Call power_common() to compute and return the result; note it handles
        // scale selection itself.
        self.power_common(&exp)
    }

    /// Do bounds checking and rounding according to `typmod`.
    ///
    /// Returns true if overflows.
    ///
    /// Notes that no matter whether overflows, `self` will be rounded.
    pub fn apply_typmod(&mut self, typmod: Typmod) -> bool {
        // Do nothing if we have a default typmod (-1)
        if typmod.value() < VAR_HEADER_SIZE {
            return false;
        }

        let (precision, scale) = typmod.extract();
        let max_digits = precision - scale;

        // Round to target scale (and set self.dscale)
        self.round_common(scale);

        // Check for overflow - note we can't do this before rounding, because
        // rounding could raise the weight.  Also note that the self's weight could
        // be inflated by leading zeroes, which will be stripped before storage
        // but perhaps might not have been yet. In any case, we must recognize a
        // true zero, whose weight doesn't mean anything.
        let mut ddigits = (self.weight + 1) * DEC_DIGITS;
        if ddigits > max_digits {
            // Determine true weight; and check for all-zero result
            for &dig in self.digits().iter() {
                if dig != 0 {
                    // Adjust for any high-order decimal zero digits
                    debug_assert_eq!(DEC_DIGITS, 4);
                    if dig < 10 {
                        ddigits -= 3;
                    } else if dig < 100 {
                        ddigits -= 2;
                    } else if dig < 1000 {
                        ddigits -= 1;
                    }

                    if ddigits > max_digits {
                        return true;
                    }

                    break;
                }

                ddigits -= DEC_DIGITS;
            }
        }

        false
    }

    /// Returns a normalized string, suppressing insignificant
    /// trailing zeroes and then any trailing decimal point.
    ///
    /// The intent of this is to produce strings that are equal
    /// if and only if the input numeric values compare equal.
    pub fn normalize(&self) -> String {
        if self.is_nan() {
            return String::from("NaN");
        }

        let mut s = self.to_string();

        // If there's no decimal point, there's certainly nothing to remove.
        if s.find('.').is_some() {
            // Back up over trailing fractional zeroes.  Since there is a decimal
            // point, this loop will terminate safely.
            let mut new_len = s.len();
            let bytes = s.as_bytes();
            let count_zeros = bytes.iter().rev().take_while(|i| **i == b'0').count();
            new_len -= count_zeros;

            // We want to get rid of the decimal point too, if it's now last.
            if bytes[new_len - 1] == b'.' {
                new_len -= 1;
            }

            // Delete whatever we backed up over.
            s.truncate(new_len);
        }

        s
    }

    /// Compute factorial.
    ///
    /// Returns `None` if overflows.
    pub fn factorial(num: i64) -> Option<Self> {
        if num <= 1 {
            return Some(ONE.clone());
        }

        // Fail immediately if the result would overflow
        if num > 32177 {
            // value overflows numeric format
            return None;
        }

        let mut result: NumericVar = From::from(num);

        for n in (2..num).rev() {
            let fact = From::from(n);
            result = result.mul_common(&fact, 0);
        }

        Some(result)
    }
}

impl<'a> fmt::Display for NumericVar<'a> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        self.write(f)
    }
}
