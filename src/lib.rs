// Copyright 2020 CoD Team

//! Arbitrary precision numeric, compatible with PostgreSQL's numeric.

mod convert;
mod error;
mod ops;
mod parse;

pub use crate::convert::TryFromRef;
pub use crate::error::NumericParseError;
pub use crate::error::NumericTryFromError;

use crate::parse::{parse_decimal, Decimal};
use lazy_static::lazy_static;
use std::fmt;

/// Limit on the precision (and hence scale) specifiable in a NUMERIC typmod.
/// Note that the implementation limit on the length of a numeric value is
/// much larger --- beware of what you use this for!
const NUMERIC_MAX_PRECISION: i32 = 1000;

// Internal limits on the scales chosen for calculation results
const NUMERIC_MAX_DISPLAY_SCALE: i32 = NUMERIC_MAX_PRECISION;
const NUMERIC_MIN_DISPLAY_SCALE: i32 = 0;

//const NUMERIC_MAX_RESULT_SCALE: i32 = NUMERIC_MAX_PRECISION * 2;

/// For inherently inexact calculations such as division and square root,
/// we try to get at least this many significant digits; the idea is to
/// deliver a result no worse than f64 would.
const NUMERIC_MIN_SIG_DIGITS: i32 = 16;

const NBASE: i32 = 10000;
const HALF_NBASE: NumericDigit = 5000;
const DEC_DIGITS: usize = 4;
const MUL_GUARD_DIGITS: i32 = 2;
const DIV_GUARD_DIGITS: i32 = 4;

//const NUMERIC_SIGN_MASK: i32 = 0xC000;
const NUMERIC_POS: i32 = 0x0000;
const NUMERIC_NEG: i32 = 0x4000;
//const NUMERIC_SHORT: i32 = 0x8000;
const NUMERIC_NAN: i32 = 0xC000;

type NumericDigit = i16;

const ROUND_POWERS: [NumericDigit; 4] = [0, 1000, 100, 10];

lazy_static! {
    // 0.5
    static ref ZERO_POINT_FIVE: NumericVar = ".5".parse().unwrap();
    static ref ONE: NumericVar = "1".parse().unwrap();
}

/// `NumericVar` is the format we use for arithmetic.
/// The value represented by a NumericVar is determined by the `sign`, `weight`,
/// `ndigits`, and `digits[]` array.
///
/// Note: the first digit of a NumericVar's value is assumed to be multiplied
/// by NBASE ** weight.  Another way to say it is that there are weight+1
/// digits before the decimal point.  It is possible to have weight < 0.
///
/// `buf` points at the physical start of the digit buffer for the
/// NumericVar. `offset` points at the first digit in actual use (the one
/// with the specified weight).  We normally leave an unused digit or two
/// (preset to zeroes) between buf and digits, so that there is room to store
/// a carry out of the top digit without reallocating space.  We just need to
/// decrement digits (and increment weight) to make room for the carry digit.
/// (There is no such extra space in a numeric value stored in the database,
/// only in a NumericVar in memory.)
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
pub struct NumericVar {
    ndigits: i32,
    weight: i32,
    sign: i32,
    dscale: i32,
    buf: Vec<NumericDigit>,
    offset: usize,
}

impl NumericVar {
    /// Creates a `NaN` numeric.
    pub const fn nan() -> Self {
        Self {
            ndigits: 0,
            weight: 0,
            sign: NUMERIC_NAN,
            dscale: 0,
            buf: Vec::new(),
            offset: 0,
        }
    }

    /// Creates a zero numeric.
    pub const fn zero() -> Self {
        Self {
            ndigits: 0,
            weight: 0,
            sign: NUMERIC_POS,
            dscale: 0,
            buf: Vec::new(),
            offset: 0,
        }
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

    /// Returns immutable digits buffer.
    #[inline]
    fn digits(&self) -> &[NumericDigit] {
        debug_assert_eq!(self.buf.len(), self.offset + self.ndigits as usize);
        &self.buf.as_slice()[self.offset..self.offset + self.ndigits as usize]
    }

    /// Returns mutable digits buffer.
    #[inline]
    fn digits_mut(&mut self) -> &mut [NumericDigit] {
        debug_assert_eq!(self.buf.len(), self.offset + self.ndigits as usize);
        &mut self.buf.as_mut_slice()[self.offset..self.offset + self.ndigits as usize]
    }

    /// Allocates digits buffer.
    fn alloc_buf(&mut self, ndigits: i32) {
        self.buf = Vec::with_capacity(ndigits as usize + 1);
        unsafe {
            self.buf.set_len(ndigits as usize + 1);
        }
        self.buf[0] = 0; // spare digit for later rounding
        self.offset = 1;
        self.ndigits = ndigits;
    }

    /// Sets `self` to ZERO.
    ///
    /// Note: its dscale is not touched.
    #[allow(dead_code)]
    fn zeroed(&mut self) {
        self.ndigits = 0;
        self.weight = 0;
        self.sign = NUMERIC_POS;
        self.buf = Vec::new();
        self.offset = 0;
    }

    /// Round the value of a variable to no more than rscale decimal digits
    /// after the decimal point.
    ///
    /// NOTE: we allow rscale < 0 here, implying rounding before the decimal point.
    fn round_common(&mut self, rscale: i32) {
        debug_assert!(!self.is_nan());

        // Carry may need one additional digit
        debug_assert!(self.offset > 0 || self.ndigits == 0);

        // decimal digits wanted
        let di = (self.weight + 1) * DEC_DIGITS as i32 + rscale;

        // If di = 0, the value loses all digits, but could round up to 1 if its
        // first extra digit is >= 5.  If di < 0 the result must be 0.
        if di < 0 {
            self.ndigits = 0;
            self.weight = 0;
            self.sign = NUMERIC_POS;
        } else {
            // NBASE digits wanted
            let mut ndigits = (di + DEC_DIGITS as i32 - 1) / DEC_DIGITS as i32;
            // 0, or number of decimal digits to keep in last NBASE digit
            let di = di % DEC_DIGITS as i32;

            if ndigits < self.ndigits || (ndigits == self.ndigits && di > 0) {
                self.ndigits = ndigits;

                let digits = &mut self.buf.as_mut_slice()[self.offset..];
                let mut carry: i32 = 0;

                if di == 0 {
                    if digits[ndigits as usize] >= HALF_NBASE {
                        carry = 1;
                    }
                } else {
                    // Must round within last NBASE digit
                    let mut pow10 = ROUND_POWERS[di as usize];
                    ndigits -= 1;
                    let extra = digits[ndigits as usize] % pow10;
                    digits[ndigits as usize] -= extra;

                    if extra >= pow10 / 2 {
                        pow10 += digits[ndigits as usize];
                        if pow10 >= NBASE as NumericDigit {
                            pow10 -= NBASE as NumericDigit;
                            carry = 1;
                        }
                        digits[ndigits as usize] = pow10;
                    }
                }

                // Carry may need one additional digit, so we use buf from start.
                let digits = &mut self.buf.as_mut_slice();
                let offset = self.offset;

                // Propagate carry if needed
                while carry > 0 {
                    ndigits -= 1;
                    let i = (offset as i32 + ndigits) as usize;
                    carry += digits[i] as i32;

                    if carry >= NBASE as i32 {
                        digits[i] = (carry - NBASE as i32) as NumericDigit;
                        carry = 1;
                    } else {
                        digits[i] = carry as NumericDigit;
                        carry = 0;
                    }
                }

                if ndigits < 0 {
                    debug_assert_eq!(ndigits, -1);
                    debug_assert!(self.offset > 0);
                    self.offset -= 1;
                    self.ndigits += 1;
                    self.weight += 1;
                }
            }
        }

        self.dscale = rscale;
        self.buf.truncate(self.offset + self.ndigits as usize);
    }

    /// Truncate (towards zero) the value of a variable at rscale decimal digits
    /// after the decimal point.
    ///
    /// NOTE: we allow rscale < 0 here, implying truncation before the decimal point.
    fn trunc_common(&mut self, rscale: i32) {
        debug_assert!(!self.is_nan());

        // decimal digits wanted
        let di = (self.weight + 1) * DEC_DIGITS as i32 + rscale;

        // If di <= 0, the value loses all digits.
        if di <= 0 {
            self.ndigits = 0;
            self.weight = 0;
            self.sign = NUMERIC_POS;
        } else {
            // NBASE digits wanted
            let mut ndigits = (di + DEC_DIGITS as i32 - 1) / DEC_DIGITS as i32;

            if ndigits <= self.ndigits {
                self.ndigits = ndigits;

                // 0, or number of decimal digits to keep in last NBASE digit
                let di = di % DEC_DIGITS as i32;

                if di > 0 {
                    let digits = &mut self.buf.as_mut_slice()[self.offset..];
                    let pow10 = ROUND_POWERS[di as usize];
                    ndigits -= 1;

                    let extra = digits[ndigits as usize] % pow10;
                    digits[ndigits as usize] -= extra;
                }
            }
        }

        self.dscale = rscale;
        self.buf.truncate(self.offset + self.ndigits as usize);
    }

    /// Return the smallest integer greater than or equal to the argument
    /// on variable level
    fn ceil_common(&self) -> Self {
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
    fn floor_common(&self) -> Self {
        debug_assert!(!self.is_nan());

        let mut result = self.clone();
        result.trunc_common(0);

        if self.is_negative() && self.cmp_common(&result) != 0 {
            result = result.sub_common(&ONE);
        }

        result
    }

    /// Strips the leading and trailing zeroes, and normalize zero.
    fn strip(&mut self) {
        let digits = &self.buf.as_slice()[self.offset..];
        let mut ndigits = self.ndigits;
        let mut i = 0;

        // strip leading zeroes
        while ndigits > 0 && digits[i] == 0 {
            i += 1;
            self.weight -= 1;
            ndigits -= 1;
        }

        // strip trailing zeroes
        while ndigits > 0 && digits[i + ndigits as usize - 1] == 0 {
            ndigits -= 1;
        }

        // if it's zero, normalize the sign and weight
        if ndigits == 0 {
            self.sign = NUMERIC_POS;
            self.weight = 0;
        }

        self.offset += i;
        self.ndigits = ndigits;
        self.buf.truncate(self.offset + ndigits as usize);
    }

    /// Reserve 1 digit for rounding.
    fn reserve_digit(&mut self) {
        if self.ndigits > 0 && self.offset == 0 {
            let mut buf = Vec::with_capacity(self.ndigits as usize + 1);
            buf.push(0); // spare digit for rounding
            buf.extend_from_slice(self.digits());

            self.buf = buf;
            self.offset = 1;
        }
    }

    /// Set this numeric from other numeric.
    ///
    /// Note: If there are digits, we will reserve one more digit for rounding.
    fn set_from_var(&mut self, value: &NumericVar) {
        self.ndigits = value.ndigits;
        self.weight = value.weight;
        self.sign = value.sign;
        self.dscale = value.dscale;

        if value.ndigits > 0 {
            let mut buf = Vec::with_capacity(value.ndigits as usize + 1);
            buf.push(0); // spare digit for rounding
            buf.extend_from_slice(value.digits());

            self.buf = buf;
            self.offset = 1;
        } else {
            self.buf = Vec::new();
            self.offset = 0;
        }
    }

    /// Parses a string bytes and put the number into this variable.
    ///
    /// This function does not handle leading or trailing spaces, and it doesn't
    /// accept `NaN` either. It returns the remaining string bytes so that caller can
    /// check for trailing spaces/garbage if deemed necessary.
    fn set_from_str<'a>(&mut self, s: &'a [u8]) -> Result<&'a [u8], NumericParseError> {
        let (
            Decimal {
                sign,
                integral,
                fractional,
                exp,
            },
            s,
        ) = parse_decimal(s)?;

        let dec_weight = integral.len() as i32 + exp - 1;
        let dec_scale = {
            let mut result = fractional.len() as i32 - exp;
            if result < 0 {
                result = 0;
            }
            result
        };

        let weight = if dec_weight >= 0 {
            (dec_weight + 1 + DEC_DIGITS as i32 - 1) / DEC_DIGITS as i32 - 1
        } else {
            -((-dec_weight - 1) / DEC_DIGITS as i32 + 1)
        };
        let offset = (weight + 1) * DEC_DIGITS as i32 - (dec_weight + 1);
        let ndigits =
            (integral.len() as i32 + fractional.len() as i32 + offset + DEC_DIGITS as i32 - 1)
                / DEC_DIGITS as i32;

        let mut dec_digits: Vec<u8> =
            Vec::with_capacity(integral.len() + fractional.len() + DEC_DIGITS * 2);
        // leading padding for digit alignment later
        dec_digits.extend_from_slice([0; DEC_DIGITS].as_ref());
        dec_digits.extend(integral.iter().map(|&i| i - b'0'));
        dec_digits.extend(fractional.iter().map(|&i| i - b'0'));
        // trailing padding for digit alignment later
        dec_digits.extend_from_slice([0; DEC_DIGITS].as_ref());

        self.alloc_buf(ndigits);
        self.sign = sign as i32;
        self.weight = weight;
        self.dscale = dec_scale;

        let mut i = 0;
        let digits = self.digits_mut();
        debug_assert_eq!(ndigits as usize, digits.len());

        let iter = (&dec_digits[DEC_DIGITS - offset as usize..])
            .chunks_exact(DEC_DIGITS)
            .take(ndigits as usize);
        for chunk in iter {
            let digit = read_numeric_digit(chunk);
            digits[i] = digit;
            i += 1;
        }

        // Strip any leading/trailing zeroes, and normalize weight if zero.
        self.strip();

        Ok(s)
    }

    /// Add the absolute values of two variables into result.
    fn add_abs(&self, other: &Self) -> Self {
        debug_assert!(!self.is_nan());
        debug_assert!(!other.is_nan());

        // copy these values into local vars for speed in inner loop
        let var1_ndigits = self.ndigits;
        let var2_ndigits = other.ndigits;
        let var1_digits = self.digits();
        let var2_digits = other.digits();

        let res_weight = std::cmp::max(self.weight, other.weight) + 1;
        let res_dscale = std::cmp::max(self.dscale, other.dscale);

        // Note: here we are figuring rscale in base-NBASE digits
        let res_rscale = {
            let rscale1 = self.ndigits - self.weight - 1;
            let rscale2 = other.ndigits - other.weight - 1;
            std::cmp::max(rscale1, rscale2)
        };

        let res_ndigits = {
            let ndigits = res_rscale + res_weight + 1;
            if ndigits > 0 {
                ndigits
            } else {
                1
            }
        };

        let mut res = Self::nan();
        res.alloc_buf(res_ndigits);
        let res_digits = res.digits_mut();

        let mut carry: NumericDigit = 0;
        let mut i1 = res_rscale + self.weight + 1;
        let mut i2 = res_rscale + other.weight + 1;
        for i in (0..res_ndigits as usize).rev() {
            i1 -= 1;
            i2 -= 1;

            if i1 >= 0 && i1 < var1_ndigits {
                carry += var1_digits[i1 as usize];
            }
            if i2 >= 0 && i2 < var2_ndigits {
                carry += var2_digits[i2 as usize];
            }

            if carry >= NBASE as NumericDigit {
                res_digits[i] = carry - NBASE as NumericDigit;
                carry = 1;
            } else {
                res_digits[i] = carry;
                carry = 0;
            }
        }

        debug_assert_eq!(carry, 0); // else we failed to allow for carry out

        res.ndigits = res_ndigits;
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
    fn sub_abs(&self, other: &Self) -> Self {
        debug_assert!(!self.is_nan());
        debug_assert!(!other.is_nan());

        // copy these values into local vars for speed in inner loop
        let var1_ndigits = self.ndigits;
        let var2_ndigits = other.ndigits;
        let var1_digits = self.digits();
        let var2_digits = other.digits();

        let res_weight = self.weight;
        let res_dscale = std::cmp::max(self.dscale, other.dscale);

        // Note: here we are figuring rscale in base-NBASE digits
        let res_rscale = {
            let rscale1 = self.ndigits - self.weight - 1;
            let rscale2 = other.ndigits - other.weight - 1;
            std::cmp::max(rscale1, rscale2)
        };

        let res_ndigits = {
            let ndigits = res_rscale + res_weight + 1;
            if ndigits <= 0 {
                1
            } else {
                ndigits
            }
        };

        let mut res = Self::nan();
        res.alloc_buf(res_ndigits);
        let res_digits = res.digits_mut();

        let mut borrow: NumericDigit = 0;
        let mut i1 = res_rscale + self.weight + 1;
        let mut i2 = res_rscale + other.weight + 1;
        for i in (0..res_ndigits as usize).rev() {
            i1 -= 1;
            i2 -= 1;

            if i1 >= 0 && i1 < var1_ndigits {
                borrow += var1_digits[i1 as usize];
            }
            if i2 >= 0 && i2 < var2_ndigits {
                borrow -= var2_digits[i2 as usize];
            }

            if borrow < 0 {
                res_digits[i] = borrow + NBASE as NumericDigit;
                borrow = -1;
            } else {
                res_digits[i] = borrow;
                borrow = 0;
            }
        }

        debug_assert_eq!(borrow, 0); // else caller gave us self < other

        res.ndigits = res_ndigits;
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
    fn cmp_abs(&self, other: &Self) -> i32 {
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
            if var1_digits[i1 as usize] != 0 {
                return 1;
            }

            i1 += 1;
            var1_weight -= 1;
        }
        while var2_weight > var1_weight && i2 < var2_ndigits {
            if var2_digits[i2 as usize] != 0 {
                return -1;
            }

            i2 += 1;
            var2_weight -= 1;
        }

        // At this point, either var1_weight == var2_weight or we've run out of digits

        if var1_weight == var2_weight {
            while i1 < var1_ndigits && i2 < var2_ndigits {
                let stat = var1_digits[i1 as usize] - var2_digits[i2 as usize];
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
            if var1_digits[i1 as usize] != 0 {
                return 1;
            }

            i1 += 1;
        }
        while i2 < var2_ndigits {
            if var2_digits[i2 as usize] != 0 {
                return -1;
            }

            i2 += 1;
        }

        return 0;
    }

    /// Full version of add functionality on variable level (handling signs).
    fn add_common(&self, other: &Self) -> Self {
        debug_assert!(!self.is_nan());
        debug_assert!(!other.is_nan());

        // Decide on the signs of the two variables what to do
        if self.is_positive() {
            if other.is_positive() {
                // Both are positive
                // result = +(ABS(self) + ABS(other))
                let mut result = self.add_abs(other);
                result.sign = NUMERIC_POS;
                return result;
            } else {
                let cmp = self.cmp_abs(other);
                match cmp {
                    0 => {
                        // ABS(self) == ABS(other)
                        // result = ZERO
                        let mut result = Self::zero();
                        result.dscale = std::cmp::max(self.dscale, other.dscale);
                        return result;
                    }
                    1 => {
                        // ABS(self) > ABS(other)
                        // result = +(ABS(self) - ABS(other))
                        let mut result = self.sub_abs(other);
                        result.sign = NUMERIC_POS;
                        return result;
                    }
                    -1 => {
                        // ABS(self) < ABS(other)
                        // result = -(ABS(other) - ABS(self))
                        let mut result = other.sub_abs(self);
                        result.sign = NUMERIC_NEG;
                        return result;
                    }
                    _ => panic!("invalid comparison result"),
                }
            }
        } else {
            if other.is_positive() {
                // self is negative, other is positive
                // Must compare absolute values
                let cmp = self.cmp_abs(other);
                match cmp {
                    0 => {
                        // ABS(self) == ABS(other)
                        // result = ZERO
                        let mut result = Self::zero();
                        result.dscale = std::cmp::max(self.dscale, other.dscale);
                        return result;
                    }
                    1 => {
                        // ABS(self) > ABS(other)
                        // result = -(ABS(self) - ABS(other))
                        let mut result = self.sub_abs(other);
                        result.sign = NUMERIC_NEG;
                        return result;
                    }
                    -1 => {
                        // ABS(self) < ABS(other)
                        // result = +(ABS(other) - ABS(self))
                        let mut result = other.sub_abs(self);
                        result.sign = NUMERIC_POS;
                        return result;
                    }
                    _ => panic!("invalid comparison result"),
                }
            } else {
                // Both are negative
                // result = -(ABS(self) + ABS(other))
                let mut result = self.add_abs(other);
                result.sign = NUMERIC_NEG;
                return result;
            }
        }
    }

    /// Full version of sub functionality on variable level (handling signs).
    fn sub_common(&self, other: &Self) -> Self {
        debug_assert!(!self.is_nan());
        debug_assert!(!other.is_nan());

        // Decide on the signs of the two variables what to do
        if self.is_positive() {
            if other.is_negative() {
                // self is positive, other is negative
                // result = +(ABS(self) + ABS(other))
                let mut result = self.add_abs(other);
                result.sign = NUMERIC_POS;
                return result;
            } else {
                // Both are positive
                // Must compare absolute values
                let cmp = self.cmp_abs(other);
                match cmp {
                    0 => {
                        // ABS(self) == ABS(other)
                        // result = ZERO
                        let mut result = Self::zero();
                        result.dscale = std::cmp::max(self.dscale, other.dscale);
                        return result;
                    }
                    1 => {
                        // ABS(self) > ABS(other)
                        // result = +(ABS(self) - ABS(other))
                        let mut result = self.sub_abs(other);
                        result.sign = NUMERIC_POS;
                        return result;
                    }
                    -1 => {
                        // ABS(self) < ABS(other)
                        // result = -(ABS(other) - ABS(self))
                        let mut result = other.sub_abs(self);
                        result.sign = NUMERIC_NEG;
                        return result;
                    }
                    _ => panic!("invalid comparison result"),
                }
            }
        } else {
            if other.is_negative() {
                // Both are negative
                // Must compare absolute values
                let cmp = self.cmp_abs(other);
                match cmp {
                    0 => {
                        // ABS(self) == ABS(other)
                        // result = ZERO
                        let mut result = Self::zero();
                        result.dscale = std::cmp::max(self.dscale, other.dscale);
                        return result;
                    }
                    1 => {
                        // ABS(self) > ABS(other)
                        // result = -(ABS(self) - ABS(other))
                        let mut result = self.sub_abs(other);
                        result.sign = NUMERIC_NEG;
                        return result;
                    }
                    -1 => {
                        // ABS(self) < ABS(other)
                        // result = +(ABS(other) - ABS(self))
                        let mut result = other.sub_abs(self);
                        result.sign = NUMERIC_POS;
                        return result;
                    }
                    _ => panic!("invalid comparison result"),
                }
            } else {
                // var1 is negative, var2 is positive
                // result = -(ABS(self) + ABS(other))
                let mut result = self.add_abs(other);
                result.sign = NUMERIC_NEG;
                return result;
            }
        }
    }

    /// Multiplication on variable level.
    /// Product of self * other is returned.
    /// Result is rounded to no more than rscale fractional digits.
    fn mul_common(&self, other: &Self, rscale: i32) -> Self {
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
            let mut result = Self::zero();
            result.dscale = rscale;
            return result;
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
            let max_digits = res_weight
                + 1
                + (rscale + DEC_DIGITS as i32 - 1) / DEC_DIGITS as i32
                + MUL_GUARD_DIGITS;
            std::cmp::min(ndigits, max_digits)
        };

        if res_ndigits < 3 {
            // All input digits will be ignored; so result is zero
            let mut result = Self::zero();
            result.dscale = rscale;
            return result;
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
        let bound = std::cmp::min(var1_ndigits - 1, res_ndigits - 3);
        for i1 in (0..=bound).rev() {
            let var1_digit = var1_digits[i1 as usize] as i32;
            if var1_digit == 0 {
                continue;
            }

            // Time to normalize?
            max_dig += var1_digit;
            if max_dig > ((i32::max_value() - i32::max_value() / NBASE) / (NBASE - 1)) {
                // Yes, do it
                let mut carry = 0;
                for i in (0..res_ndigits).rev() {
                    let mut new_dig = dig[i as usize] + carry;
                    if new_dig >= NBASE {
                        carry = new_dig / NBASE;
                        new_dig -= carry * NBASE;
                    } else {
                        carry = 0;
                    }
                    dig[i as usize] = new_dig;
                }
                debug_assert_eq!(carry, 0);
                // Reset max_dig to indicate new worst-case
                max_dig = 1 + var1_digit;
            }

            // Add the appropriate multiple of var2 into the accumulator.
            //
            // As above, digits of var2 can be ignored if they don't contribute,
            // so we only include digits for which i1+i2+2 <= res_ndigits - 1.
            let bound = std::cmp::min(var2_ndigits - 1, res_ndigits - i1 - 3);
            let mut i = i1 + bound + 2;
            for i2 in (0..=bound).rev() {
                dig[i as usize] += var1_digit * var2_digits[i2 as usize] as i32;
                i -= 1;
            }
        }

        // Now we do a final carry propagation pass to normalize the result, which
        // we combine with storing the result digits into the output. Note that
        // this is still done at full precision w/guard digits.
        let mut result = Self::nan();
        result.alloc_buf(res_ndigits);
        let res_digits = result.digits_mut();
        let mut carry = 0;
        for i in (0..res_ndigits).rev() {
            let mut new_dig = dig[i as usize] as i32 + carry;
            if new_dig >= NBASE {
                carry = new_dig / NBASE;
                new_dig -= carry * NBASE;
            } else {
                carry = 0;
            }
            res_digits[i as usize] = new_dig as NumericDigit;
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
    fn select_div_scale(&self, other: &Self) -> i32 {
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
            first_digit1 = var1_digits[i as usize];
            if first_digit1 != 0 {
                weight1 = self.weight - i;
                break;
            }
        }

        let mut weight2 = 0; // values to use if other is zero
        let mut first_digit2 = 0;
        let var2_digits = other.digits();
        for i in 0..other.ndigits {
            first_digit2 = var2_digits[i as usize];
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
        let mut rscale = NUMERIC_MIN_SIG_DIGITS - qweight * DEC_DIGITS as i32;
        rscale = std::cmp::max(rscale, self.dscale);
        rscale = std::cmp::max(rscale, other.dscale);
        rscale = std::cmp::max(rscale, NUMERIC_MIN_DISPLAY_SCALE);
        rscale = std::cmp::min(rscale, NUMERIC_MAX_DISPLAY_SCALE);

        rscale
    }

    /// Division on variable level. Quotient of `self` / `other` is returned.
    /// The quotient is figured to exactly rscale fractional digits.
    /// If round is true, it is rounded at the rscale'th digit; if false, it
    /// is truncated (towards zero) at that digit.
    ///
    /// Returns `None` if `other == 0`.
    fn div_common(&self, other: &Self, rscale: i32, round: bool) -> Option<Self> {
        debug_assert!(!self.is_nan());
        debug_assert!(!other.is_nan());

        // copy these values into local vars for speed in inner loop
        let var1_ndigits = self.ndigits;
        let var2_ndigits = other.ndigits;

        // First of all division by zero check; we must not be handed an
        // unnormalized divisor.
        if var2_ndigits == 0 || other.digits()[0] == 0 {
            return None;
        }

        // Now result zero check
        if var1_ndigits == 0 {
            let mut result = Self::zero();
            result.dscale = rscale;
            return Some(result);
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
            let mut ndigits = res_weight + 1 + (rscale + DEC_DIGITS as i32 - 1) / DEC_DIGITS as i32;
            // ... but always at least 1
            ndigits = std::cmp::max(ndigits, 1);
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
            std::cmp::max(ndigits, var1_ndigits)
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
        dividend[1..var1_ndigits as usize + 1].copy_from_slice(self.digits());
        divisor[1..var2_ndigits as usize + 1].copy_from_slice(other.digits());

        // Now we can alloc the result to hold the generated quotient digits.
        let mut result = Self::nan();
        result.alloc_buf(res_ndigits);
        let res_digits = result.digits_mut();

        if var2_ndigits == 1 {
            // If there's only a single divisor digit, we can use a fast path (cf.
            // Knuth section 4.3.1 exercise 16).
            let divisor1 = divisor[1] as i32;
            let mut carry = 0i32;
            for i in 0..res_ndigits as usize {
                carry = carry * NBASE + dividend[i + 1] as i32;
                res_digits[i] = (carry / divisor1) as NumericDigit;
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
                    carry += divisor[i] as i32 * d;
                    divisor[i] = (carry % NBASE) as NumericDigit;
                    carry /= NBASE;
                }
                debug_assert_eq!(carry, 0);

                carry = 0;
                // at this point only var1_ndigits of dividend can be nonzero
                for i in (0..=var1_ndigits as usize).rev() {
                    carry += dividend[i] as i32 * d;
                    dividend[i] = (carry % NBASE) as NumericDigit;
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
            for j in 0..res_ndigits as usize {
                // Estimate quotient digit from the first two dividend digits
                let next2digits = dividend[j] as i32 * NBASE + dividend[j + 1] as i32;

                // If next2digits are 0, then quotient digit must be 0 and there's
                // no need to adjust the working dividend.  It's worth testing
                // here to fall out ASAP when processing trailing zeroes in a
                // dividend.
                if next2digits == 0 {
                    res_digits[j] = 0;
                    continue;
                }

                let mut qhat = if dividend[j] == divisor1 {
                    NBASE - 1
                } else {
                    next2digits / divisor1 as i32
                };

                // Adjust quotient digit if it's too large.  Knuth proves that
                // after this step, the quotient digit will be either correct or
                // just one too large.  (Note: it's OK to use dividend[j+2] here
                // because we know the divisor length is at least 2.)
                while divisor2 as i32 * qhat
                    > (next2digits - qhat * divisor1 as i32) * NBASE + dividend[j + 2] as i32
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
                        carry += divisor[i] as i32 * qhat;
                        borrow -= carry % NBASE;
                        carry /= NBASE;
                        borrow += dividend[j + i] as i32;
                        if borrow < 0 {
                            dividend[j + i] = (borrow + NBASE) as NumericDigit;
                            borrow = -1;
                        } else {
                            dividend[j + i] = borrow as NumericDigit;
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
                            carry += dividend[j + i] as i32 + divisor[i] as i32;
                            if carry >= NBASE {
                                dividend[j + i] = (carry - NBASE) as NumericDigit;
                                carry = 1;
                            } else {
                                dividend[j + i] = carry as NumericDigit;
                                carry = 0;
                            }
                        }
                        // A carry should occur here to cancel the borrow above
                        debug_assert_eq!(carry, 1);
                    }
                }

                // And we're done with this quotient digit
                res_digits[j] = qhat as NumericDigit;
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

    /// This has the same API as `div()`, but is implemented using the division
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
    fn div_fast_common(&self, other: &Self, rscale: i32, round: bool) -> Option<Self> {
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
            let mut result = Self::zero();
            result.dscale = rscale;
            return Some(result);
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
            let mut ndigits = res_weight + 1 + (rscale + DEC_DIGITS as i32 - 1) / DEC_DIGITS as i32;
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
            div[i + 1] = var1_digits[i] as i32;
        }

        // We estimate each quotient digit using floating-point arithmetic, taking
        // the first four digits of the (current) dividend and divisor.  This must
        // be float to avoid overflow.  The quotient digits will generally be off
        // by no more than one from the exact answer.
        let mut fdivisor = var2_digits[0] as f64;
        for i in 1..4 {
            fdivisor *= NBASE as f64;
            if i < var2_ndigits {
                fdivisor += var2_digits[i as usize] as f64;
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
            let mut fdividend = div[qi] as f64;
            for i in 1..4usize {
                fdividend *= NBASE as f64;
                if (qi + i) as i32 <= div_ndigits {
                    fdividend += div[qi + i] as f64;
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
                        new_dig = div[i] + carry;
                        if new_dig < 0 {
                            carry = -((-new_dig - 1) / NBASE) - 1;
                            new_dig -= carry * NBASE;
                        } else if new_dig >= NBASE {
                            carry = new_dig / NBASE;
                            new_dig -= carry * NBASE;
                        } else {
                            carry = 0;
                        }
                        div[i] = new_dig;
                    }
                    new_dig = div[qi] + carry;
                    div[qi] = new_dig;

                    // All the div[] digits except possibly div[qi] are now in the
                    // range 0..NBASE-1.  We do not need to consider div[qi] in
                    // the max_div value anymore, so we can reset max_div to 1.
                    max_div = 1;

                    // Recompute the quotient digit since new info may have
                    // propagated into the top four dividend digits
                    fdividend = div[qi] as f64;
                    for i in 1..4usize {
                        fdividend *= NBASE as f64;
                        if (qi + i) as i32 <= div_ndigits {
                            fdividend += div[qi + i] as f64;
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
                    let istop = std::cmp::min(var2_ndigits, div_ndigits - qi as i32 + 1);
                    for i in 0..istop as usize {
                        div[qi + i] -= qdigit * var2_digits[i] as i32;
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
            div[qi + 1] += div[qi] * NBASE;

            div[qi] = qdigit;
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
        let mut result = Self::nan();
        result.alloc_buf(div_ndigits + 1);
        let res_digits = result.digits_mut();

        let mut carry = 0;
        for i in (0..=div_ndigits as usize).rev() {
            let mut new_dig = div[i] + carry;
            if new_dig < 0 {
                carry = -((-new_dig - 1) / NBASE) - 1;
                new_dig -= carry * NBASE;
            } else if new_dig >= NBASE {
                carry = new_dig / NBASE;
                new_dig -= carry * NBASE;
            } else {
                carry = 0;
            }
            res_digits[i] = new_dig as NumericDigit;
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
    fn mod_common(&self, other: &Self) -> Option<Self> {
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
    fn cmp_common(&self, other: &Self) -> i32 {
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
    fn sqrt_common(&self, rscale: i32) -> Self {
        debug_assert!(self.is_positive());

        let local_rscale = rscale + 8;

        if self.ndigits == 0 {
            let mut result = Self::zero();
            result.dscale = rscale;
            return result;
        }

        // Initialize the result to the first guess
        let mut result = Self::zero();
        result.alloc_buf(1);
        result.digits_mut()[0] = {
            let i = self.digits()[0] / 2;
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

    /// Negate this value.
    #[inline]
    pub fn negate(&mut self) {
        if self.ndigits > 0 {
            if self.is_positive() {
                self.sign = NUMERIC_NEG;
            } else if self.is_negative() {
                self.sign = NUMERIC_POS;
            }
        }
    }

    /// Checked numeric division.
    /// Computes `self / other`, returning `None` if `other == 0`.
    #[inline]
    pub fn checked_div(&self, other: &Self) -> Option<Self> {
        // Handle NaN
        if self.is_nan() || other.is_nan() {
            return Some(NumericVar::nan());
        }

        // Select scale for division result
        let rscale = self.select_div_scale(other);
        NumericVar::div_common(self, other, rscale, true)
    }

    /// Round a value to have `scale` digits after the decimal point.
    /// We allow negative `scale`, implying rounding before the decimal
    /// point --- Oracle interprets rounding that way.
    #[inline]
    pub fn round(&mut self, scale: i32) {
        if self.is_nan() {
            return;
        }

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
        if self.is_nan() {
            return;
        }

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
        if self.is_nan() {
            return Self::nan();
        }

        self.ceil_common()
    }

    /// Return the largest integer equal to or less than the argument.
    #[inline]
    pub fn floor(&self) -> Self {
        if self.is_nan() {
            return Self::nan();
        }

        self.floor_common()
    }

    /// Compute the absolute value of `self`.
    #[inline]
    pub fn abs(&mut self) {
        if self.is_nan() {
            return;
        }

        self.sign = NUMERIC_POS;
    }

    /// Compute the square root of a numeric.
    ///
    /// # Panics
    /// Panics if `self` is negative.
    pub fn sqrt(&self) -> Self {
        assert!(
            !self.is_negative(),
            "cannot take square root of a negative number"
        );

        if self.is_nan() {
            return Self::nan();
        }

        // Determine the result scale.
        // We choose a scale to give at least NUMERIC_MIN_SIG_DIGITS significant digits;
        // but in any case not less than the input's dscale.

        // Assume the input was normalized, so arg.weight is accurate
        let sweight = (self.weight + 1) * DEC_DIGITS as i32 / 2 - 1;

        let rscale = (NUMERIC_MIN_SIG_DIGITS - sweight)
            .max(self.dscale)
            .max(NUMERIC_MIN_DISPLAY_SCALE)
            .min(NUMERIC_MAX_DISPLAY_SCALE);

        let result = self.sqrt_common(rscale);
        result
    }
}

impl fmt::Display for NumericVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
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

                // In the first digit, suppress extra leading decimal zeroes.
                if d > 0 {
                    write!(f, "{:>0width$}", dig, width = DEC_DIGITS)?;
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

            for scale in (0..self.dscale).step_by(DEC_DIGITS) {
                let dig = if d >= 0 && d < self.ndigits {
                    digits[d as usize]
                } else {
                    0
                };

                if scale + DEC_DIGITS as i32 <= self.dscale {
                    write!(f, "{:>0width$}", dig, width = DEC_DIGITS)?;
                } else {
                    // truncate the last digit
                    let width = (self.dscale - scale) as usize;
                    let dig = (0..DEC_DIGITS - width).fold(dig, |acc, _| acc / 10);
                    write!(f, "{:>0width$}", dig, width = width)?;
                }

                d += 1;
            }
        }

        Ok(())
    }
}

/// Reads a `NumericDigit` from `&[u8]`.
#[inline]
fn read_numeric_digit(s: &[u8]) -> NumericDigit {
    debug_assert!(s.len() <= DEC_DIGITS);

    let mut digit = 0;

    for &i in s {
        digit = digit * 10 + i as NumericDigit;
    }

    digit
}

#[cfg(test)]
mod tests {
    use super::*;

    fn assert_round(val: &str, rscale: i32, expected: &str) {
        let mut numeric = val.parse::<NumericVar>().unwrap();
        numeric.round(rscale);
        assert_eq!(numeric.to_string(), expected);
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
        let mut numeric = val.parse::<NumericVar>().unwrap();
        numeric.trunc(rscale);
        assert_eq!(numeric.to_string(), expected);
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
        let var = val.parse::<NumericVar>().unwrap();
        let result = var.sqrt();
        assert_eq!(result.to_string(), expected);
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
        let var = "-1".parse::<NumericVar>().unwrap();
        let _ = var.sqrt();
    }

    fn assert_ceil(val: &str, expected: &str) {
        let var = val.parse::<NumericVar>().unwrap();
        let result = var.ceil();
        assert_eq!(result.to_string(), expected);
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
        let var = val.parse::<NumericVar>().unwrap();
        let result = var.floor();
        assert_eq!(result.to_string(), expected);
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
        let mut var = val.parse::<NumericVar>().unwrap();
        var.abs();
        assert_eq!(var.to_string(), expected);
    }

    #[test]
    fn abs() {
        assert_abs("NaN", "NaN");
        assert_abs("0.0", "0.0");
        assert_abs("123456.123456", "123456.123456");
        assert_abs("-123456.123456", "123456.123456");
    }
}
