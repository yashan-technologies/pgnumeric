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
use std::fmt;

const NBASE: i32 = 10000;
const HALF_NBASE: NumericDigit = 5000;
const DEC_DIGITS: usize = 4;
const MUL_GUARD_DIGITS: i32 = 2;
//const DIV_GUARD_DIGITS: i32 = 4;

//const NUMERIC_SIGN_MASK: i32 = 0xC000;
const NUMERIC_POS: i32 = 0x0000;
const NUMERIC_NEG: i32 = 0x4000;
//const NUMERIC_SHORT: i32 = 0x8000;
const NUMERIC_NAN: i32 = 0xC000;

type NumericDigit = i16;

static ROUND_POWERS: [NumericDigit; 4] = [0, 1000, 100, 10];

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
    fn round(&mut self, rscale: i32) {
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
    #[allow(dead_code)]
    fn trunc(&mut self, rscale: i32) {
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
    fn add(&self, other: &Self) -> Self {
        if self.is_nan() || other.is_nan() {
            return Self::nan();
        }

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
    fn sub(&self, other: &Self) -> Self {
        if self.is_nan() || other.is_nan() {
            return Self::nan();
        }

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
    fn mul(&self, other: &Self, rscale: i32) -> Self {
        if self.is_nan() || other.is_nan() {
            return Self::nan();
        }

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
        result.round(rscale);

        // Strip leading and trailing zeroes
        result.strip();

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
    use std::convert::TryInto;

    fn assert_round_floating<V: TryInto<NumericVar, Error = NumericTryFromError>, E: AsRef<str>>(
        val: V,
        rscale: i32,
        expected: E,
    ) {
        let mut numeric = val.try_into().unwrap();
        numeric.round(rscale);
        assert_eq!(numeric.to_string(), expected.as_ref());
    }

    #[test]
    fn round() {
        assert_round_floating(123456.123456f64, 6, "123456.123456");
        assert_round_floating(123456.123456f64, 5, "123456.12346");
        assert_round_floating(123456.123456f64, 4, "123456.1235");
        assert_round_floating(123456.123456f64, 3, "123456.123");
        assert_round_floating(123456.123456f64, 2, "123456.12");
        assert_round_floating(123456.123456f64, 1, "123456.1");
        assert_round_floating(123456.123456f64, 0, "123456");
        assert_round_floating(123456.123456f64, -1, "123460");
        assert_round_floating(123456.123456f64, -2, "123500");
        assert_round_floating(123456.123456f64, -3, "123000");
        assert_round_floating(123456.123456f64, -4, "120000");
        assert_round_floating(123456.123456f64, -5, "100000");
        assert_round_floating(9999.9f64, 1, "9999.9");
        assert_round_floating(9999.9f64, -2, "10000");
        assert_round_floating(9999.9f64, -4, "10000");
    }

    fn assert_trunc_floating<V: TryInto<NumericVar, Error = NumericTryFromError>, E: AsRef<str>>(
        val: V,
        rscale: i32,
        expected: E,
    ) {
        let mut numeric = val.try_into().unwrap();
        numeric.trunc(rscale);
        assert_eq!(numeric.to_string(), expected.as_ref());
    }

    #[test]
    fn trunc() {
        assert_trunc_floating(123456.123456f64, 6, "123456.123456");
        assert_trunc_floating(123456.123456f64, 5, "123456.12345");
        assert_trunc_floating(123456.123456f64, 4, "123456.1234");
        assert_trunc_floating(123456.123456f64, 3, "123456.123");
        assert_trunc_floating(123456.123456f64, 2, "123456.12");
        assert_trunc_floating(123456.123456f64, 1, "123456.1");
        assert_trunc_floating(123456.123456f64, 0, "123456");
        assert_trunc_floating(123456.123456f64, -1, "123450");
        assert_trunc_floating(123456.123456f64, -2, "123400");
        assert_trunc_floating(123456.123456f64, -3, "123000");
        assert_trunc_floating(123456.123456f64, -4, "120000");
        assert_trunc_floating(123456.123456f64, -5, "100000");
        assert_trunc_floating(9999.9f64, 1, "9999.9");
        assert_trunc_floating(9999.9f64, -2, "9900");
        assert_trunc_floating(9999.9f64, -4, "0");
    }
}
