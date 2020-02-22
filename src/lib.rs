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
use std::convert::{TryFrom, TryInto};
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

const NBASE: i32 = 10000;
const HALF_NBASE: NumericDigit = 5000;
const DEC_DIGITS: i32 = 4;
const MUL_GUARD_DIGITS: i32 = 2;
const DIV_GUARD_DIGITS: i32 = 4;

//const NUMERIC_SIGN_MASK: i32 = 0xC000;
const NUMERIC_POS: i32 = 0x0000;
const NUMERIC_NEG: i32 = 0x4000;
//const NUMERIC_SHORT: i32 = 0x8000;
const NUMERIC_NAN: i32 = 0xC000;

const VAR_HEADER_SIZE: i32 = std::mem::size_of::<i32>() as i32;

type NumericDigit = i16;

const ROUND_POWERS: [NumericDigit; 4] = [0, 1000, 100, 10];

lazy_static! {
    // 0.5
    static ref ZERO_POINT_FIVE: NumericVar = ".5".parse().unwrap();
    // 0.9
    static ref ZERO_POINT_NINE: NumericVar = ".9".parse().unwrap();
    // 1.1
    static ref ONE_POINT_ONE: NumericVar = "1.1".parse().unwrap();
    // 1
    static ref ONE: NumericVar = "1".parse().unwrap();
    // 2
    static ref TWO: NumericVar = "2".parse().unwrap();
    // 10
    static ref TEN: NumericVar = "10".parse().unwrap();
}

const DIVIDE_BY_ZERO_MSG: &str = "attempt to divide by zero";

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
        Self::scaled_zero(0)
    }

    /// Creates a zero numeric with given scale.
    pub const fn scaled_zero(scale: i32) -> Self {
        Self {
            ndigits: 0,
            weight: 0,
            sign: NUMERIC_POS,
            dscale: scale,
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

    /// Returns the scale, i.e. the count of decimal digits in the fractional part.
    ///
    /// Returns `None` if `self` is `NaN`.
    #[inline]
    pub fn scale(&self) -> Option<i32> {
        if self.is_nan() {
            None
        } else {
            Some(self.dscale)
        }
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
            (dec_weight + 1 + DEC_DIGITS - 1) / DEC_DIGITS - 1
        } else {
            -((-dec_weight - 1) / DEC_DIGITS + 1)
        };
        let offset = (weight + 1) * DEC_DIGITS - (dec_weight + 1);
        let ndigits = (integral.len() as i32 + fractional.len() as i32 + offset + DEC_DIGITS - 1)
            / DEC_DIGITS;

        let mut dec_digits: Vec<u8> =
            Vec::with_capacity(integral.len() + fractional.len() + DEC_DIGITS as usize * 2);
        // leading padding for digit alignment later
        dec_digits.extend_from_slice([0; DEC_DIGITS as usize].as_ref());
        dec_digits.extend(integral.iter().map(|&i| i - b'0'));
        dec_digits.extend(fractional.iter().map(|&i| i - b'0'));
        // trailing padding for digit alignment later
        dec_digits.extend_from_slice([0; DEC_DIGITS as usize].as_ref());

        self.alloc_buf(ndigits);
        self.sign = sign as i32;
        self.weight = weight;
        self.dscale = dec_scale;

        let mut i = 0;
        let digits = self.digits_mut();
        debug_assert_eq!(ndigits as usize, digits.len());

        let iter = (&dec_digits[(DEC_DIGITS - offset) as usize..])
            .chunks_exact(DEC_DIGITS as usize)
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

    /// Convert `self` to text representation.
    /// `self` is displayed to the number of digits indicated by its dscale.
    fn write<W: fmt::Write>(&self, f: &mut W) -> Result<(), fmt::Error> {
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
    fn write_sci<W: fmt::Write>(
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
            exp -= DEC_DIGITS - (self.digits()[0] as f64).log10() as i32;
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
    fn select_sci_scale(&self) -> i32 {
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

        let result = front + end + (ri - i - 1) as i32 * DEC_DIGITS - 1;

        result
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
                        return Self::scaled_zero(self.dscale.max(other.dscale));
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
                        return Self::scaled_zero(self.dscale.max(other.dscale));
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
                        return Self::scaled_zero(self.dscale.max(other.dscale));
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
                        return Self::scaled_zero(self.dscale.max(other.dscale));
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
            return Self::scaled_zero(rscale);
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
            std::cmp::min(ndigits, max_digits)
        };

        if res_ndigits < 3 {
            // All input digits will be ignored; so result is zero
            return Self::scaled_zero(rscale);
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
        let mut rscale = NUMERIC_MIN_SIG_DIGITS - qweight * DEC_DIGITS;
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
            return Some(Self::scaled_zero(rscale));
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
            return Some(Self::scaled_zero(rscale));
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
            return Self::scaled_zero(rscale);
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

    /// Raise `self` to the power of exp, where exp is an integer.
    ///
    /// Returns `None` if overflows.
    ///
    /// # Panics
    /// Panics if self is zero and exp is less than zero.
    fn power_int(&self, exp: i32, rscale: i32) -> Option<Self> {
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
            return Some(Self::scaled_zero(rscale));
        }

        // The general case repeatedly multiplies base according to the bit
        // pattern of exp.
        //
        // First we need to estimate the weight of the result so that we know how
        // many significant digits are needed.
        let digits = self.digits();
        let mut f = digits[0] as f64;
        let mut p = self.weight * DEC_DIGITS;

        for i in 1..self.ndigits as usize {
            if (i * DEC_DIGITS as usize) < 16 {
                break;
            }

            f = f * NBASE as f64 + digits[i] as f64;
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
            return Some(Self::scaled_zero(rscale));
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
                result.zeroed();
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
    fn ln_common(&self, rscale: i32) -> Self {
        debug_assert!(!self.is_nan());
        debug_assert!(self.cmp_common(&Self::zero()) > 0);

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

    /// Compute the logarithm of `self` in a given base.
    ///
    /// Note: this routine chooses dscale of the result.
    fn log_common(&self, base: &NumericVar) -> Self {
        debug_assert!(!self.is_nan());
        debug_assert!(!base.is_nan());
        debug_assert!(self.cmp_common(&Self::zero()) > 0);

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
        let result = ln_num
            .div_fast_common(&ln_base, rscale, true)
            .expect(DIVIDE_BY_ZERO_MSG);

        result
    }

    /// Raise e to the power of x, computed to rscale fractional digits.
    ///
    /// Returns `None` if overflows.
    fn exp_common(&self, rscale: i32) -> Option<Self> {
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
        let dweight = (val * std::f64::consts::LOG10_E) as i32;
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
        const LOG10_2: f64 = 0.301029995663981_f64;
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

    /// Estimate the dweight of the most significant decimal digit of the natural
    /// logarithm of a number.
    ///
    /// Essentially, we're approximating `log10(abs(ln(self)))`.  This is used to
    /// determine the appropriate rscale when computing natural logarithms.
    fn estimate_ln_dweight(&self) -> i32 {
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
                let ln_var = (digits as f64).ln() + dweight as f64 * std::f64::consts::LN_10;
                ln_dweight = ln_var.abs().log10() as i32;
            } else {
                ln_dweight = 0;
            }
        }

        ln_dweight
    }

    /// Raise `self` to the power of `exp`
    ///
    /// Returns `None` if overflows.
    ///
    /// Note: this routine chooses dscale of the result.
    ///
    /// # Panics
    /// Panics if self is zero and exp is less than zero.
    fn power_common(&self, exp: &NumericVar) -> Option<Self> {
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
        if self.cmp_common(&Self::zero()) == 0 {
            return Some(Self::scaled_zero(NUMERIC_MIN_SIG_DIGITS));
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

        val *= std::f64::consts::LOG10_E; // approximate decimal result weight

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
        let result = ln_num.exp_common(rscale);

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

    /// Returns a numeric that represents the sign of self.
    /// * -1 if `self` is less than 0
    /// * 0 if `self` is equal to 0
    /// * 1 if `self` is greater than zero
    /// * `NaN` if `self` is `NaN`
    #[inline]
    pub fn signum(&self) -> Self {
        if self.is_nan() {
            Self::nan()
        } else if self.ndigits == 0 {
            Self::zero()
        } else {
            let mut result = ONE.clone();
            result.sign = self.sign;
            result
        }
    }

    /// Increment `self` by one.
    #[inline]
    pub fn inc(&self) -> Self {
        if self.is_nan() {
            return Self::nan();
        }

        // Compute the result and return it
        self.add_common(&ONE)
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

    /// Computes `self / other`, truncating the result to an integer.
    ///
    /// Returns `None` if `other == 0`.
    #[inline]
    pub fn checked_div_trunc(&self, other: &Self) -> Option<Self> {
        // Handle NaN
        if self.is_nan() || other.is_nan() {
            return Some(NumericVar::nan());
        }

        NumericVar::div_common(self, other, 0, false)
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
    #[inline]
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
        let sweight = (self.weight + 1) * DEC_DIGITS / 2 - 1;

        let rscale = (NUMERIC_MIN_SIG_DIGITS - sweight)
            .max(self.dscale)
            .max(NUMERIC_MIN_DISPLAY_SCALE)
            .min(NUMERIC_MAX_DISPLAY_SCALE);

        let result = self.sqrt_common(rscale);
        result
    }

    /// Compute the natural logarithm of `self`.
    ///
    /// # Panics
    /// Panics if `self <= 0`.
    #[inline]
    pub fn ln(&self) -> Self {
        if self.is_nan() {
            return Self::nan();
        }

        let cmp = self.cmp_common(&Self::zero());
        assert_ne!(cmp, 0, "cannot take logarithm of zero");
        assert!(cmp > 0, "cannot take logarithm of a negative number");

        // Estimated dweight of logarithm
        let ln_dweight = self.estimate_ln_dweight();

        let rscale = (NUMERIC_MIN_SIG_DIGITS - ln_dweight)
            .max(self.dscale)
            .max(NUMERIC_MIN_DISPLAY_SCALE)
            .min(NUMERIC_MAX_DISPLAY_SCALE);

        let result = self.ln_common(rscale);
        result
    }

    /// Compute the logarithm of `self` in a given base.
    ///
    /// # Panics
    /// Panics if `self <= 0` or `base <= 0`.
    #[inline]
    pub fn log(&self, base: &Self) -> Self {
        if self.is_nan() || base.is_nan() {
            return Self::nan();
        }

        let cmp = self.cmp_common(&Self::zero());
        assert_ne!(cmp, 0, "cannot take logarithm of zero");
        assert!(cmp > 0, "cannot take logarithm of a negative number");

        let cmp = base.cmp_common(&Self::zero());
        assert_ne!(cmp, 0, "cannot take logarithm of zero");
        assert!(cmp > 0, "cannot take logarithm of a negative number");

        //  Call log_common() to compute and return the result; note it handles scale
        //	selection itself.
        let result = self.log_common(base);
        result
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
    #[inline]
    pub fn exp(&self) -> Option<Self> {
        if self.is_nan() {
            return Some(Self::nan());
        }

        // Determine the result scale.  We choose a scale
        // to give at least NUMERIC_MIN_SIG_DIGITS significant digits;
        // but in any case not less than the input's dscale.

        let mut val: f64 = TryFrom::try_from(self).unwrap();

        // log10(result) = num * log10(e), so this is approximately the decimal
        // weight of the result:
        val *= std::f64::consts::LOG10_E;

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
    pub fn pow(&self, exp: &NumericVar) -> Option<Self> {
        // Handle NaN cases.  We follow the POSIX spec for pow(3), which says that
        // NaN ^ 0 = 1, and 1 ^ NaN = 1, while all other cases with NaN inputs
        // yield NaN (with no error).
        if self.is_nan() {
            if !exp.is_nan() {
                if exp.cmp_common(&Self::zero()) == 0 {
                    return Some(ONE.clone());
                }
            }
            return Some(Self::nan());
        } else if exp.is_nan() {
            if self.cmp_common(&ONE) == 0 {
                return Some(ONE.clone());
            }
            return Some(Self::nan());
        }

        if self.cmp_common(&Self::zero()) == 0 && exp.cmp_common(&Self::zero()) < 0 {
            panic!("zero raised to a negative power is undefined")
        }

        let mut exp_trunc = exp.clone();
        exp_trunc.trunc_common(0);

        if self.cmp_common(&Self::zero()) < 0 && exp.cmp_common(&exp_trunc) != 0 {
            panic!("a negative number raised to a non-integer power yields a complex result")
        }

        // Call power_common() to compute and return the result; note it handles
        // scale selection itself.
        self.power_common(exp)
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
            let fact: NumericVar = From::from(n);
            result = result.mul_common(&fact, 0);
        }

        Some(result)
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
}

/// Reads a `NumericDigit` from `&[u8]`.
#[inline]
fn read_numeric_digit(s: &[u8]) -> NumericDigit {
    debug_assert!(s.len() <= DEC_DIGITS as usize);

    let mut digit = 0;

    for &i in s {
        digit = digit * 10 + i as NumericDigit;
    }

    digit
}

impl fmt::Display for NumericVar {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        self.write(f)
    }
}

impl fmt::LowerExp for NumericVar {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let rscale = self.select_sci_scale();
        self.write_sci(f, rscale, true)
    }
}

impl fmt::UpperExp for NumericVar {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let rscale = self.select_sci_scale();
        self.write_sci(f, rscale, false)
    }
}

/// Type modifier.
///
/// For numeric, `Typmod` is composed by `precision` and `scale`.
/// They are converted into a internal integer value.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct Typmod(i32);

impl Typmod {
    /// Creates a `Typmod`.
    ///
    /// Callers have to guarantee that:
    /// * `1 <= precision <= NUMERIC_MAX_PRECISION`
    /// * `0 <= scale <= precision`
    #[inline]
    pub unsafe fn new_unchecked(precision: i32, scale: i32) -> Self {
        debug_assert!(precision >= 1 && precision <= NUMERIC_MAX_PRECISION);
        debug_assert!(scale >= 0 && scale <= precision);

        Typmod(((precision << 16) | scale) + VAR_HEADER_SIZE)
    }

    /// Creates a `Typmod`.
    /// `scale` defaults to zero.
    ///
    /// Callers have to guarantee that:
    /// * `1 <= precision <= NUMERIC_MAX_PRECISION`
    #[inline]
    pub unsafe fn with_precision_unchecked(precision: i32) -> Self {
        debug_assert!(precision >= 1 && precision <= NUMERIC_MAX_PRECISION);

        Typmod((precision << 16) + VAR_HEADER_SIZE)
    }

    /// Creates a `Typmod`.
    ///
    /// Returns `None`:
    /// * if `1 <= precision <= NUMERIC_MAX_PRECISION`
    /// * if `0 <= scale <= precision`
    #[inline]
    pub fn new(precision: i32, scale: i32) -> Option<Self> {
        if precision < 1 || precision > NUMERIC_MAX_PRECISION {
            None
        } else if scale < 0 || scale > precision {
            None
        } else {
            Some(unsafe { Self::new_unchecked(precision, scale) })
        }
    }

    /// Creates a `Typmod`.
    /// `scale` defaults to zero.
    ///
    /// Returns `None`:
    /// * if `1 <= precision <= NUMERIC_MAX_PRECISION`
    #[inline]
    pub fn with_precision(precision: i32) -> Option<Self> {
        if precision < 1 || precision > NUMERIC_MAX_PRECISION {
            None
        } else {
            Some(unsafe { Self::with_precision_unchecked(precision) })
        }
    }

    /// Creates a `Typmod` from a `Typmod`'s value.
    ///
    /// Callers have to guarantee that the `value` is valid.
    #[inline]
    pub unsafe fn from_value_unchecked(value: i32) -> Self {
        Typmod(value)
    }

    /// Returns `Typmod`'s value in `i32`.
    #[inline]
    pub const fn value(self) -> i32 {
        self.0
    }

    /// Extracts `(precision, scale)` from `Typmod`.
    #[inline]
    pub const fn extract(self) -> (i32, i32) {
        let t = self.0 - VAR_HEADER_SIZE;
        ((t >> 16) & 0xFFFF, t & 0xFFFF)
    }
}

impl Default for Typmod {
    #[inline]
    fn default() -> Self {
        Typmod(-1)
    }
}

impl fmt::Display for Typmod {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let (precision, scale) = self.extract();
        write!(f, "({}, {})", precision, scale)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn assert_signum(val: &str, expected: &str) {
        let val = val.parse::<NumericVar>().unwrap();
        let result = val.signum();
        assert_eq!(result.to_string(), expected);
    }

    #[test]
    fn signum() {
        assert_signum("NaN", "NaN");
        assert_signum("0", "0");
        assert_signum("31", "1");
        assert_signum("-47", "-1");
    }

    fn assert_inc(val: &str, expected: &str) {
        let val = val.parse::<NumericVar>().unwrap();
        let result = val.inc();
        assert_eq!(result.to_string(), expected);
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
        let val = val.parse::<NumericVar>().unwrap();
        let other = other.parse::<NumericVar>().unwrap();

        let result = val.checked_div_trunc(&other).map(|n| n.to_string());
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

    fn assert_write_sci(val: &str, scale: i32, expected: &str) {
        let var = val.parse::<NumericVar>().unwrap();
        let mut s = String::new();
        var.write_sci(&mut s, scale, true).unwrap();
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
        let var = val.parse::<NumericVar>().unwrap();
        let s = format!("{:E}", var);
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
        let var = val.parse::<NumericVar>().unwrap();
        let ln = var.ln();
        assert_eq!(ln.to_string(), expected);
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
        let var = val.parse::<NumericVar>().unwrap();
        let base = base.parse::<NumericVar>().unwrap();
        let log = var.log(&base);
        assert_eq!(log.to_string(), expected);
    }

    fn assert_log2(val: &str, expected: &str) {
        let var = val.parse::<NumericVar>().unwrap();
        let log2 = var.log2();
        assert_eq!(log2.to_string(), expected);
    }

    fn assert_log10(val: &str, expected: &str) {
        let var = val.parse::<NumericVar>().unwrap();
        let log2 = var.log10();
        assert_eq!(log2.to_string(), expected);
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
        let var = val.parse::<NumericVar>().unwrap();
        let ln = var.exp().expect("value overflows numeric format");
        assert_eq!(ln.to_string(), expected);
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
        let base = base.parse::<NumericVar>().unwrap();
        let exp = exp.parse::<NumericVar>().unwrap();
        let pow = base.pow(&exp).expect("value overflows numeric format");
        assert_eq!(pow.to_string(), expected);
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
        let result = NumericVar::factorial(num).map(|n| n.to_string());
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

    #[test]
    fn typmod() {
        let t = Typmod::new(10, 5).unwrap();
        assert_eq!(t.value(), 655369);
        assert_eq!(
            unsafe { Typmod::from_value_unchecked(655369) }.extract(),
            (10, 5)
        );
        assert_eq!(t.extract(), (10, 5));
        assert_eq!(t.to_string(), "(10, 5)");

        let t = Typmod::with_precision(10).unwrap();
        assert_eq!(t.value(), 655364);
        assert_eq!(
            unsafe { Typmod::from_value_unchecked(655364) }.extract(),
            (10, 0)
        );
        assert_eq!(t.extract(), (10, 0));
        assert_eq!(t.to_string(), "(10, 0)");

        assert_eq!(Typmod::new(0, 0), None);
        assert_eq!(Typmod::new(NUMERIC_MAX_PRECISION + 1, 0), None);
        assert_eq!(Typmod::new(10, -1), None);
        assert_eq!(Typmod::new(10, 11), None);
        assert_eq!(Typmod::with_precision(0), None);
        assert_eq!(Typmod::with_precision(NUMERIC_MAX_PRECISION + 1), None);
    }

    fn assert_apply_typmod(val: &str, typmod: Typmod, overflow: bool, expected: &str) {
        let mut val = val.parse::<NumericVar>().unwrap();
        let of = val.apply_typmod(typmod);
        assert_eq!(of, overflow);
        if !of {
            assert_eq!(val.to_string(), expected);
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
}
