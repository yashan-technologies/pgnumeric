// Copyright 2020 CoD Team

//! Arbitrary precision numeric, compatible with PostgreSQL's numeric.

mod convert;
mod error;
mod parse;

pub use crate::error::NumericParseError;
pub use crate::error::NumericTryFromError;

use crate::convert::{from_floating, from_signed, from_unsigned};
use crate::parse::{eat_whitespaces, extract_nan, parse_decimal, Decimal};
use std::convert::TryFrom;
use std::fmt;
use std::str::FromStr;

const NBASE: i32 = 10000;
const HALF_NBASE: NumericDigit = 5000;
const DEC_DIGITS: usize = 4;
//const MUL_GUARD_DIGITS: i32 = 2;
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

    /// Returns immutable digits buffer.
    #[inline]
    fn digits(&self) -> &[NumericDigit] {
        debug_assert_eq!(self.buf.len(), self.offset + self.ndigits as usize);
        &self.buf.as_slice()[self.offset..]
    }

    /// Returns mutable digits buffer.
    #[inline]
    fn digits_mut(&mut self) -> &mut [NumericDigit] {
        debug_assert_eq!(self.buf.len(), self.offset + self.ndigits as usize);
        &mut self.buf.as_mut_slice()[self.offset..]
    }

    /// Checks if the value is `NaN`.
    #[inline]
    pub fn is_nan(&self) -> bool {
        self.sign == NUMERIC_NAN
    }

    /// Allocates digits buffer.
    fn alloc(&mut self, ndigits: i32) {
        self.buf = Vec::with_capacity(ndigits as usize + 1);
        unsafe {
            self.buf.set_len(ndigits as usize + 1);
        }
        self.buf[0] = 0;
        self.offset = 1;
        self.ndigits = ndigits;
    }

    /// Round the value of a variable to no more than rscale decimal digits
    /// after the decimal point.
    ///
    /// NOTE: we allow rscale < 0 here, implying rounding before the decimal point.
    #[allow(dead_code)]
    fn round(&mut self, rscale: i32) {
        // Carry may need one additional digit
        debug_assert!(self.offset > 0);

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
                let mut carray: i32 = 0;

                if di == 0 {
                    if digits[ndigits as usize] >= HALF_NBASE {
                        carray = 1;
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
                            carray = 1;
                        }
                        digits[ndigits as usize] = pow10;
                    }
                }

                // Carry may need one additional digit, so we use buf from start.
                let digits = &mut self.buf.as_mut_slice();
                let offset = self.offset;

                // Propagate carry if needed
                while carray > 0 {
                    ndigits -= 1;
                    let i = (offset as i32 + ndigits) as usize;
                    carray += digits[i] as i32;

                    if carray >= NBASE as i32 {
                        digits[i] = (carray - NBASE as i32) as NumericDigit;
                        carray = 1;
                    } else {
                        digits[i] = carray as NumericDigit;
                        carray = 0;
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

    /// Parses a string bytes and put the number into this variable.
    ///
    /// This function does not handle leading or trailing spaces, and it doesn't
    /// accept `NaN` either. It returns the remaining string bytes so that caller can
    /// check for trailing spaces/garbage if deemed necessary.
    fn set_var_from_str<'a>(&mut self, s: &'a [u8]) -> Result<&'a [u8], NumericParseError> {
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

        self.alloc(ndigits);
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

    /// Parses a string slice and creates a number.
    ///
    /// This function handles leading or trailing spaces, and it
    /// accepts `NaN` either.
    fn from_str(s: &str) -> Result<Self, NumericParseError> {
        let s = s.as_bytes();
        let s = eat_whitespaces(s);
        if s.is_empty() {
            return Err(NumericParseError::empty());
        }

        let (is_nan, s) = extract_nan(s);

        let numeric = if is_nan {
            if s.iter().any(|n| !n.is_ascii_whitespace()) {
                return Err(NumericParseError::invalid());
            }

            Self::nan()
        } else {
            let mut n = NumericVar::nan();
            let s = n.set_var_from_str(s)?;

            if s.iter().any(|n| !n.is_ascii_whitespace()) {
                return Err(NumericParseError::invalid());
            }

            n
        };

        Ok(numeric)
    }
}

impl FromStr for NumericVar {
    type Err = NumericParseError;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        NumericVar::from_str(s)
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

macro_rules! impl_from_signed {
    ($t: ty) => {
        impl From<$t> for NumericVar {
            #[inline]
            fn from(val: $t) -> Self {
                from_signed(val)
            }
        }
    };
}

macro_rules! impl_from_unsigned {
    ($t: ty) => {
        impl From<$t> for NumericVar {
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

impl From<bool> for NumericVar {
    fn from(b: bool) -> Self {
        let val = if b { 1u8 } else { 0u8 };
        val.into()
    }
}

impl From<usize> for NumericVar {
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

impl From<isize> for NumericVar {
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
        impl TryFrom<$t> for NumericVar {
            type Error = NumericTryFromError;

            fn try_from(f: $t) -> Result<Self, Self::Error> {
                from_floating(f)
            }
        }
    };
}

impl_try_from_floating!(f32);
impl_try_from_floating!(f64);

#[cfg(test)]
mod tests {
    use super::*;
    use std::convert::TryInto;

    fn assert_parse_empty<S: AsRef<str>>(s: S) {
        let result = s.as_ref().parse::<NumericVar>();
        assert_eq!(result.unwrap_err(), NumericParseError::empty());
    }

    fn assert_parse_invalid<S: AsRef<str>>(s: S) {
        let result = s.as_ref().parse::<NumericVar>();
        assert_eq!(result.unwrap_err(), NumericParseError::invalid());
    }

    fn assert_parse_overflow<S: AsRef<str>>(s: S) {
        let result = s.as_ref().parse::<NumericVar>();
        assert_eq!(result.unwrap_err(), NumericParseError::overflow());
    }

    #[test]
    fn parse_error() {
        assert_parse_empty("");
        assert_parse_empty("   ");
        assert_parse_invalid("-");
        assert_parse_invalid("   -   ");
        assert_parse_invalid("-.");
        assert_parse_invalid("- 1");
        assert_parse_invalid("-NaN");
        assert_parse_invalid("NaN.");
        assert_parse_invalid("NaN1");
        assert_parse_invalid("   NaN   .   ");
        assert_parse_invalid("   NaN   1   ");
        assert_parse_invalid(".");
        assert_parse_invalid("   .   ");
        assert_parse_invalid("e");
        assert_parse_invalid("   e   ");
        assert_parse_invalid("-e");
        assert_parse_invalid("-1e");
        assert_parse_invalid("1e1.1");
        assert_parse_invalid("-1 e1");
        assert_parse_invalid("   x   ");
        assert_parse_overflow("1e10000000000");
        assert_parse_overflow("1e2147483648");
        assert_parse_overflow("1e-2147483648");
    }

    fn assert_parse<S: AsRef<str>, V: AsRef<str>>(s: S, expected: V) {
        let numeric = s.as_ref().parse::<NumericVar>().unwrap();
        assert_eq!(numeric.to_string(), expected.as_ref());
    }

    #[test]
    fn parse_valid() {
        // NaN
        assert_parse("NaN", "NaN");
        assert_parse("   NaN   ", "NaN");

        // Integer
        assert_parse("0", "0");
        assert_parse("-0", "0");
        assert_parse("   -0   ", "0");
        assert_parse("00000.", "0");
        assert_parse("-00000.", "0");
        assert_parse("128", "128");
        assert_parse("-128", "-128");
        assert_parse("65536", "65536");
        assert_parse("-65536", "-65536");
        assert_parse("4294967296", "4294967296");
        assert_parse("-4294967296", "-4294967296");
        assert_parse("18446744073709551616", "18446744073709551616");
        assert_parse("-18446744073709551616", "-18446744073709551616");
        assert_parse(
            "340282366920938463463374607431768211456",
            "340282366920938463463374607431768211456",
        );
        assert_parse(
            "-340282366920938463463374607431768211456",
            "-340282366920938463463374607431768211456",
        );
        assert_parse("000000000123", "123");
        assert_parse("-000000000123", "-123");

        // Floating-point number
        assert_parse("0.0", "0.0");
        assert_parse("-0.0", "0.0");
        assert_parse("   -0.0   ", "0.0");
        assert_parse(".0", "0.0");
        assert_parse(".00000", "0.00000");
        assert_parse("-.0", "0.0");
        assert_parse("-.00000", "0.00000");
        assert_parse("128.128", "128.128");
        assert_parse("-128.128", "-128.128");
        assert_parse("65536.65536", "65536.65536");
        assert_parse("-65536.65536", "-65536.65536");
        assert_parse("4294967296.4294967296", "4294967296.4294967296");
        assert_parse("-4294967296.4294967296", "-4294967296.4294967296");
        assert_parse(
            "18446744073709551616.18446744073709551616",
            "18446744073709551616.18446744073709551616",
        );
        assert_parse(
            "-18446744073709551616.18446744073709551616",
            "-18446744073709551616.18446744073709551616",
        );
        assert_parse(
            "340282366920938463463374607431768211456.340282366920938463463374607431768211456",
            "340282366920938463463374607431768211456.340282366920938463463374607431768211456",
        );
        assert_parse(
            "-340282366920938463463374607431768211456.340282366920938463463374607431768211456",
            "-340282366920938463463374607431768211456.340282366920938463463374607431768211456",
        );
        assert_parse("000000000123.000000000123", "123.000000000123");
        assert_parse("-000000000123.000000000123", "-123.000000000123");

        // Scientific notation
        assert_parse("0e0", "0");
        assert_parse("-0E-0", "0");
        assert_parse("0000000000E0000000000", "0");
        assert_parse("-0000000000E-0000000000", "0");
        assert_parse("00000000001e0000000000", "1");
        assert_parse("-00000000001e-0000000000", "-1");
        assert_parse("00000000001e00000000001", "10");
        assert_parse("-00000000001e-00000000001", "-0.1");
        assert_parse("1e10", "10000000000");
        assert_parse("-1e-10", "-0.0000000001");
        assert_parse("0000001.23456000e3", "1234.56000");
        assert_parse("-0000001.23456000E-3", "-0.00123456000");
    }

    fn assert_from<V: Into<NumericVar>, E: AsRef<str>>(val: V, expected: E) {
        let numeric = val.into();
        assert_eq!(numeric.to_string(), expected.as_ref());
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

    fn assert_try_from<V: TryInto<NumericVar, Error = NumericTryFromError>, E: AsRef<str>>(
        val: V,
        expected: E,
    ) {
        let numeric = val.try_into().unwrap();
        assert_eq!(numeric.to_string(), expected.as_ref());
    }

    fn assert_try_from_invalid<V: TryInto<NumericVar, Error = NumericTryFromError>>(val: V) {
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
