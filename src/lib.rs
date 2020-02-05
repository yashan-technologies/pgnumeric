// Copyright 2020 CoD Team

//! Arbitrary precision numeric, compatible with PostgreSQL's numeric.

pub use crate::error::ParseNumericError;
use crate::parse::{eat_whitespaces, extract_nan, parse_decimal, Decimal};
use std::fmt;
use std::str::FromStr;

mod error;
mod parse;

//const NBASE: i32 = 10000;
//const HALF_NBASE: i32 = 5000;
const DEC_DIGITS: usize = 4;
//const MUL_GUARD_DIGITS: i32 = 2;
//const DIV_GUARD_DIGITS: i32 = 4;

//const NUMERIC_SIGN_MASK: i32 = 0xC000;
const NUMERIC_POS: i32 = 0x0000;
const NUMERIC_NEG: i32 = 0x4000;
//const NUMERIC_SHORT: i32 = 0x8000;
const NUMERIC_NAN: i32 = 0xC000;

type NumericDigit = i16;

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
#[derive(Debug)]
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
    fn set_var_from_str<'a>(&mut self, s: &'a [u8]) -> Result<&'a [u8], ParseNumericError> {
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
    fn from_str(s: &str) -> Result<Self, ParseNumericError> {
        let s = s.as_bytes();
        let s = eat_whitespaces(s);
        if s.is_empty() {
            return Err(ParseNumericError::empty());
        }

        let (is_nan, s) = extract_nan(s);

        let numeric = if is_nan {
            if s.iter().any(|n| !n.is_ascii_whitespace()) {
                return Err(ParseNumericError::invalid());
            }

            Self::nan()
        } else {
            let mut n = NumericVar::nan();
            let s = n.set_var_from_str(s)?;

            if s.iter().any(|n| !n.is_ascii_whitespace()) {
                return Err(ParseNumericError::invalid());
            }

            n
        };

        Ok(numeric)
    }
}

impl FromStr for NumericVar {
    type Err = ParseNumericError;

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

#[cfg(test)]
mod tests {
    use super::*;

    fn assert_empty<S: AsRef<str>>(s: S) {
        let result = s.as_ref().parse::<NumericVar>();
        assert_eq!(result.unwrap_err(), ParseNumericError::empty());
    }

    fn assert_invalid<S: AsRef<str>>(s: S) {
        let result = s.as_ref().parse::<NumericVar>();
        assert_eq!(result.unwrap_err(), ParseNumericError::invalid());
    }

    fn assert_overflow<S: AsRef<str>>(s: S) {
        let result = s.as_ref().parse::<NumericVar>();
        assert_eq!(result.unwrap_err(), ParseNumericError::overflow());
    }

    #[test]
    fn parse_error() {
        assert_empty("");
        assert_empty("   ");
        assert_invalid("-");
        assert_invalid("   -   ");
        assert_invalid("-.");
        assert_invalid("- 1");
        assert_invalid("-NaN");
        assert_invalid("NaN.");
        assert_invalid("NaN1");
        assert_invalid("   NaN   .   ");
        assert_invalid("   NaN   1   ");
        assert_invalid(".");
        assert_invalid("   .   ");
        assert_invalid("e");
        assert_invalid("   e   ");
        assert_invalid("-e");
        assert_invalid("-1e");
        assert_invalid("1e1.1");
        assert_invalid("-1 e1");
        assert_invalid("   x   ");
        assert_overflow("1e10000000000");
        assert_overflow("1e2147483648");
        assert_overflow("1e-2147483648");
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
}
