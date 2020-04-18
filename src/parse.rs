// Copyright 2020 CoD Team

//! Numeric parsing utilities.

use crate::binary::{NumericDigit, NUMERIC_NEG, NUMERIC_POS};
use crate::data::NumericData;
use crate::error::NumericParseError;
use crate::num::NumericBuf;
use crate::var::{NumericVar, DEC_DIGITS};
use smallvec::SmallVec;
use std::convert::TryInto;
use std::str::FromStr;

#[derive(Debug)]
enum Sign {
    Positive = NUMERIC_POS as isize,
    Negative = NUMERIC_NEG as isize,
}

/// The interesting parts of a decimal string.
#[derive(Debug)]
struct Decimal<'a> {
    pub sign: Sign,
    pub integral: &'a [u8],
    pub fractional: &'a [u8],
    pub exp: i32,
}

/// Checks if the input string is a valid numeric and if so, locate the integral
/// part, the fractional part, and the exponent in it.
fn parse_decimal(s: &[u8]) -> Result<(Decimal, &[u8]), NumericParseError> {
    let (sign, s) = extract_sign(s);

    if s.is_empty() {
        return Err(NumericParseError::invalid());
    }

    let (integral, s) = eat_digits(s);

    let (fractional, exp, s) = match s.first() {
        Some(&b'e') | Some(&b'E') => {
            if integral.is_empty() {
                return Err(NumericParseError::invalid());
            }

            let (exp, s) = extract_exponent(&s[1..])?;
            (b"".as_ref(), exp, s)
        }
        Some(&b'.') => {
            let (fractional, s) = eat_digits(&s[1..]);
            if integral.is_empty() && fractional.is_empty() {
                return Err(NumericParseError::invalid());
            }

            match s.first() {
                Some(&b'e') | Some(&b'E') => {
                    let (exp, s) = extract_exponent(&s[1..])?;
                    (fractional, exp, s)
                }
                _ => (fractional, 0, s),
            }
        }
        _ => {
            if integral.is_empty() {
                return Err(NumericParseError::invalid());
            }

            (b"".as_ref(), 0, s)
        }
    };

    Ok((
        Decimal {
            sign,
            integral,
            fractional,
            exp,
        },
        s,
    ))
}

/// Carves off whitespaces up to the first non-whitespace character.
#[inline]
fn eat_whitespaces(s: &[u8]) -> &[u8] {
    let i = s.iter().take_while(|&i| i.is_ascii_whitespace()).count();
    &s[i..]
}

/// Carves off decimal digits up to the first non-digit character.
#[inline]
fn eat_digits(s: &[u8]) -> (&[u8], &[u8]) {
    let i = s.iter().take_while(|&i| i.is_ascii_digit()).count();
    (&s[..i], &s[i..])
}

/// Extracts `NaN` value.
#[inline]
fn extract_nan(s: &[u8]) -> (bool, &[u8]) {
    if s.len() < 3 {
        (false, s)
    } else {
        let mut buf: [u8; 3] = s[0..3].try_into().unwrap();
        buf.make_ascii_lowercase();
        if &buf == b"nan" {
            (true, &s[3..])
        } else {
            (false, s)
        }
    }
}

/// Splits a decimal string bytes into sign and the rest, without inspecting or validating the rest.
#[inline]
fn extract_sign(s: &[u8]) -> (Sign, &[u8]) {
    match s.first() {
        Some(b'+') => (Sign::Positive, &s[1..]),
        Some(b'-') => (Sign::Negative, &s[1..]),
        _ => (Sign::Positive, s),
    }
}

/// Extracts exponent, if any.
fn extract_exponent(s: &[u8]) -> Result<(i32, &[u8]), NumericParseError> {
    let (sign, s) = extract_sign(s);
    let (mut number, s) = eat_digits(s);

    if number.is_empty() {
        return Err(NumericParseError::invalid());
    }

    while number.first() == Some(&b'0') {
        number = &number[1..];
    }

    if number.len() > 10 {
        return Err(NumericParseError::overflow());
    }

    let exp = {
        let mut result: i64 = 0;
        for &n in number {
            result = result * 10 + (n - b'0') as i64;
        }
        match sign {
            Sign::Positive => result,
            Sign::Negative => -result,
        }
    };

    // At this point, dweight and dscale can't be more than about
    // INT_MAX/2 due to the MaxAllocSize limit on string length, so
    // constraining the exponent similarly should be enough to prevent
    // integer overflow in this function.
    if exp >= i32::max_value() as i64 / 2 || exp <= -(i32::max_value() as i64 / 2) {
        return Err(NumericParseError::overflow());
    }

    Ok((exp as i32, s))
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

/// Parses a string bytes and put the number into this variable.
///
/// This function does not handle leading or trailing spaces, and it doesn't
/// accept `NaN` either. It returns the remaining string bytes so that caller can
/// check for trailing spaces/garbage if deemed necessary.
fn parse_str(s: &[u8]) -> Result<(NumericVar<'static>, &[u8]), NumericParseError> {
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
    let ndigits =
        (integral.len() as i32 + fractional.len() as i32 + offset + DEC_DIGITS - 1) / DEC_DIGITS;

    let mut dec_digits: SmallVec<[u8; 128]> =
        SmallVec::with_capacity(integral.len() + fractional.len() + DEC_DIGITS as usize * 2);
    // leading padding for digit alignment later
    dec_digits.extend_from_slice([0; DEC_DIGITS as usize].as_ref());
    dec_digits.extend(integral.iter().map(|&i| i - b'0'));
    dec_digits.extend(fractional.iter().map(|&i| i - b'0'));
    // trailing padding for digit alignment later
    dec_digits.extend_from_slice([0; DEC_DIGITS as usize].as_ref());

    let mut data = NumericData::with_ndigits(ndigits);
    let digits = data.digits_mut(ndigits);
    debug_assert_eq!(ndigits as usize, digits.len());

    let iter = (&dec_digits[(DEC_DIGITS - offset) as usize..])
        .chunks_exact(DEC_DIGITS as usize)
        .take(ndigits as usize);
    for (i, chunk) in iter.enumerate() {
        let digit = read_numeric_digit(chunk);
        digits[i] = digit;
    }

    let num = NumericVar::owned(ndigits, weight, dec_scale, sign as u16, data);

    Ok((num, s))
}

/// Parses a string slice and creates a number.
///
/// This function handles leading or trailing spaces, and it
/// accepts `NaN` either.
fn from_str(s: &str) -> Result<NumericBuf, NumericParseError> {
    let s = s.as_bytes();
    let s = eat_whitespaces(s);
    if s.is_empty() {
        return Err(NumericParseError::empty());
    }

    let (is_nan, s) = extract_nan(s);

    if is_nan {
        if s.iter().any(|n| !n.is_ascii_whitespace()) {
            return Err(NumericParseError::invalid());
        }

        Ok(NumericBuf::nan())
    } else {
        let (n, s) = parse_str(s)?;

        if s.iter().any(|n| !n.is_ascii_whitespace()) {
            return Err(NumericParseError::invalid());
        }

        match n.make_result() {
            Some(result) => Ok(result),
            None => Err(NumericParseError::overflow()),
        }
    }
}

impl FromStr for NumericBuf {
    type Err = NumericParseError;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        from_str(s)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn assert_parse_empty<S: AsRef<str>>(s: S) {
        let result = s.as_ref().parse::<NumericBuf>();
        assert_eq!(result.unwrap_err(), NumericParseError::empty());
    }

    fn assert_parse_invalid<S: AsRef<str>>(s: S) {
        let result = s.as_ref().parse::<NumericBuf>();
        assert_eq!(result.unwrap_err(), NumericParseError::invalid());
    }

    fn assert_parse_overflow<S: AsRef<str>>(s: S) {
        let result = s.as_ref().parse::<NumericBuf>();
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
        let numeric = s.as_ref().parse::<NumericBuf>().unwrap();
        assert_eq!(numeric.to_string(), expected.as_ref());
    }

    #[test]
    fn parse_valid() {
        // NaN
        assert_parse("NaN", "NaN");
        assert_parse("Nan", "NaN");
        assert_parse("NAN", "NaN");
        assert_parse("NAn", "NaN");
        assert_parse("naN", "NaN");
        assert_parse("nan", "NaN");
        assert_parse("nAN", "NaN");
        assert_parse("nAn", "NaN");
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
