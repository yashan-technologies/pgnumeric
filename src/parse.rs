// Copyright 2020 CoD Team

//! Numeric parsing utilities

use crate::{ParseNumericError, NUMERIC_NEG, NUMERIC_POS};

#[derive(Debug)]
pub enum Sign {
    Positive = NUMERIC_POS as isize,
    Negative = NUMERIC_NEG as isize,
}

/// The interesting parts of a decimal string.
#[derive(Debug)]
pub struct Decimal<'a> {
    pub sign: Sign,
    pub integral: &'a [u8],
    pub fractional: &'a [u8],
    pub exp: i32,
}

/// Checks if the input string is a valid numeric and if so, locate the integral
/// part, the fractional part, and the exponent in it.
pub fn parse_decimal(s: &[u8]) -> Result<(Decimal, &[u8]), ParseNumericError> {
    let (sign, s) = extract_sign(s);

    if s.is_empty() {
        return Err(ParseNumericError::invalid());
    }

    let (integral, s) = eat_digits(s);

    let (fractional, exp, s) = match s.first() {
        Some(&b'e') | Some(&b'E') => {
            if integral.is_empty() {
                return Err(ParseNumericError::invalid());
            }

            let (exp, s) = extract_exponent(&s[1..])?;
            (b"".as_ref(), exp, s)
        }
        Some(&b'.') => {
            let (fractional, s) = eat_digits(&s[1..]);
            if integral.is_empty() && fractional.is_empty() {
                return Err(ParseNumericError::invalid());
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
                return Err(ParseNumericError::invalid());
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
pub fn eat_whitespaces(s: &[u8]) -> &[u8] {
    let mut i = 0;
    while i < s.len() && s[i].is_ascii_whitespace() {
        i += 1;
    }
    &s[i..]
}

/// Carves off decimal digits up to the first non-digit character.
pub fn eat_digits(s: &[u8]) -> (&[u8], &[u8]) {
    let mut i = 0;
    while i < s.len() && s[i].is_ascii_digit() {
        i += 1;
    }
    (&s[..i], &s[i..])
}

/// Extracts `NaN` value.
pub fn extract_nan(s: &[u8]) -> (bool, &[u8]) {
    if s.len() < 3 {
        (false, s)
    } else {
        if &s[0..3] == b"NaN" {
            (true, &s[3..])
        } else {
            (false, s)
        }
    }
}

/// Splits a decimal string bytes into sign and the rest, without inspecting or validating the rest.
pub fn extract_sign(s: &[u8]) -> (Sign, &[u8]) {
    match s.first() {
        Some(b'+') => (Sign::Positive, &s[1..]),
        Some(b'-') => (Sign::Negative, &s[1..]),
        _ => (Sign::Positive, s),
    }
}

/// Extracts exponent, if any.
pub fn extract_exponent(s: &[u8]) -> Result<(i32, &[u8]), ParseNumericError> {
    let (sign, s) = extract_sign(s);
    let (mut number, s) = eat_digits(s);

    if number.is_empty() {
        return Err(ParseNumericError::invalid());
    }

    while number.first() == Some(&b'0') {
        number = &number[1..];
    }

    if number.len() > 10 {
        return Err(ParseNumericError::overflow());
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
        return Err(ParseNumericError::overflow());
    }

    Ok((exp as i32, s))
}
