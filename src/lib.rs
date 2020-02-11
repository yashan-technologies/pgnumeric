// Copyright 2020 CoD Team

//! Arbitrary precision numeric, compatible with PostgreSQL's numeric.

mod convert;
mod error;
mod parse;

pub use crate::convert::TryFromRef;
pub use crate::error::NumericParseError;
pub use crate::error::NumericTryFromError;

use crate::parse::{parse_decimal, Decimal};
use std::fmt;

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
        &self.buf.as_slice()[self.offset..self.offset + self.ndigits as usize]
    }

    /// Returns mutable digits buffer.
    #[inline]
    fn digits_mut(&mut self) -> &mut [NumericDigit] {
        debug_assert_eq!(self.buf.len(), self.offset + self.ndigits as usize);
        &mut self.buf.as_mut_slice()[self.offset..self.offset + self.ndigits as usize]
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
