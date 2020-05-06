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

//! Implementing operators for numeric.

use crate::num::{Numeric, NumericBuf, VALUE_OVERFLOW_MSG};
use std::cmp::Ordering;
use std::ops::{
    Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, RemAssign, Sub, SubAssign,
};

// The main implementation
// &self + &other
impl Add<&NumericBuf> for &NumericBuf {
    type Output = NumericBuf;

    #[inline]
    fn add(self, other: &NumericBuf) -> Self::Output {
        self.checked_add(other).expect(VALUE_OVERFLOW_MSG)
    }
}

// self + &other
impl Add<&NumericBuf> for NumericBuf {
    type Output = NumericBuf;

    #[inline]
    fn add(self, other: &NumericBuf) -> Self::Output {
        Add::add(&self, other)
    }
}

impl Add<&NumericBuf> for &Numeric {
    type Output = NumericBuf;

    #[inline]
    fn add(self, other: &NumericBuf) -> Self::Output {
        Add::add(self, other.as_numeric())
    }
}

// self + other
impl Add<NumericBuf> for NumericBuf {
    type Output = NumericBuf;

    #[inline]
    fn add(self, other: NumericBuf) -> Self::Output {
        Add::add(&self, &other)
    }
}

// &self + other
impl Add<NumericBuf> for &NumericBuf {
    type Output = NumericBuf;

    #[inline]
    fn add(self, other: NumericBuf) -> Self::Output {
        Add::add(self, &other)
    }
}

impl Add<NumericBuf> for &Numeric {
    type Output = NumericBuf;

    #[inline]
    fn add(self, other: NumericBuf) -> Self::Output {
        Add::add(self, other.as_numeric())
    }
}

impl Add<&Numeric> for &NumericBuf {
    type Output = NumericBuf;

    #[inline]
    fn add(self, other: &Numeric) -> Self::Output {
        Add::add(self.as_numeric(), other)
    }
}

impl Add<&Numeric> for NumericBuf {
    type Output = NumericBuf;

    #[inline]
    fn add(self, other: &Numeric) -> Self::Output {
        Add::add(self.as_numeric(), other)
    }
}

impl Add<&Numeric> for &Numeric {
    type Output = NumericBuf;

    #[inline]
    fn add(self, other: &Numeric) -> Self::Output {
        self.checked_add(other).expect(VALUE_OVERFLOW_MSG)
    }
}

// &mut self += &other
impl AddAssign<&NumericBuf> for NumericBuf {
    #[inline]
    fn add_assign(&mut self, other: &NumericBuf) {
        let result = Add::add(self as &NumericBuf, other);
        *self = result;
    }
}

// &mut self += other
impl AddAssign<NumericBuf> for NumericBuf {
    #[inline]
    fn add_assign(&mut self, other: NumericBuf) {
        let result = Add::add(self as &NumericBuf, &other);
        *self = result;
    }
}

impl AddAssign<&Numeric> for NumericBuf {
    #[inline]
    fn add_assign(&mut self, other: &Numeric) {
        let result = Add::add(self.as_numeric(), other);
        *self = result;
    }
}

// The main implementation
// &self - &other
impl Sub<&NumericBuf> for &NumericBuf {
    type Output = NumericBuf;

    #[inline]
    fn sub(self, other: &NumericBuf) -> Self::Output {
        self.checked_sub(other).expect(VALUE_OVERFLOW_MSG)
    }
}

// self - &other
impl Sub<&NumericBuf> for NumericBuf {
    type Output = NumericBuf;

    #[inline]
    fn sub(self, other: &NumericBuf) -> Self::Output {
        Sub::sub(&self, other)
    }
}

impl Sub<&NumericBuf> for &Numeric {
    type Output = NumericBuf;

    #[inline]
    fn sub(self, other: &NumericBuf) -> Self::Output {
        Sub::sub(self, other.as_numeric())
    }
}

// self - other
impl Sub<NumericBuf> for NumericBuf {
    type Output = NumericBuf;

    #[inline]
    fn sub(self, other: NumericBuf) -> Self::Output {
        Sub::sub(&self, &other)
    }
}

// &self - other
impl Sub<NumericBuf> for &NumericBuf {
    type Output = NumericBuf;

    #[inline]
    fn sub(self, other: NumericBuf) -> Self::Output {
        Sub::sub(self, &other)
    }
}

impl Sub<NumericBuf> for &Numeric {
    type Output = NumericBuf;

    #[inline]
    fn sub(self, other: NumericBuf) -> Self::Output {
        Sub::sub(self, other.as_numeric())
    }
}

impl Sub<&Numeric> for &Numeric {
    type Output = NumericBuf;

    #[inline]
    fn sub(self, other: &Numeric) -> Self::Output {
        self.checked_sub(other).expect(VALUE_OVERFLOW_MSG)
    }
}

impl Sub<&Numeric> for NumericBuf {
    type Output = NumericBuf;

    #[inline]
    fn sub(self, other: &Numeric) -> Self::Output {
        Sub::sub(self.as_numeric(), other)
    }
}

impl Sub<&Numeric> for &NumericBuf {
    type Output = NumericBuf;

    #[inline]
    fn sub(self, other: &Numeric) -> Self::Output {
        Sub::sub(self.as_numeric(), other)
    }
}

// &mut self -= &other
impl SubAssign<&NumericBuf> for NumericBuf {
    #[inline]
    fn sub_assign(&mut self, other: &NumericBuf) {
        let result = Sub::sub(self as &NumericBuf, other);
        *self = result;
    }
}

// &mut self -= other
impl SubAssign<NumericBuf> for NumericBuf {
    #[inline]
    fn sub_assign(&mut self, other: NumericBuf) {
        let result = Sub::sub(self as &NumericBuf, &other);
        *self = result;
    }
}

impl SubAssign<&Numeric> for NumericBuf {
    #[inline]
    fn sub_assign(&mut self, other: &Numeric) {
        let result = Sub::sub(self.as_numeric(), other);
        *self = result;
    }
}

// The main implementation
// &self * &other
impl Mul<&NumericBuf> for &NumericBuf {
    type Output = NumericBuf;

    #[inline]
    fn mul(self, other: &NumericBuf) -> Self::Output {
        self.checked_mul(other).expect(VALUE_OVERFLOW_MSG)
    }
}

// self * &other
impl Mul<&NumericBuf> for NumericBuf {
    type Output = NumericBuf;

    #[inline]
    fn mul(self, other: &NumericBuf) -> Self::Output {
        Mul::mul(&self, other)
    }
}

impl Mul<&NumericBuf> for &Numeric {
    type Output = NumericBuf;

    #[inline]
    fn mul(self, other: &NumericBuf) -> Self::Output {
        Mul::mul(self, other.as_numeric())
    }
}

// self * other
impl Mul<NumericBuf> for NumericBuf {
    type Output = NumericBuf;

    #[inline]
    fn mul(self, other: NumericBuf) -> Self::Output {
        Mul::mul(&self, &other)
    }
}

// &self * other
impl Mul<NumericBuf> for &NumericBuf {
    type Output = NumericBuf;

    #[inline]
    fn mul(self, other: NumericBuf) -> Self::Output {
        Mul::mul(self, &other)
    }
}

impl Mul<NumericBuf> for &Numeric {
    type Output = NumericBuf;

    #[inline]
    fn mul(self, other: NumericBuf) -> Self::Output {
        Mul::mul(self, other.as_numeric())
    }
}

impl Mul<&Numeric> for &Numeric {
    type Output = NumericBuf;

    #[inline]
    fn mul(self, other: &Numeric) -> Self::Output {
        self.checked_mul(other).expect(VALUE_OVERFLOW_MSG)
    }
}

impl Mul<&Numeric> for NumericBuf {
    type Output = NumericBuf;

    #[inline]
    fn mul(self, other: &Numeric) -> Self::Output {
        Mul::mul(self.as_numeric(), other)
    }
}

impl Mul<&Numeric> for &NumericBuf {
    type Output = NumericBuf;

    #[inline]
    fn mul(self, other: &Numeric) -> Self::Output {
        Mul::mul(self.as_numeric(), other)
    }
}

// &mut self *= &other
impl MulAssign<&NumericBuf> for NumericBuf {
    #[inline]
    fn mul_assign(&mut self, other: &NumericBuf) {
        let result = Mul::mul(self as &NumericBuf, other);
        *self = result;
    }
}

// &mut self *= other
impl MulAssign<NumericBuf> for NumericBuf {
    #[inline]
    fn mul_assign(&mut self, other: NumericBuf) {
        let result = Mul::mul(self as &NumericBuf, &other);
        *self = result;
    }
}

impl MulAssign<&Numeric> for NumericBuf {
    #[inline]
    fn mul_assign(&mut self, other: &Numeric) {
        let result = Mul::mul(self.as_numeric(), other);
        *self = result;
    }
}

// The main implementation
// &self / &other
impl Div<&NumericBuf> for &NumericBuf {
    type Output = NumericBuf;

    #[inline]
    fn div(self, other: &NumericBuf) -> Self::Output {
        let (result, overflow) = self.overflowing_div(other);
        if overflow {
            panic!(VALUE_OVERFLOW_MSG)
        }

        result
    }
}

// self / &other
impl Div<&NumericBuf> for NumericBuf {
    type Output = NumericBuf;

    #[inline]
    fn div(self, other: &NumericBuf) -> Self::Output {
        Div::div(&self, other)
    }
}

impl Div<&NumericBuf> for &Numeric {
    type Output = NumericBuf;

    #[inline]
    fn div(self, other: &NumericBuf) -> Self::Output {
        Div::div(self, other.as_numeric())
    }
}

// &self / other
impl Div<NumericBuf> for &NumericBuf {
    type Output = NumericBuf;

    #[inline]
    fn div(self, other: NumericBuf) -> Self::Output {
        Div::div(self, &other)
    }
}

// self / other
impl Div<NumericBuf> for NumericBuf {
    type Output = NumericBuf;

    #[inline]
    fn div(self, other: NumericBuf) -> Self::Output {
        Div::div(&self, &other)
    }
}

impl Div<NumericBuf> for &Numeric {
    type Output = NumericBuf;

    #[inline]
    fn div(self, other: NumericBuf) -> Self::Output {
        Div::div(self, other.as_numeric())
    }
}

impl Div<&Numeric> for &NumericBuf {
    type Output = NumericBuf;

    #[inline]
    fn div(self, other: &Numeric) -> Self::Output {
        Div::div(self.as_numeric(), other)
    }
}

impl Div<&Numeric> for NumericBuf {
    type Output = NumericBuf;

    #[inline]
    fn div(self, other: &Numeric) -> Self::Output {
        Div::div(self.as_numeric(), other)
    }
}

impl Div<&Numeric> for &Numeric {
    type Output = NumericBuf;

    #[inline]
    fn div(self, other: &Numeric) -> Self::Output {
        let (result, overflow) = self.overflowing_div(other);
        if overflow {
            panic!(VALUE_OVERFLOW_MSG)
        }

        result
    }
}

// &mut self /= &other
impl DivAssign<&NumericBuf> for NumericBuf {
    #[inline]
    fn div_assign(&mut self, other: &NumericBuf) {
        let result = Div::div(self as &NumericBuf, other);
        *self = result;
    }
}

// &mut self /= other
impl DivAssign<NumericBuf> for NumericBuf {
    #[inline]
    fn div_assign(&mut self, other: NumericBuf) {
        let result = Div::div(self as &NumericBuf, &other);
        *self = result;
    }
}

impl DivAssign<&Numeric> for NumericBuf {
    #[inline]
    fn div_assign(&mut self, other: &Numeric) {
        let result = Div::div(self.as_numeric(), other);
        *self = result;
    }
}

// The main implementation
// &self % &other
impl Rem<&NumericBuf> for &NumericBuf {
    type Output = NumericBuf;

    #[inline]
    fn rem(self, other: &NumericBuf) -> Self::Output {
        let (result, overflow) = self.overflowing_rem(other);
        if overflow {
            panic!(VALUE_OVERFLOW_MSG)
        }

        result
    }
}

// self % &other
impl Rem<&NumericBuf> for NumericBuf {
    type Output = NumericBuf;

    #[inline]
    fn rem(self, other: &NumericBuf) -> Self::Output {
        Rem::rem(&self, other)
    }
}

impl Rem<&NumericBuf> for &Numeric {
    type Output = NumericBuf;

    #[inline]
    fn rem(self, other: &NumericBuf) -> Self::Output {
        Rem::rem(self, other.as_numeric())
    }
}

// &self % other
impl Rem<NumericBuf> for &NumericBuf {
    type Output = NumericBuf;

    #[inline]
    fn rem(self, other: NumericBuf) -> Self::Output {
        Rem::rem(self, &other)
    }
}

// self % other
impl Rem<NumericBuf> for NumericBuf {
    type Output = NumericBuf;

    #[inline]
    fn rem(self, other: NumericBuf) -> Self::Output {
        Rem::rem(&self, &other)
    }
}

impl Rem<NumericBuf> for &Numeric {
    type Output = NumericBuf;

    #[inline]
    fn rem(self, other: NumericBuf) -> Self::Output {
        Rem::rem(self, other.as_numeric())
    }
}

impl Rem<&Numeric> for &NumericBuf {
    type Output = NumericBuf;

    #[inline]
    fn rem(self, other: &Numeric) -> Self::Output {
        Rem::rem(self.as_numeric(), other)
    }
}

impl Rem<&Numeric> for NumericBuf {
    type Output = NumericBuf;

    #[inline]
    fn rem(self, other: &Numeric) -> Self::Output {
        Rem::rem(self.as_numeric(), other)
    }
}

impl Rem<&Numeric> for &Numeric {
    type Output = NumericBuf;

    #[inline]
    fn rem(self, other: &Numeric) -> Self::Output {
        let (result, overflow) = self.overflowing_rem(other);
        if overflow {
            panic!(VALUE_OVERFLOW_MSG)
        }

        result
    }
}

// &mut self %= &other
impl RemAssign<&NumericBuf> for NumericBuf {
    #[inline]
    fn rem_assign(&mut self, other: &NumericBuf) {
        let result = Rem::rem(self as &NumericBuf, other);
        *self = result;
    }
}

// &mut self %= other
impl RemAssign<NumericBuf> for NumericBuf {
    #[inline]
    fn rem_assign(&mut self, other: NumericBuf) {
        let result = Rem::rem(self as &NumericBuf, &other);
        *self = result;
    }
}

impl RemAssign<&Numeric> for NumericBuf {
    #[inline]
    fn rem_assign(&mut self, other: &Numeric) {
        let result = Rem::rem(self.as_numeric(), other);
        *self = result;
    }
}

// -self
impl Neg for NumericBuf {
    type Output = NumericBuf;

    #[inline]
    fn neg(mut self) -> Self::Output {
        self.negate_mut();
        self
    }
}

// -&self
impl Neg for &NumericBuf {
    type Output = NumericBuf;

    #[inline]
    fn neg(self) -> Self::Output {
        self.negate()
    }
}

impl Neg for &Numeric {
    type Output = NumericBuf;

    #[inline]
    fn neg(self) -> Self::Output {
        self.negate()
    }
}

impl PartialEq<NumericBuf> for NumericBuf {
    #[inline]
    fn eq(&self, other: &NumericBuf) -> bool {
        Ord::cmp(self, other) == Ordering::Equal
    }
}

impl Eq for NumericBuf {}

impl PartialOrd<NumericBuf> for NumericBuf {
    #[inline]
    fn partial_cmp(&self, other: &NumericBuf) -> Option<Ordering> {
        Some(Ord::cmp(self, other))
    }
}

impl Ord for NumericBuf {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        Numeric::cmp(self, other)
    }
}

impl PartialEq<Numeric> for Numeric {
    #[inline]
    fn eq(&self, other: &Numeric) -> bool {
        Ord::cmp(self, other) == Ordering::Equal
    }
}

impl Eq for Numeric {}

impl PartialOrd<Numeric> for Numeric {
    #[inline]
    fn partial_cmp(&self, other: &Numeric) -> Option<Ordering> {
        Some(Ord::cmp(self, other))
    }
}

impl Ord for Numeric {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        Numeric::cmp(self, other)
    }
}

impl PartialEq<Numeric> for NumericBuf {
    #[inline]
    fn eq(&self, other: &Numeric) -> bool {
        self.as_numeric() == other
    }
}

impl PartialEq<&Numeric> for NumericBuf {
    #[inline]
    fn eq(&self, other: &&Numeric) -> bool {
        self.as_numeric() == *other
    }
}

impl PartialEq<NumericBuf> for Numeric {
    #[inline]
    fn eq(&self, other: &NumericBuf) -> bool {
        self == other.as_numeric()
    }
}

impl PartialEq<NumericBuf> for &Numeric {
    #[inline]
    fn eq(&self, other: &NumericBuf) -> bool {
        *self == other.as_numeric()
    }
}

impl PartialOrd<Numeric> for NumericBuf {
    #[inline]
    fn partial_cmp(&self, other: &Numeric) -> Option<Ordering> {
        self.as_numeric().partial_cmp(other)
    }
}

impl PartialOrd<&Numeric> for NumericBuf {
    #[inline]
    fn partial_cmp(&self, other: &&Numeric) -> Option<Ordering> {
        self.as_numeric().partial_cmp(*other)
    }
}

impl PartialOrd<NumericBuf> for Numeric {
    #[inline]
    fn partial_cmp(&self, other: &NumericBuf) -> Option<Ordering> {
        self.partial_cmp(other.as_numeric())
    }
}

impl PartialOrd<NumericBuf> for &Numeric {
    #[inline]
    fn partial_cmp(&self, other: &NumericBuf) -> Option<Ordering> {
        (*self).partial_cmp(other.as_numeric())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::ops::Deref;

    // use this function to test `as_bytes` in ops.
    fn transform(val: &NumericBuf) -> &Numeric {
        val.deref()
    }

    fn assert_add(val1: &str, val2: &str, expected: &str) {
        let var1 = val1.parse::<NumericBuf>().unwrap();
        let var2 = val2.parse::<NumericBuf>().unwrap();

        let result1 = &var1 + &var2;
        assert_eq!(transform(&result1).to_string(), expected);

        let result2 = &var2 + &var1;
        assert_eq!(transform(&result2).to_string(), expected);

        let mut result3 = var1.clone();
        result3 += &var2;
        assert_eq!(transform(&result3).to_string(), expected);

        let mut result4 = var2.clone();
        result4 += &var1;
        assert_eq!(transform(&result4).to_string(), expected);
    }

    #[test]
    fn add() {
        assert_add("NaN", "10000.00001", "NaN");
        assert_add("NaN", "00000.00000", "NaN");
        assert_add("NaN", "-10000.00001", "NaN");
        assert_add("0.000000001", "100000000", "100000000.000000001");
        assert_add("123456789.987654321", "-123456789.987654321", "0.000000000");
        assert_add("987654321.123456789", "-987654321.123456789", "0.000000000");
        assert_add(
            "123456789.987654321",
            "987654321.123456789",
            "1111111111.111111110",
        );
        assert_add("123456789.987654321", "00000.00000", "123456789.987654321");
        assert_add(
            "123456789.987654321",
            "-987654321.123456789",
            "-864197531.135802468",
        );
        assert_add("00000.00000", "987654321.123456789", "987654321.123456789");
        assert_add("00000.00000", "00000.00000", "0.00000");
        assert_add(
            "00000.00000",
            "-987654321.123456789",
            "-987654321.123456789",
        );
        assert_add(
            "-123456789.987654321",
            "987654321.123456789",
            "864197531.135802468",
        );
        assert_add(
            "-123456789.987654321",
            "00000.00000",
            "-123456789.987654321",
        );
        assert_add(
            "-123456789.987654321",
            "-987654321.123456789",
            "-1111111111.111111110",
        );
    }

    fn assert_sub(val1: &str, val2: &str, expected1: &str, expected2: &str) {
        let var1 = val1.parse::<NumericBuf>().unwrap();
        let var2 = val2.parse::<NumericBuf>().unwrap();

        let result1 = &var1 - &var2;
        assert_eq!(transform(&result1).to_string(), expected1);

        let result2 = &var2 - &var1;
        assert_eq!(transform(&result2).to_string(), expected2);

        let mut result3 = var1.clone();
        result3 -= &var2;
        assert_eq!(transform(&result3).to_string(), expected1);

        let mut result4 = var2.clone();
        result4 -= &var1;
        assert_eq!(transform(&result4).to_string(), expected2);
    }

    #[test]
    fn sub() {
        assert_sub("NaN", "10000.00001", "NaN", "NaN");
        assert_sub("NaN", "00000.00000", "NaN", "NaN");
        assert_sub("NaN", "-10000.00001", "NaN", "NaN");
        assert_sub(
            "0.000000001",
            "100000000",
            "-99999999.999999999",
            "99999999.999999999",
        );
        assert_sub(
            "123456789.987654321",
            "123456789.987654321",
            "0.000000000",
            "0.000000000",
        );
        assert_sub(
            "987654321.123456789",
            "987654321.123456789",
            "0.000000000",
            "0.000000000",
        );
        assert_sub(
            "123456789.987654321",
            "987654321.123456789",
            "-864197531.135802468",
            "864197531.135802468",
        );
        assert_sub(
            "123456789.987654321",
            "00000.00000",
            "123456789.987654321",
            "-123456789.987654321",
        );
        assert_sub(
            "123456789.987654321",
            "-987654321.123456789",
            "1111111111.111111110",
            "-1111111111.111111110",
        );
        assert_sub(
            "00000.00000",
            "987654321.123456789",
            "-987654321.123456789",
            "987654321.123456789",
        );
        assert_sub("00000.00000", "00000.00000", "0.00000", "0.00000");
        assert_sub(
            "00000.00000",
            "-987654321.123456789",
            "987654321.123456789",
            "-987654321.123456789",
        );
        assert_sub(
            "-123456789.987654321",
            "987654321.123456789",
            "-1111111111.111111110",
            "1111111111.111111110",
        );
        assert_sub(
            "-123456789.987654321",
            "00000.00000",
            "-123456789.987654321",
            "123456789.987654321",
        );
        assert_sub(
            "-123456789.987654321",
            "-987654321.123456789",
            "864197531.135802468",
            "-864197531.135802468",
        );
    }

    fn assert_mul(val1: &str, val2: &str, expected: &str) {
        let var1 = val1.parse::<NumericBuf>().unwrap();
        let var2 = val2.parse::<NumericBuf>().unwrap();

        let result1 = &var1 * &var2;
        assert_eq!(transform(&result1).to_string(), expected);

        let result2 = &var2 * &var1;
        assert_eq!(transform(&result2).to_string(), expected);

        let mut result3 = var1.clone();
        result3 *= &var2;
        assert_eq!(transform(&result3).to_string(), expected);

        let mut result4 = var2.clone();
        result4 *= &var1;
        assert_eq!(transform(&result4).to_string(), expected);
    }

    #[test]
    fn mul() {
        assert_mul("NaN", "10000.00001", "NaN");
        assert_mul("NaN", "00000.00000", "NaN");
        assert_mul("NaN", "-10000.00001", "NaN");
        assert_mul("0.000000001", "100000000", "0.100000000");
        assert_mul(
            "123456789.987654321",
            "-123456789.987654321",
            "-15241578994055784.200731595789971041",
        );
        assert_mul(
            "987654321.123456789",
            "-987654321.123456789",
            "-975461058033836303.240512116750190521",
        );
        assert_mul(
            "123456789.987654321",
            "987654321.123456789",
            "121932632103337905.662094193112635269",
        );
        assert_mul("123456789.987654321", "00000.00000", "0.00000000000000");
        assert_mul(
            "123456789.987654321",
            "-987654321.123456789",
            "-121932632103337905.662094193112635269",
        );
        assert_mul("00000.00000", "987654321.123456789", "0.00000000000000");
        assert_mul("00000.00000", "00000.00000", "0.0000000000");
        assert_mul("00000.00000", "-987654321.123456789", "0.00000000000000");
        assert_mul(
            "-123456789.987654321",
            "987654321.123456789",
            "-121932632103337905.662094193112635269",
        );
        assert_mul("-123456789.987654321", "00000.00000", "0.00000000000000");
        assert_mul(
            "-123456789.987654321",
            "-987654321.123456789",
            "121932632103337905.662094193112635269",
        );
    }

    fn assert_div(val1: &str, val2: &str, expected: &str) {
        let var1 = val1.parse::<NumericBuf>().unwrap();
        let var2 = val2.parse::<NumericBuf>().unwrap();

        let result1 = &var1 / &var2;
        assert_eq!(transform(&result1).to_string(), expected);

        let mut result2 = var1.clone();
        result2 /= &var2;
        assert_eq!(transform(&result2).to_string(), expected);
    }

    #[test]
    fn div() {
        assert_div("NaN", "10000.00001", "NaN");
        assert_div("NaN", "00000.00000", "NaN");
        assert_div("NaN", "-10000.00001", "NaN");
        assert_div("10000.00001", "NaN", "NaN");
        assert_div("00000.00000", "NaN", "NaN");
        assert_div("-10000.00001", "NaN", "NaN");
        assert_div("NaN", "NaN", "NaN");
        assert_div(
            "0.000000001",
            "100000000",
            "0.000000000000000010000000000000000000",
        );
        assert_div("100000000", "0.000000001", "100000000000000000.000000000");
        assert_div(
            "123456789.987654321",
            "123456789.987654321",
            "1.00000000000000000000",
        );
        assert_div(
            "987654321.123456789",
            "987654321.123456789",
            "1.00000000000000000000",
        );
        assert_div(
            "123456789.987654321",
            "987654321.123456789",
            "0.12499999984531250018",
        );
        assert_div(
            "987654321.123456789",
            "123456789.987654321",
            "8.0000000099000000",
        );
        assert_div(
            "00000.00000",
            "123456789.987654321",
            "0.0000000000000000000000000000",
        );
        assert_div(
            "123456789.987654321",
            "-987654321.123456789",
            "-0.12499999984531250018",
        );
        assert_div(
            "-987654321.123456789",
            "123456789.987654321",
            "-8.0000000099000000",
        );
        assert_div(
            "00000.00000",
            "987654321.123456789",
            "0.0000000000000000000000000000",
        );
        assert_div(
            "00000.00000",
            "-987654321.123456789",
            "0.0000000000000000000000000000",
        );
        assert_div(
            "-123456789.987654321",
            "987654321.123456789",
            "-0.12499999984531250018",
        );
        assert_div(
            "987654321.123456789",
            "-123456789.987654321",
            "-8.0000000099000000",
        );
        assert_div(
            "00000.00000",
            "-123456789.987654321",
            "0.0000000000000000000000000000",
        );
        assert_div(
            "-123456789.987654321",
            "-987654321.123456789",
            "0.12499999984531250018",
        );
        assert_div(
            "-987654321.123456789",
            "-123456789.987654321",
            "8.0000000099000000",
        );
    }

    #[test]
    #[should_panic(expected = "attempt to divide by zero")]
    fn div_by_zero() {
        assert_div("1", "0", "");
    }

    fn assert_rem(val1: &str, val2: &str, expected: &str) {
        let var1 = val1.parse::<NumericBuf>().unwrap();
        let var2 = val2.parse::<NumericBuf>().unwrap();

        let result1 = &var1 % &var2;
        assert_eq!(transform(&result1).to_string(), expected);

        let mut result2 = var1.clone();
        result2 %= &var2;
        assert_eq!(transform(&result2).to_string(), expected);
    }

    #[test]
    fn rem() {
        assert_rem("NaN", "10000.00001", "NaN");
        assert_rem("NaN", "00000.00000", "NaN");
        assert_rem("NaN", "-10000.00001", "NaN");
        assert_rem("10000.00001", "NaN", "NaN");
        assert_rem("00000.00000", "NaN", "NaN");
        assert_rem("-10000.00001", "NaN", "NaN");
        assert_rem("NaN", "NaN", "NaN");
        assert_rem("0.000000001", "100000000", "0.000000001");
        assert_rem("100000000", "0.000000001", "0.000000000");
        assert_rem("123456789.987654321", "123456789.987654321", "0.000000000");
        assert_rem("987654321.123456789", "987654321.123456789", "0.000000000");
        assert_rem(
            "123456789.987654321",
            "987654321.123456789",
            "123456789.987654321",
        );
        assert_rem("987654321.123456789", "123456789.987654321", "1.222222221");
        assert_rem("00000.00000", "123456789.987654321", "0.000000000");
        assert_rem(
            "123456789.987654321",
            "-987654321.123456789",
            "123456789.987654321",
        );
        assert_rem(
            "-987654321.123456789",
            "123456789.987654321",
            "-1.222222221",
        );
        assert_rem("00000.00000", "987654321.123456789", "0.000000000");
        assert_rem("00000.00000", "-987654321.123456789", "0.000000000");
        assert_rem(
            "-123456789.987654321",
            "987654321.123456789",
            "-123456789.987654321",
        );
        assert_rem("987654321.123456789", "-123456789.987654321", "1.222222221");
        assert_rem("00000.00000", "-123456789.987654321", "0.000000000");
        assert_rem(
            "-123456789.987654321",
            "-987654321.123456789",
            "-123456789.987654321",
        );
        assert_rem(
            "-987654321.123456789",
            "-123456789.987654321",
            "-1.222222221",
        );
    }

    #[test]
    #[should_panic(expected = "attempt to divide by zero")]
    fn rem_div_by_zero() {
        assert_rem("1", "0", "");
    }

    macro_rules! assert_cmp {
        ($left: expr, $cmp: tt, $right: expr) => {{
            let left = $left.parse::<NumericBuf>().unwrap();
            let right = $right.parse::<NumericBuf>().unwrap();
            assert!(left $cmp right, "left = {}, right = {}", left, right);
        }};
    }

    fn assert_ord(val1: &str, val2: &str, expected: &str) {
        let var1 = val1.parse::<NumericBuf>().unwrap();
        let var2 = val2.parse::<NumericBuf>().unwrap();

        let result = std::cmp::max(var1, var2);
        assert_eq!(transform(&result).to_string(), expected);
    }

    #[test]
    fn cmp() {
        assert_cmp!("NaN", ==, "NaN");
        assert_cmp!("NaN", >, "1e100000");
        assert_cmp!("NaN", >, "00000.00000");
        assert_cmp!("NaN", >, "-1e100000");
        assert_cmp!("1e100000", <, "NaN");
        assert_cmp!("00000.00000", <, "NaN");
        assert_cmp!("-1e100000", <, "NaN");
        assert_cmp!("00000.00000", ==, "0");
        assert_cmp!("0.000000001", <,"100000000");
        assert_cmp!("100000000", >, "0.000000001");
        assert_cmp!("123456789.987654321", ==, "123456789.987654321");
        assert_cmp!("987654321.123456789", ==, "987654321.123456789");
        assert_cmp!("123456789.987654321", <, "987654321.123456789");
        assert_cmp!("987654321.123456789", >, "123456789.987654321");
        assert_cmp!("00000.00000", <, "123456789.987654321");
        assert_cmp!("123456789.987654321", >, "-987654321.123456789");
        assert_cmp!("-987654321.123456789", <, "123456789.987654321");
        assert_cmp!("00000.00000", <, "987654321.123456789");
        assert_cmp!("00000.00000", >, "-987654321.123456789");
        assert_cmp!("-123456789.987654321", <, "987654321.123456789");
        assert_cmp!("987654321.123456789", >, "-123456789.987654321");
        assert_cmp!("00000.00000", >, "-123456789.987654321");
        assert_cmp!("-123456789.987654321", >, "-987654321.123456789");
        assert_cmp!("-987654321.123456789", <, "-123456789.987654321");
        assert_cmp!("1.0e-10000", >=, "1.0e-10001");
        assert_cmp!("1.0e-10001", <=, "1.0e-10000");
        assert_cmp!("1.0e-10000", !=, "1.0e-10001");
        assert_cmp!("1.0e100000", <=, "1.0e100001");
        assert_cmp!("1.0e100001", >=, "1.0e100000");
        assert_cmp!("1.0e100000", !=, "1.0e100001");

        assert_ord("NaN", "1e100000", "NaN");
        assert_ord(
            "123456789.987654321",
            "987654321.123456789",
            "987654321.123456789",
        );
    }

    fn assert_neg(val: &str, expected: &str) {
        let var = val.parse::<NumericBuf>().unwrap();
        let expected_var = expected.parse::<NumericBuf>().unwrap();
        assert_eq!(transform(&-&var), expected_var.as_numeric());
    }

    #[test]
    fn neg() {
        assert_neg("NaN", "NaN");
        assert_neg("00000.00000", "0.00000");
        assert_neg("1.0", "-1.0");
        assert_neg("-1.0", "1.0");
        assert_neg("1.23e10", "-1.23e10");
        assert_neg("-1.23e10", "1.23e10");
    }
}
