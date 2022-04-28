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

//! Numeric type modifier.

use crate::binary::VAR_HEADER_SIZE;
use crate::var::NUMERIC_MAX_PRECISION;
use std::fmt;

/// Type modifier.
///
/// For numeric, `Typmod` is composed by `precision` and `scale`.
/// They are converted into a internal integer value.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct Typmod(i32);

impl Typmod {
    /// Creates a `Typmod`.
    ///
    /// # Safety
    /// Callers have to guarantee that:
    /// * `1 <= precision <= NUMERIC_MAX_PRECISION`
    /// * `0 <= scale <= precision`
    #[inline]
    pub unsafe fn new_unchecked(precision: i32, scale: i32) -> Self {
        debug_assert!((1..=NUMERIC_MAX_PRECISION).contains(&precision));
        debug_assert!(scale >= 0 && scale <= precision);

        Typmod(((precision << 16) | scale) + VAR_HEADER_SIZE)
    }

    /// Creates a `Typmod`.
    /// `scale` defaults to zero.
    ///
    /// # Safety
    /// Callers have to guarantee that:
    /// * `1 <= precision <= NUMERIC_MAX_PRECISION`
    #[inline]
    pub unsafe fn with_precision_unchecked(precision: i32) -> Self {
        debug_assert!((1..=NUMERIC_MAX_PRECISION).contains(&precision));

        Typmod((precision << 16) + VAR_HEADER_SIZE)
    }

    /// Creates a `Typmod`.
    ///
    /// Returns `None`:
    /// * if `1 <= precision <= NUMERIC_MAX_PRECISION`
    /// * if `0 <= scale <= precision`
    #[inline]
    pub fn new(precision: i32, scale: i32) -> Option<Self> {
        if !(1..=NUMERIC_MAX_PRECISION).contains(&precision) || scale < 0 || scale > precision {
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
        if !(1..=NUMERIC_MAX_PRECISION).contains(&precision) {
            None
        } else {
            Some(unsafe { Self::with_precision_unchecked(precision) })
        }
    }

    /// Creates a `Typmod` from a `Typmod`'s value.
    ///
    /// # Safety
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
}
