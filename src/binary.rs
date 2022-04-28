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

//! Numeric binary representation.

// The Numeric type as stored on disk.
//
// If the high bits of the first word of a NumericChoice (n_header, or
// n_short.n_header, or n_long.n_sign_dscale) are NUMERIC_SHORT, then the
// numeric follows the NumericShort format; if they are NUMERIC_POS or
// NUMERIC_NEG, it follows the NumericLong format.  If they are NUMERIC_NAN,
// it is a NaN.  We currently always store a NaN using just two bytes (i.e.
// only n_header), but previous releases used only the NumericLong format,
// so we might find 4-byte NaNs on disk if a database has been migrated using
// pg_upgrade.  In either case, when the high bits indicate a NaN, the
// remaining bits are never examined.  Currently, we always initialize these
// to zero, but it might be possible to use them for some other purpose in
// the future.
//
// In the NumericShort format, the remaining 14 bits of the header word
// (n_short.n_header) are allocated as follows: 1 for sign (positive or
// negative), 6 for dynamic scale, and 7 for weight.  In practice, most
// commonly-encountered values can be represented this way.
//
// In the NumericLong format, the remaining 14 bits of the header word
// (n_long.n_sign_dscale) represent the display scale; and the weight is
// stored separately in n_weight.
//
// NOTE: by convention, values in the packed form have been stripped of
// all leading and trailing zero digits (where a "digit" is of base NBASE).
// In particular, if the value is zero, there will be no digits at all!
// The weight is arbitrary in that case, but we normally set it to zero.

use crate::var::NumericVar;
use cfg_if::cfg_if;
use std::marker::PhantomData;
use std::mem::size_of;

/// Use `i16` to represent a numeric digit.
pub type NumericDigit = i16;

/// Size of numeric digit.
pub const NUMERIC_DIGIT_SIZE: u32 = size_of::<NumericDigit>() as u32;

pub const VAR_HEADER_SIZE: i32 = size_of::<i32>() as i32;
pub const NUMERIC_HEADER_SIZE: usize =
    VAR_HEADER_SIZE as usize + size_of::<u16>() + size_of::<i16>();
pub const NUMERIC_HEADER_SIZE_SHORT: usize = VAR_HEADER_SIZE as usize + size_of::<u16>();
pub const NUMERIC_HEADER_NDIGITS: u32 =
    (NUMERIC_HEADER_SIZE as u32 + NUMERIC_DIGIT_SIZE - 1) / NUMERIC_DIGIT_SIZE;

// Interpretation of high bits.
pub const NUMERIC_SIGN_MASK: u16 = 0xC000;
pub const NUMERIC_POS: u16 = 0x0000;
pub const NUMERIC_NEG: u16 = 0x4000;
pub const NUMERIC_SHORT: u16 = 0x8000;
pub const NUMERIC_NAN: u16 = 0xC000;

// Short format definitions.
const NUMERIC_SHORT_SIGN_MASK: u16 = 0x2000;
const NUMERIC_SHORT_DSCALE_MASK: u16 = 0x1F80;
const NUMERIC_SHORT_DSCALE_SHIFT: u16 = 7;
const NUMERIC_SHORT_DSCALE_MAX: u16 = NUMERIC_SHORT_DSCALE_MASK >> NUMERIC_SHORT_DSCALE_SHIFT;
const NUMERIC_SHORT_WEIGHT_SIGN_MASK: u16 = 0x0040;
const NUMERIC_SHORT_WEIGHT_MASK: u16 = 0x003F;
const NUMERIC_SHORT_WEIGHT_MAX: i16 = NUMERIC_SHORT_WEIGHT_MASK as i16;
const NUMERIC_SHORT_WEIGHT_MIN: i16 = (-(NUMERIC_SHORT_WEIGHT_MASK as i32 + 1)) as i16;

const NUMERIC_DSCALE_MASK: u16 = 0x3FFF;

pub const NUMERIC_WEIGHT_MAX: i16 = i16::max_value();
pub const NUMERIC_WEIGHT_MIN: i16 = -NUMERIC_WEIGHT_MAX;
pub const NUMERIC_DSCALE_MAX: i16 = 0x3FFF;

/// A flexible array.
#[repr(C)]
#[derive(Debug)]
struct FlexArray<T>(PhantomData<T>, [T; 0]);

impl<T> FlexArray<T> {
    #[inline]
    pub fn as_ptr(&self) -> *const T {
        self as *const _ as *const T
    }

    #[inline]
    pub unsafe fn as_slice(&self, len: usize) -> &[T] {
        std::slice::from_raw_parts(self.as_ptr(), len)
    }
}

/// A `union` field.
#[repr(C)]
#[derive(Debug)]
struct UnionField<T>(PhantomData<T>);

impl<T> UnionField<T> {
    #[inline]
    pub const fn new() -> Self {
        Self(PhantomData)
    }

    #[inline]
    pub unsafe fn as_ref(&self) -> &T {
        &*(self as *const _ as *const T)
    }

    #[inline]
    pub unsafe fn as_mut(&mut self) -> &mut T {
        &mut *(self as *mut _ as *mut T)
    }
}

#[repr(C)]
pub(crate) struct NumericShort {
    // Sign + display scale + weight
    n_header: u16,

    // Digits
    n_data: FlexArray<NumericDigit>,
}

impl NumericShort {
    #[inline]
    pub fn set_header(&mut self, weight: i16, dscale: u16, sign: u16) {
        if sign == NUMERIC_NAN {
            debug_assert_eq!(weight, 0);
            debug_assert_eq!(dscale, 0);
            self.n_header = NUMERIC_NAN;
            return;
        }

        let s = if sign == NUMERIC_NEG {
            NUMERIC_SHORT | NUMERIC_SHORT_SIGN_MASK
        } else {
            NUMERIC_SHORT
        };
        let ds = dscale << NUMERIC_SHORT_DSCALE_SHIFT;
        let ws = if weight < 0 {
            NUMERIC_SHORT_WEIGHT_SIGN_MASK
        } else {
            0
        };
        let w = (weight & NUMERIC_SHORT_WEIGHT_MASK as i16) as u16;
        self.n_header = s | ds | ws | w;
    }
}

#[repr(C)]
pub(crate) struct NumericLong {
    // Sign + display scale
    n_sign_dscale: u16,

    // Weight of 1st digit
    n_weight: i16,

    // Digits
    n_data: FlexArray<NumericDigit>,
}

impl NumericLong {
    #[inline]
    pub fn set_header(&mut self, weight: i16, dscale: u16, sign: u16) {
        self.n_sign_dscale = sign | (dscale & NUMERIC_DSCALE_MASK);
        self.n_weight = weight;
    }
}

/// `NumericChoice` is a `union` in PostgreSQL.
/// Here we use `UnionField` to simulate it.
#[repr(C)]
struct NumericChoice {
    // Header word
    n_header: UnionField<u16>,

    // Long form (4-byte header)
    n_long: UnionField<NumericLong>,

    // Short form (2-byte header)
    n_short: UnionField<NumericShort>,

    // 4-byte header for union
    _data: [u16; 2],
}

impl NumericChoice {
    #[inline]
    fn n_header(&self) -> u16 {
        unsafe { *(self.n_header.as_ref()) }
    }

    #[inline]
    pub fn flag_bits(&self) -> u16 {
        self.n_header() & NUMERIC_SIGN_MASK
    }

    #[inline]
    pub fn is_nan(&self) -> bool {
        self.flag_bits() == NUMERIC_NAN
    }

    #[inline]
    pub fn is_short(&self) -> bool {
        self.flag_bits() == NUMERIC_SHORT
    }

    /// If the flag bits are `NUMERIC_SHORT` or `NUMERIC_NAN`, we want the short header;
    /// otherwise, we want the long one.  Instead of testing against each value, we
    /// can just look at the high bit, for a slight efficiency gain.
    #[inline]
    pub fn header_is_short(&self) -> bool {
        (self.n_header() & 0x8000) != 0
    }

    #[inline]
    pub fn header_size(&self) -> u32 {
        if self.header_is_short() {
            NUMERIC_HEADER_SIZE_SHORT as u32
        } else {
            NUMERIC_HEADER_SIZE as u32
        }
    }

    #[inline]
    pub fn sign(&self) -> u16 {
        if self.is_short() {
            if (self.n_header() & NUMERIC_SHORT_SIGN_MASK) != 0 {
                NUMERIC_NEG
            } else {
                NUMERIC_POS
            }
        } else {
            self.flag_bits()
        }
    }

    #[inline]
    pub fn dscale(&self) -> u16 {
        unsafe {
            if self.header_is_short() {
                (self.n_short.as_ref().n_header & NUMERIC_SHORT_DSCALE_MASK)
                    >> NUMERIC_SHORT_DSCALE_SHIFT
            } else {
                self.n_long.as_ref().n_sign_dscale & NUMERIC_DSCALE_MASK
            }
        }
    }

    #[inline]
    fn weight_short(&self) -> i16 {
        debug_assert!(self.header_is_short());
        let weight_sign =
            unsafe { self.n_short.as_ref().n_header & NUMERIC_SHORT_WEIGHT_SIGN_MASK };
        let weight = unsafe { self.n_short.as_ref().n_header & NUMERIC_SHORT_WEIGHT_MASK };
        if weight_sign != 0 {
            ((!NUMERIC_SHORT_WEIGHT_MASK) | weight) as i16
        } else {
            weight as i16
        }
    }

    #[inline]
    fn weight_long(&self) -> i16 {
        debug_assert!(!self.header_is_short());
        unsafe { self.n_long.as_ref().n_weight }
    }

    #[inline]
    pub fn weight(&self) -> i16 {
        if self.header_is_short() {
            self.weight_short()
        } else {
            self.weight_long()
        }
    }
}

/// `NumericBinary` is used to represent binary format of disk storage.
/// Notes that do not create a `NumericBinary` directly.
#[repr(C)]
pub(crate) struct NumericBinary {
    // varlena header (do not touch directly!)
    // xxxxxx00 4-byte length word, aligned, uncompressed data (up to 1G)
    // see also postgres.h
    vl_len: u32,

    // choice of format
    choice: NumericChoice,
}

impl NumericBinary {
    #[inline]
    pub fn can_be_short(weight: i16, dscale: u16) -> bool {
        dscale <= NUMERIC_SHORT_DSCALE_MAX
            && weight <= NUMERIC_SHORT_WEIGHT_MAX
            && weight >= NUMERIC_SHORT_WEIGHT_MIN
    }

    #[inline]
    const fn encode_len(len: u32) -> u32 {
        cfg_if! {
            if #[cfg(feature = "big-endian-varlen")] {
                (len & 0x3FFF_FFFF).to_be()
            } else {
                len << 2
            }
        }
    }

    #[inline]
    const fn decode_len(len: u32) -> u32 {
        cfg_if! {
            if #[cfg(feature = "big-endian-varlen")] {
                u32::from_be(len) & 0x3FFF_FFFF
            } else {
                (len >> 2) & 0x3FFF_FFFF
            }
        }
    }

    #[inline]
    pub fn set_len(&mut self, len: u32) {
        self.vl_len = NumericBinary::encode_len(len);
    }

    #[inline]
    pub const fn len(&self) -> u32 {
        NumericBinary::decode_len(self.vl_len)
    }

    #[allow(dead_code)]
    #[inline]
    pub fn is_short(&self) -> bool {
        self.choice.is_short()
    }

    #[inline]
    pub fn header_size(&self) -> u32 {
        self.choice.header_size()
    }

    #[inline]
    pub fn ndigits(&self) -> i32 {
        ((self.len() - self.choice.header_size()) / NUMERIC_DIGIT_SIZE) as i32
    }

    #[inline]
    pub fn sign(&self) -> u16 {
        self.choice.sign()
    }

    #[inline]
    pub fn dscale(&self) -> u16 {
        self.choice.dscale()
    }

    #[inline]
    pub fn weight(&self) -> i16 {
        self.choice.weight()
    }

    #[inline]
    pub fn is_nan(&self) -> bool {
        self.choice.is_nan()
    }

    #[inline]
    pub fn is_negative(&self) -> bool {
        self.choice.sign() == NUMERIC_NEG
    }

    #[inline]
    pub fn is_positive(&self) -> bool {
        self.choice.sign() == NUMERIC_POS
    }

    #[inline]
    pub fn long_mut(&mut self) -> &mut NumericLong {
        unsafe { self.choice.n_long.as_mut() }
    }

    #[inline]
    pub fn short_mut(&mut self) -> &mut NumericShort {
        unsafe { self.choice.n_short.as_mut() }
    }

    #[inline]
    pub const fn nan() -> NumericBinary {
        NumericBinary {
            vl_len: NumericBinary::encode_len(NUMERIC_HEADER_SIZE_SHORT as u32),
            choice: NumericChoice {
                n_header: UnionField::new(),
                n_long: UnionField::new(),
                n_short: UnionField::new(),
                _data: [NUMERIC_NAN, 0],
            },
        }
    }

    #[inline]
    pub const fn zero() -> NumericBinary {
        NumericBinary {
            vl_len: NumericBinary::encode_len(NUMERIC_HEADER_SIZE_SHORT as u32),
            choice: NumericChoice {
                n_header: UnionField::new(),
                n_long: UnionField::new(),
                n_short: UnionField::new(),
                _data: [NUMERIC_SHORT, 0],
            },
        }
    }

    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        let len = self.len();
        unsafe {
            std::slice::from_raw_parts(self as *const NumericBinary as *const u8, len as usize)
        }
    }

    #[inline]
    pub fn as_var(&self) -> NumericVar {
        let flat_bits = self.choice.flag_bits();
        if flat_bits == NUMERIC_SHORT {
            let len = self.len();
            let ndigits = ((len - NUMERIC_HEADER_SIZE_SHORT as u32) / NUMERIC_DIGIT_SIZE) as i32;

            let short = unsafe { self.choice.n_short.as_ref() };
            let weight = {
                let weight_sign = short.n_header & NUMERIC_SHORT_WEIGHT_SIGN_MASK;
                let weight = short.n_header & NUMERIC_SHORT_WEIGHT_MASK;
                if weight_sign != 0 {
                    ((!NUMERIC_SHORT_WEIGHT_MASK) | weight) as i16
                } else {
                    weight as i16
                }
            };
            let dscale = (short.n_header & NUMERIC_SHORT_DSCALE_MASK) >> NUMERIC_SHORT_DSCALE_SHIFT;
            let sign = {
                if (self.choice.n_header() & NUMERIC_SHORT_SIGN_MASK) != 0 {
                    NUMERIC_NEG
                } else {
                    NUMERIC_POS
                }
            };
            let digits = unsafe { short.n_data.as_slice(ndigits as usize) };

            NumericVar::borrowed(ndigits, weight as i32, dscale as i32, sign, digits)
        } else if flat_bits == NUMERIC_NAN {
            NumericVar::borrowed(0, 0, 0, NUMERIC_NAN, &[])
        } else {
            let len = self.len();
            let ndigits = ((len - NUMERIC_HEADER_SIZE as u32) / NUMERIC_DIGIT_SIZE) as i32;

            let long = unsafe { self.choice.n_long.as_ref() };
            let weight = long.n_weight;
            let dscale = long.n_sign_dscale & NUMERIC_DSCALE_MASK;
            let sign = flat_bits;
            let digits = unsafe { long.n_data.as_slice(ndigits as usize) };

            NumericVar::borrowed(ndigits, weight as i32, dscale as i32, sign, digits)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::data::NumericData;
    use std::mem::size_of;

    #[test]
    fn consts() {
        assert_eq!(NUMERIC_WEIGHT_MAX, 32767);
        assert_eq!(NUMERIC_WEIGHT_MIN, -32767);
        assert_eq!(NUMERIC_DSCALE_MAX, 16383);
        assert_eq!(NUMERIC_SHORT_WEIGHT_MAX, 63);
        assert_eq!(NUMERIC_SHORT_WEIGHT_MIN, -64);
        assert_eq!(NUMERIC_SHORT_DSCALE_MAX, 63);
        assert_eq!(NUMERIC_HEADER_SIZE % NUMERIC_DIGIT_SIZE as usize, 0);
        assert_eq!(NUMERIC_HEADER_SIZE_SHORT % NUMERIC_DIGIT_SIZE as usize, 0);
    }

    #[test]
    fn binary() {
        let mut data = NumericData::with_ndigits(3);
        assert_eq!(data.len(), 3 + NUMERIC_HEADER_NDIGITS + 1);
        assert_eq!(data.offset(), NUMERIC_HEADER_NDIGITS + 1);

        let buf = data.as_mut_slice().as_ptr();
        let offset = unsafe { buf.offset(data.offset() as isize) };

        unsafe {
            let bin_ptr = (offset as *mut u8).sub(NUMERIC_HEADER_SIZE);
            let bin: &mut NumericBinary = &mut *(bin_ptr as *mut NumericBinary);
            assert_eq!(bin_ptr, buf.offset(1) as *mut u8);

            let long_mut = bin.long_mut();
            let long = long_mut as *mut NumericLong as *mut u8;
            assert_eq!(bin_ptr.add(size_of::<u32>()), long);

            let long_data = long_mut.n_data.as_ptr();
            assert_eq!(
                long.add(size_of::<u16>() + size_of::<i16>()),
                long_data as *mut u8
            );
        }

        unsafe {
            let bin_ptr = (offset as *mut u8).sub(NUMERIC_HEADER_SIZE_SHORT);
            let bin: &mut NumericBinary = &mut *(bin_ptr as *mut NumericBinary);
            assert_eq!(bin_ptr, buf.offset(2) as *mut u8);

            let short_mut = bin.short_mut();
            let short = short_mut as *mut NumericShort as *mut u8;
            assert_eq!(bin_ptr.add(size_of::<u32>()), short);

            let short_data = short_mut.n_data.as_ptr();
            assert_eq!(short.add(size_of::<u16>()), short_data as *mut u8);
        }
    }
}
