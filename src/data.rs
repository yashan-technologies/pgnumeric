// Copyright 2020 CoD Team

//! Numeric data presentation.

use std::marker::PhantomData;
use std::mem::{self, size_of};
use std::ptr::NonNull;

/// Use `i16` to represent a numeric digit.
pub type NumericDigit = i16;

/// Size of numeric digit.
pub const NUMERIC_DIGIT_SIZE: u32 = size_of::<NumericDigit>() as u32;

#[derive(Debug)]
pub(crate) struct NumericData {
    // digits buffer
    buf: Option<NonNull<NumericDigit>>,
    // NumericDigit size of buf
    len: u32,
    // digits start position
    offset: u32,
    // indicate whether buf is owned by self
    owned: bool,
    // indicate whether data header is set.
    set_header: bool,
}

unsafe impl Send for NumericData {}
unsafe impl Sync for NumericData {}

impl NumericData {
    #[inline]
    pub const fn new() -> Self {
        Self {
            buf: None,
            len: 0,
            offset: 0,
            owned: false,
            set_header: false,
        }
    }

    #[inline]
    pub const fn zero_unowned() -> Self {
        const ZERO_BINARY: NumericBinary = NumericBinary {
            vl_len: (NUMERIC_HEADER_SIZE_SHORT as u32) << 2,
            choice: NumericChoice {
                n_header: UnionField::new(),
                n_long: UnionField::new(),
                n_short: UnionField::new(),
                _data: [NUMERIC_SHORT, 0],
            },
        };

        let buf = unsafe {
            Some(NonNull::new_unchecked(
                &ZERO_BINARY as *const _ as *mut NumericDigit,
            ))
        };

        Self {
            buf,
            len: NUMERIC_HEADER_SIZE_SHORT as u32 / NUMERIC_DIGIT_SIZE,
            offset: NUMERIC_HEADER_SIZE_SHORT as u32 / NUMERIC_DIGIT_SIZE,
            owned: false,
            set_header: true,
        }
    }

    /// Only alloc buf, but not set header.
    #[inline]
    pub fn zero_owned() -> Self {
        let mut zero = Self::new();
        zero.buf_alloc(0);
        zero
    }

    #[inline]
    pub const fn len(&self) -> u32 {
        self.len
    }

    #[inline]
    pub const fn offset(&self) -> u32 {
        self.offset
    }

    #[inline]
    pub fn offset_set(&mut self, offset: u32) {
        debug_assert!(offset <= self.len);
        self.offset = offset;
    }

    #[inline]
    pub fn offset_add(&mut self, val: u32) {
        debug_assert!(self.offset + val <= self.len);
        self.offset += val;
    }

    #[inline]
    pub fn offset_sub(&mut self, val: u32) {
        debug_assert!(self.offset >= val);
        self.offset -= val;
    }

    #[inline]
    pub fn buf_alloc(&mut self, ndigits: i32) {
        debug_assert!(ndigits >= 0);
        self.buf_free();

        // data header and spare digit for rounding
        let len = ndigits as u32 + NUMERIC_HEADER_NDIGITS + 1;

        let mut vec = Vec::<NumericDigit>::with_capacity(len as usize);

        let ptr = vec.as_mut_ptr();
        debug_assert!(!ptr.is_null());
        mem::forget(vec);

        let buf = unsafe { NonNull::new_unchecked(ptr) };

        self.buf = Some(buf);
        self.len = len;
        self.offset = NUMERIC_HEADER_NDIGITS + 1;
        self.owned = true;
        self.set_header = false;
    }

    #[inline]
    fn buf_free(&mut self) {
        if let Some(buf) = self.buf {
            if self.owned {
                unsafe {
                    let _vec: Vec<NumericDigit> =
                        Vec::from_raw_parts(buf.as_ptr(), 0, self.len as usize);
                }
                self.owned = false;
            }
            self.buf = None;
        }
    }

    /// Copy buf with rounding digit.
    #[inline]
    fn buf_copy(&self, ndigits: i32) -> (NonNull<NumericDigit>, u32, u32) {
        debug_assert!(ndigits >= 0);
        debug_assert!(self.buf.is_some());
        let len = ndigits as u32 + NUMERIC_HEADER_NDIGITS + 1;
        let mut vec = Vec::with_capacity(len as usize);

        if ndigits > 0 {
            unsafe { vec.set_len(NUMERIC_HEADER_NDIGITS as usize + 1) }
            vec.extend_from_slice(self.digits(ndigits));
        }

        let ptr = vec.as_mut_ptr();
        debug_assert!(!ptr.is_null());
        mem::forget(vec);

        let buf = unsafe { NonNull::new_unchecked(ptr) };
        (buf, len, NUMERIC_HEADER_NDIGITS + 1)
    }

    #[inline]
    pub fn clear(&mut self) {
        self.buf_free();
        self.len = 0;
        self.offset = 0;
        self.owned = false;
        self.set_header = false;
    }

    #[inline]
    pub fn digits(&self, ndigits: i32) -> &[NumericDigit] {
        debug_assert!(self.offset + ndigits as u32 <= self.len);
        match self.buf {
            Some(buf) => unsafe {
                let ptr = buf.as_ptr().offset(self.offset as isize);
                std::slice::from_raw_parts(ptr, ndigits as usize)
            },
            None => &[],
        }
    }

    #[inline]
    pub fn digits_mut(&mut self, ndigits: i32) -> &mut [NumericDigit] {
        assert!(self.owned, "can only write owned memory");
        debug_assert!(ndigits > 0);
        debug_assert!(self.offset + ndigits as u32 <= self.len);
        unsafe {
            let ptr = self
                .buf
                .expect("null pointer")
                .as_ptr()
                .offset(self.offset as isize);
            std::slice::from_raw_parts_mut(ptr, ndigits as usize)
        }
    }

    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [NumericDigit] {
        assert!(self.owned, "can only write owned memory");
        debug_assert!(self.offset > NUMERIC_HEADER_NDIGITS);
        unsafe {
            let ptr = self.buf.expect("null pointer").as_ptr();
            std::slice::from_raw_parts_mut(ptr, self.len as usize)
        }
    }

    #[inline]
    pub fn reserve_rounding_digit(&mut self, ndigits: i32) {
        debug_assert!(ndigits > 0);
        // there is no rounding digit,
        // so we should copy the buf with rounding digit.
        if self.offset <= NUMERIC_HEADER_NDIGITS {
            let (new_buf, new_len, new_offset) = self.buf_copy(ndigits);
            self.buf_free();
            self.buf = Some(new_buf);
            self.len = new_len;
            self.offset = new_offset;
            self.owned = true;
            self.set_header = false;
        }
    }

    #[inline]
    pub fn copy(&self, ndigits: i32) -> Self {
        debug_assert!(ndigits >= 0);
        debug_assert!(self.buf.is_some());

        let (buf, len, offset) = self.buf_copy(ndigits);
        Self {
            buf: Some(buf),
            len,
            offset,
            owned: true,
            set_header: false,
        }
    }

    #[inline]
    pub fn guarantee_owned(&mut self, ndigits: i32) {
        debug_assert!(ndigits >= 0);

        if self.buf.is_some() && !self.owned {
            let (buf, len, offset) = self.buf_copy(ndigits);
            self.buf = Some(buf);
            self.len = len;
            self.offset = offset;
            self.owned = true;
            self.set_header = false;
        }
    }

    #[allow(clippy::cast_ptr_alignment)]
    #[inline]
    pub fn set_header(&mut self, weight: i16, dscale: u16, sign: u16, ndigits: i32) {
        assert!(self.owned, "can only write owned memory");
        debug_assert!(ndigits >= 0);
        debug_assert!(
            self.offset >= NUMERIC_HEADER_NDIGITS,
            "no enough space for data header"
        );
        debug_assert!(sign != NUMERIC_NAN);

        let ptr = unsafe {
            self.buf
                .expect("null pointer")
                .as_ptr()
                .offset(self.offset as isize) as *mut u8
        };

        if NumericBinary::can_be_short(weight, dscale) {
            let bin: &mut NumericBinary = unsafe {
                let p = ptr.sub(NUMERIC_HEADER_SIZE_SHORT);
                &mut *(p as *mut NumericBinary)
            };

            let len = NUMERIC_HEADER_SIZE_SHORT as u32 + ndigits as u32 * NUMERIC_DIGIT_SIZE;
            bin.set_len(len);
            bin.short_mut().set_header(weight, dscale, sign);
        } else {
            let bin: &mut NumericBinary = unsafe {
                let p = ptr.sub(NUMERIC_HEADER_SIZE);
                &mut *(p as *mut NumericBinary)
            };

            let len = NUMERIC_HEADER_SIZE as u32 + ndigits as u32 * NUMERIC_DIGIT_SIZE;
            bin.set_len(len);
            bin.long_mut().set_header(weight, dscale, sign);
        }

        self.set_header = true;
    }

    #[inline]
    pub fn nan_bytes() -> &'static [u8] {
        const NAN_BINARY: NumericBinary = NumericBinary {
            vl_len: (NUMERIC_HEADER_SIZE_SHORT as u32) << 2,
            choice: NumericChoice {
                n_header: UnionField::new(),
                n_long: UnionField::new(),
                n_short: UnionField::new(),
                _data: [NUMERIC_NAN, 0],
            },
        };

        unsafe {
            std::slice::from_raw_parts(
                &NAN_BINARY as *const _ as *const u8,
                NUMERIC_HEADER_SIZE_SHORT,
            )
        }
    }

    #[allow(clippy::cast_ptr_alignment)]
    #[inline]
    pub fn as_bytes(&self, weight: i16, dscale: u16, ndigits: i32) -> &[u8] {
        debug_assert!(ndigits >= 0);
        debug_assert!(self.set_header);
        debug_assert!(self.buf.is_some());

        unsafe {
            let ptr = self
                .buf
                .expect("null pointer")
                .as_ptr()
                .offset(self.offset as isize) as *const u8;

            if NumericBinary::can_be_short(weight, dscale) {
                let p = ptr.sub(NUMERIC_HEADER_SIZE_SHORT);
                let len =
                    NUMERIC_HEADER_SIZE_SHORT + ndigits as usize * NUMERIC_DIGIT_SIZE as usize;
                if cfg!(debug_assertions) {
                    let bin: &NumericBinary = &*(p as *const NumericBinary);
                    assert!(bin.choice.is_short());
                }
                std::slice::from_raw_parts(p, len)
            } else {
                let p = ptr.sub(NUMERIC_HEADER_SIZE);
                let len = NUMERIC_HEADER_SIZE + ndigits as usize * NUMERIC_DIGIT_SIZE as usize;
                if cfg!(debug_assertions) {
                    let bin: &NumericBinary = &*(p as *const NumericBinary);
                    assert!(!bin.choice.is_nan() && !bin.choice.is_short());
                }
                std::slice::from_raw_parts(p, len)
            }
        }
    }

    #[allow(clippy::cast_ptr_alignment)]
    #[inline]
    pub unsafe fn from_raw_parts(ptr: *mut u8, len: u32, header_offset: u32, owned: bool) -> Self {
        debug_assert!(!ptr.is_null());
        debug_assert!(header_offset < len);
        debug_assert!(len % NUMERIC_DIGIT_SIZE == 0);
        debug_assert!(header_offset % NUMERIC_DIGIT_SIZE == 0);

        let digits_len = len / NUMERIC_DIGIT_SIZE;
        let header = ptr.offset(header_offset as isize);
        let bin: &NumericBinary = &*(header as *const NumericBinary);
        debug_assert!(len - header_offset == bin.len());

        let header_size = bin.choice.header_size();

        let offset = (header_offset + header_size) / NUMERIC_DIGIT_SIZE;
        debug_assert!((header_offset + header_size) % NUMERIC_DIGIT_SIZE == 0);

        Self {
            buf: Some(NonNull::new_unchecked(ptr as *mut NumericDigit)),
            len: digits_len,
            offset,
            owned,
            set_header: true,
        }
    }
}

impl Drop for NumericData {
    fn drop(&mut self) {
        self.buf_free();
    }
}

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

/// A flexible array.
#[repr(C)]
#[derive(Debug)]
struct FlexArray<T>(PhantomData<T>, [T; 0]);

impl<T> FlexArray<T> {
    #[cfg(test)]
    #[inline]
    pub fn as_ptr(&self) -> *const T {
        self as *const _ as *const T
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

pub const VAR_HEADER_SIZE: i32 = size_of::<i32>() as i32;
const NUMERIC_HEADER_SIZE: usize = VAR_HEADER_SIZE as usize + size_of::<u16>() + size_of::<i16>();
const NUMERIC_HEADER_SIZE_SHORT: usize = VAR_HEADER_SIZE as usize + size_of::<u16>();
const NUMERIC_HEADER_NDIGITS: u32 =
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

#[repr(C)]
struct NumericShort {
    // Sign + display scale + weight
    n_header: u16,

    // Digits
    n_data: FlexArray<NumericDigit>,
}

impl NumericShort {
    #[inline]
    fn set_header(&mut self, weight: i16, dscale: u16, sign: u16) {
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
struct NumericLong {
    // Sign + display scale
    n_sign_dscale: u16,

    // Weight of 1st digit
    n_weight: i16,

    // Digits
    n_data: FlexArray<NumericDigit>,
}

impl NumericLong {
    #[inline]
    fn set_header(&mut self, weight: i16, dscale: u16, sign: u16) {
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
    pub fn weight(&self) -> i16 {
        if self.header_is_short() {
            let weight_sign =
                unsafe { self.n_short.as_ref().n_header & NUMERIC_SHORT_WEIGHT_SIGN_MASK };
            let weight = unsafe { self.n_short.as_ref().n_header & NUMERIC_SHORT_WEIGHT_MASK };
            if weight_sign != 0 {
                ((!NUMERIC_SHORT_WEIGHT_MASK) | weight) as i16
            } else {
                weight as i16
            }
        } else {
            unsafe { self.n_long.as_ref().n_weight }
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
    pub fn set_len(&mut self, len: u32) {
        self.vl_len = len << 2;
    }

    #[inline]
    pub fn len(&self) -> u32 {
        (self.vl_len >> 2) & 0x3FFF_FFFF
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
    fn long_mut(&mut self) -> &mut NumericLong {
        unsafe { self.choice.n_long.as_mut() }
    }

    #[inline]
    fn short_mut(&mut self) -> &mut NumericShort {
        unsafe { self.choice.n_short.as_mut() }
    }

    #[allow(clippy::cast_ptr_alignment)]
    #[inline]
    pub unsafe fn from_raw_parts<'a>(
        ptr: *mut u8,
        len: u32,
        header_offset: u32,
    ) -> &'a NumericBinary {
        debug_assert!(!ptr.is_null());
        debug_assert!(header_offset < len);

        let header = ptr.offset(header_offset as isize);
        &*(header as *const NumericBinary)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
        let mut data = NumericData::new();
        data.buf_alloc(3);
        assert_eq!(data.len, 3 + NUMERIC_HEADER_NDIGITS + 1);
        assert_eq!(data.offset(), NUMERIC_HEADER_NDIGITS + 1);

        let buf = data.buf.unwrap().as_ptr();
        let offset = unsafe { buf.offset(data.offset as isize) };

        unsafe {
            let bin_ptr = (offset as *mut u8).sub(NUMERIC_HEADER_SIZE);
            let bin: &mut NumericBinary = mem::transmute(bin_ptr);
            assert_eq!(bin_ptr, buf.offset(1) as *mut u8);

            let long_mut = bin.long_mut();
            let long = long_mut as *mut NumericLong as *mut u8;
            assert_eq!(bin_ptr.offset(size_of::<u32>() as isize), long);

            let long_data = long_mut.n_data.as_ptr();
            assert_eq!(
                long.offset((size_of::<u16>() + size_of::<i16>()) as isize),
                long_data as *mut u8
            );
        }

        unsafe {
            let bin_ptr = (offset as *mut u8).sub(NUMERIC_HEADER_SIZE_SHORT);
            let bin: &mut NumericBinary = mem::transmute(bin_ptr);
            assert_eq!(bin_ptr, buf.offset(2) as *mut u8);

            let short_mut = bin.short_mut();
            let short = short_mut as *mut NumericShort as *mut u8;
            assert_eq!(bin_ptr.offset(size_of::<u32>() as isize), short);

            let short_data = short_mut.n_data.as_ptr();
            assert_eq!(
                short.offset(size_of::<u16>() as isize),
                short_data as *mut u8
            );
        }
    }
}
