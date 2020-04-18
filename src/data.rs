// Copyright 2020 CoD Team

//! Numeric data management.

use crate::binary::{
    NumericBinary, NumericDigit, NUMERIC_DIGIT_SIZE, NUMERIC_HEADER_NDIGITS, NUMERIC_HEADER_SIZE,
    NUMERIC_HEADER_SIZE_SHORT,
};
use std::borrow::Borrow;
use std::mem;
use std::ops::Deref;
use std::ptr;

#[derive(Debug)]
pub struct NumericData {
    // digits buffer
    buf: *const NumericDigit,
    // NumericDigit size of buf
    len: u32,
    // digits start position
    offset: u32,
    // indicate whether data header is set.
    set_header: bool,
}

unsafe impl Send for NumericData {}
unsafe impl Sync for NumericData {}

impl NumericData {
    #[inline]
    pub fn with_ndigits(ndigits: i32) -> Self {
        debug_assert!(ndigits >= 0);
        let mut zero = NumericData {
            buf: ptr::null(),
            len: 0,
            offset: 0,
            set_header: false,
        };
        zero.buf_alloc(ndigits);
        zero
    }

    #[inline]
    pub fn into_raw_parts(self) -> (*mut NumericDigit, u32, u32) {
        let me = mem::ManuallyDrop::new(self);
        (me.buf as *mut _, me.len, me.offset)
    }

    #[inline]
    pub unsafe fn from_raw_parts(buf: *mut NumericDigit, len: u32, offset: u32) -> Self {
        debug_assert!(!buf.is_null());
        debug_assert!(len >= offset);
        NumericData {
            buf,
            len,
            offset,
            set_header: false,
        }
    }

    #[inline]
    fn buf_alloc(&mut self, ndigits: i32) {
        debug_assert!(ndigits >= 0);
        self.buf_free();

        // data header and spare digit for rounding
        let len = ndigits as u32 + NUMERIC_HEADER_NDIGITS + 1;

        let vec = Vec::<NumericDigit>::with_capacity(len as usize);

        let ptr = vec.as_ptr();
        debug_assert!(!ptr.is_null());
        mem::forget(vec);

        self.buf = ptr;
        self.len = len;
        self.offset = NUMERIC_HEADER_NDIGITS + 1;
        self.set_header = false;
    }

    #[inline]
    fn buf_free(&mut self) {
        if !self.buf.is_null() {
            unsafe {
                let _vec: Vec<NumericDigit> =
                    Vec::from_raw_parts(self.buf as *mut _, 0, self.len as usize);
            }
            self.buf = ptr::null();
        }
    }

    /// Copy buf with rounding digit.
    #[inline]
    fn buf_copy(&self, ndigits: i32) -> (*const NumericDigit, u32, u32) {
        debug_assert!(ndigits >= 0);
        debug_assert!(!self.buf.is_null());
        let len = ndigits as u32 + NUMERIC_HEADER_NDIGITS + 1;
        let mut vec = Vec::with_capacity(len as usize);

        if ndigits > 0 {
            unsafe { vec.set_len(NUMERIC_HEADER_NDIGITS as usize + 1) }
            vec.extend_from_slice(self.digits(ndigits));
        }

        let ptr = vec.as_ptr();
        debug_assert!(!ptr.is_null());
        mem::forget(vec);

        (ptr, len, NUMERIC_HEADER_NDIGITS + 1)
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
    pub fn digits(&self, ndigits: i32) -> &[NumericDigit] {
        debug_assert!(self.offset + ndigits as u32 <= self.len);
        if !self.buf.is_null() {
            unsafe {
                let ptr = self.buf.offset(self.offset as isize);
                std::slice::from_raw_parts(ptr, ndigits as usize)
            }
        } else {
            &[]
        }
    }

    #[inline]
    pub fn digits_mut(&mut self, ndigits: i32) -> &mut [NumericDigit] {
        debug_assert!(self.offset + ndigits as u32 <= self.len);
        debug_assert!(!self.buf.is_null());
        unsafe {
            let ptr = self.buf.offset(self.offset as isize);
            std::slice::from_raw_parts_mut(ptr as *mut _, ndigits as usize)
        }
    }

    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [NumericDigit] {
        debug_assert!(self.offset > NUMERIC_HEADER_NDIGITS);
        debug_assert!(!self.buf.is_null());
        unsafe { std::slice::from_raw_parts_mut(self.buf as *mut _, self.len as usize) }
    }

    #[inline]
    pub fn reserve_rounding_digit(&mut self, ndigits: i32) {
        debug_assert!(ndigits > 0);
        // there is no rounding digit,
        // so we should copy the buf with rounding digit.
        if self.offset <= NUMERIC_HEADER_NDIGITS {
            let (new_buf, new_len, new_offset) = self.buf_copy(ndigits);
            self.buf_free();
            self.buf = new_buf;
            self.len = new_len;
            self.offset = new_offset;
            self.set_header = false;
        }
    }

    /// Sets numeric header, returning header offset.
    #[allow(clippy::cast_ptr_alignment)]
    #[inline]
    pub fn set_header(&mut self, weight: i16, dscale: u16, sign: u16, ndigits: i32) -> u32 {
        debug_assert!(ndigits >= 0);
        debug_assert!(
            self.offset >= NUMERIC_HEADER_NDIGITS,
            "no enough space for data header"
        );
        debug_assert!(!self.buf.is_null());

        let ptr = unsafe { self.buf.offset(self.offset as isize) as *mut u8 };

        let header_offset = if NumericBinary::can_be_short(weight, dscale) {
            let bin: &mut NumericBinary = unsafe {
                let p = ptr.sub(NUMERIC_HEADER_SIZE_SHORT);
                &mut *(p as *mut NumericBinary)
            };

            let len = NUMERIC_HEADER_SIZE_SHORT as u32 + ndigits as u32 * NUMERIC_DIGIT_SIZE;
            bin.set_len(len);
            bin.short_mut().set_header(weight, dscale, sign);

            self.offset * NUMERIC_DIGIT_SIZE - NUMERIC_HEADER_SIZE_SHORT as u32
        } else {
            let bin: &mut NumericBinary = unsafe {
                let p = ptr.sub(NUMERIC_HEADER_SIZE);
                &mut *(p as *mut NumericBinary)
            };

            let len = NUMERIC_HEADER_SIZE as u32 + ndigits as u32 * NUMERIC_DIGIT_SIZE;
            bin.set_len(len);
            bin.long_mut().set_header(weight, dscale, sign);

            self.offset * NUMERIC_DIGIT_SIZE - NUMERIC_HEADER_SIZE as u32
        };

        self.set_header = true;

        header_offset
    }
}

impl Drop for NumericData {
    #[inline]
    fn drop(&mut self) {
        self.buf_free();
    }
}

#[derive(Debug)]
#[repr(transparent)]
pub(crate) struct NumericDigits {
    data: [NumericDigit],
}

impl NumericDigits {
    #[inline]
    pub unsafe fn from_slice_unchecked(value: &[NumericDigit]) -> &NumericDigits {
        &*(value as *const [NumericDigit] as *const NumericDigits)
    }

    #[inline]
    pub fn as_slice(&self) -> &[NumericDigit] {
        &self.data
    }
}

impl Deref for NumericDigits {
    type Target = [NumericDigit];

    #[inline]
    fn deref(&self) -> &[NumericDigit] {
        self.as_slice()
    }
}

impl Borrow<NumericDigits> for NumericData {
    #[inline]
    fn borrow(&self) -> &NumericDigits {
        let digits = self.digits((self.len - self.offset) as i32);
        unsafe { NumericDigits::from_slice_unchecked(digits) }
    }
}

impl ToOwned for NumericDigits {
    type Owned = NumericData;

    #[inline]
    fn to_owned(&self) -> NumericData {
        let ndigits = self.data.len() as i32;
        let mut data = NumericData::with_ndigits(ndigits);
        data.digits_mut(ndigits).copy_from_slice(self.as_slice());
        data
    }
}
