// Copyright 2020 CoD Team

//! Numeric data presentation.

use crate::NumericDigit;
use std::mem;
use std::ptr::NonNull;

#[derive(Debug)]
pub struct NumericData {
    // digits buffer
    buf: Option<NonNull<NumericDigit>>,
    // length of buf
    len: u32,
    // digits start position
    offset: u32,
    // indicate whether buf is owned by self
    owned: bool,
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
        }
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
        debug_assert!(ndigits > 0);
        self.buf_free();

        let len = (ndigits + 1) as u32;

        let mut vec = Vec::<NumericDigit>::with_capacity(len as usize);
        vec.push(0); // spare digit for later rounding

        let ptr = vec.as_mut_ptr();
        debug_assert!(!ptr.is_null());
        mem::forget(vec);

        let buf = unsafe { NonNull::new_unchecked(ptr) };

        self.buf = Some(buf);
        self.len = len;
        self.offset = 1;
        self.owned = true;
    }

    #[inline]
    fn buf_free(&mut self) {
        if let Some(buf) = self.buf {
            if self.owned {
                unsafe {
                    let _vec: Vec<NumericDigit> =
                        Vec::from_raw_parts(buf.as_ptr(), 0, self.len as usize);
                }
            }
            self.buf = None;
        }
    }

    /// Copy buf with rounding digit.
    #[inline]
    fn buf_copy(&self, ndigits: i32) -> (NonNull<NumericDigit>, u32, u32) {
        debug_assert!(ndigits > 0);
        debug_assert!(self.buf.is_some());
        let len = (ndigits + 1) as u32;
        let mut vec = Vec::with_capacity(len as usize);
        vec.push(0); // spare digit for rounding
        vec.extend_from_slice(self.digits(ndigits));

        let ptr = vec.as_mut_ptr();
        debug_assert!(!ptr.is_null());
        mem::forget(vec);

        let buf = unsafe { NonNull::new_unchecked(ptr) };
        (buf, len, 1)
    }

    #[inline]
    pub fn clear(&mut self) {
        self.buf_free();
        self.len = 0;
        self.offset = 0;
        self.owned = false;
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
        debug_assert!(self.owned, "can only write owned memory");
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
        debug_assert!(self.owned, "can only write owned memory");
        debug_assert!(self.offset > 0);
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
        if self.offset == 0 {
            let (new_buf, new_len, new_offset) = self.buf_copy(ndigits);
            self.buf_free();
            self.buf = Some(new_buf);
            self.len = new_len;
            self.offset = new_offset;
            self.owned = true;
        }
    }

    #[inline]
    pub fn clone(&self, ndigits: i32) -> Self {
        debug_assert!(ndigits > 0);
        debug_assert!(self.buf.is_some());
        let (buf, len, offset) = self.buf_copy(ndigits);
        Self {
            buf: Some(buf),
            len,
            offset,
            owned: true,
        }
    }
}

impl Drop for NumericData {
    fn drop(&mut self) {
        self.buf_free();
    }
}
