//! Buffer structures to enable decoding strings without allocating.
use std::str;

/// UTF-8 encoding buffer over an u8-slice.
pub struct Utf8Buffer<'r> {
    buf: &'r mut [u8],
    idx: usize,
}

impl<'r> Utf8Buffer<'r> {
    pub fn new(b: &'r mut [u8]) -> Utf8Buffer<'r> {
        Utf8Buffer { buf: b, idx: 0 }
    }

    pub fn reset(&mut self) {
        self.idx = 0
    }

    pub fn as_str(&self) -> &str {
        unsafe { str::from_utf8_unchecked(&self.buf[0..self.idx]) }
    }

    pub fn is_full(&self) -> bool {
        self.idx >= self.buf.len()
    }

    pub fn push(&mut self, c: char) {
        let len = c.len_utf8();
        if self.idx + len > self.buf.len() {
            return ();
        }
        self.idx += c.encode_utf8(&mut self.buf[self.idx..]).len()
    }
}

pub trait Buffer {
    fn push(&mut self, c: char);
    fn is_full(&self) -> bool;
}

impl Buffer for String {
    fn push(&mut self, c: char) {
        self.push(c)
    }
    fn is_full(&self) -> bool {
        false
    }
}

impl<'r> Buffer for Utf8Buffer<'r> {
    fn push(&mut self, c: char) {
        self.push(c)
    }
    fn is_full(&self) -> bool {
        self.is_full()
    }
}
