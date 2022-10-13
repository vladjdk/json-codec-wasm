// Translation of Bjoern Hoehrmann's "Flexible and Economical UTF-8 Decoder".
// See http://bjoern.hoehrmann.de/utf-8/decoder/dfa/ for details.
//
// License
//
// Copyright (c) 2008-2009 Bjoern Hoehrmann <bjoern@hoehrmann.de>
//
// Permission is hereby granted, free of charge, to any person obtaining
// a copy of this software and associated documentation files
// (the "Software"), to deal in the Software without restriction, including
// without limitation the rights to use, copy, modify, merge, publish,
// distribute, sublicense, and/or sell copies of the Software, and to
// permit persons to whom the Software is furnished to do so, subject
// to the following conditions:
//
// The above copyright notice and this permission notice shall be included
// in all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
// OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
// MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
// IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
// CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
// TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
// SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
//

use std::char::from_u32_unchecked;
use std::error::Error;
use std::fmt;
use std::io::{self, Read};

const UTF8D: [u8; 364] = [
    // The first part of the table maps bytes to character classes that
    // to reduce the size of the transition table and create bitmasks.
     0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
     0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
     0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
     0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
     1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,  9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,
     7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,  7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,
     8,8,2,2,2,2,2,2,2,2,2,2,2,2,2,2,  2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,
    10,3,3,3,3,3,3,3,3,3,3,3,3,4,3,3, 11,6,6,6,5,8,8,8,8,8,8,8,8,8,8,8,

    // The second part is a transition table that maps a combination
    // of a state of the automaton and a character class to a state.
     0,12,24,36,60,96,84,12,12,12,48,72, 12,12,12,12,12,12,12,12,12,12,12,12,
    12, 0,12,12,12,12,12, 0,12, 0,12,12, 12,24,12,12,12,12,12,24,12,24,12,12,
    12,12,12,12,12,12,12,24,12,12,12,12, 12,24,12,12,12,12,12,12,12,24,12,12,
    12,12,12,12,12,12,12,36,12,36,12,12, 12,36,12,12,12,12,12,36,12,36,12,12,
    12,36,12,12,12,12,12,12,12,12,12,12,
];

pub const UTF8_ACCEPT: u32 = 0;
pub const UTF8_REJECT: u32 = 12;

#[inline]
pub fn decode(state: u32, byte: u32, codep: &mut u32) -> u32 {
    let typ = UTF8D[byte as usize] as u32;

    *codep =
        if state != UTF8_ACCEPT {
            (byte & 0x3f) | (*codep << 6)
        } else {
            (0xff >> typ) & byte
        };

    let ix = 256 + state + typ;
    UTF8D[ix as usize] as u32
}

pub struct Chars<R> {
    reader: R,
    state:  u32,
    codep:  u32
}

impl<R: Read> Chars<R> {
    pub fn new(r: R) -> Chars<R> {
        Chars {
            reader: r,
            state:  UTF8_ACCEPT,
            codep:  0
        }
    }
}

impl<R: Read> Iterator for Chars<R> {
    type Item = Result<char, ReadError>;

    fn next(&mut self) -> Option<Result<char, ReadError>> {
        loop {
            match read_byte(&mut self.reader) {
                Some(Ok(b)) => {
                    self.state = decode(self.state, b as u32, &mut self.codep);
                    match self.state {
                        UTF8_ACCEPT => unsafe { return Some(Ok(from_u32_unchecked(self.codep))) },
                        UTF8_REJECT => return Some(Err(ReadError::InvalidUtf8)),
                        _           => {}
                    }
                }
                Some(Err(e)) => return Some(Err(e.into())),
                None         => return None
            }
        }
    }
}

fn read_byte<R: Read>(r: &mut R) -> Option<io::Result<u8>> {
    let mut b = [0];
    loop {
        match r.read(&mut b) {
            Ok(0)  => return None,
            Ok(_)  => return Some(Ok(b[0])),
            Err(e) =>
                if e.kind() == io::ErrorKind::Interrupted {
                    continue
                } else {
                    return Some(Err(e))
                }
        }
    }
}

#[derive(Debug)]
pub enum ReadError {
    InvalidUtf8,
    Io(io::Error)
}

impl fmt::Display for ReadError {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match *self {
            ReadError::InvalidUtf8 => write!(f, "invalid utf-8 encoding"),
            ReadError::Io(ref e)   => write!(f, "i/o: {}", e)
        }
    }
}

impl Error for ReadError {
    fn description(&self) -> &str {
        match *self {
            ReadError::InvalidUtf8 => "invalid utf-8 encoding",
            ReadError::Io(_)       => "i/o error"
        }

    }

    fn cause(&self) -> Option<&Error> {
        match *self {
            ReadError::Io(ref e) => Some(e),
            _                    => None
        }
    }
}

impl From<io::Error> for ReadError {
    fn from(e: io::Error) -> ReadError {
        ReadError::Io(e)
    }
}

