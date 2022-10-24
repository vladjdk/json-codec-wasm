//! JSON ([RFC 7159](http://tools.ietf.org/html/rfc7159)) encoder.
//!
//! # Usage example
//!
//! ```
//! use json::Encoder;
//! use std::io::Cursor;
//!
//! let mut e = Encoder::new(Cursor::new(Vec::new()));
//! let r = e.object().and_then(|()| {
//!     e.key("key1")?; e.array()?;
//!         for i in 0 .. 10 {
//!             e.bool(i % 2 == 0)?
//!         }
//!     e.end()?;
//!     e.key("key2")?; e.string("\"hello world\"")?;
//!     e.key("key3")?; e.object()?;
//!         e.key("inner1")?; e.bool(true)?;
//!         e.key("inner2")?; e.array()?;
//!             e.string("\u{2764}\u{fe0f}")?;
//!             e.string("again")?;
//!             e.bool(false)?;
//!             e.usize(1024)?;
//!             e.u8(90)?;
//!             e.i128(-100)?;
//!             e.null()?;
//!         e.end()?;
//!     e.end()?;
//! e.end()});
//! assert!(r.is_ok())

use std::borrow::{Borrow, Cow};
use std::error::Error;
use std::fmt;
use std::io::{self, Write};
use std::str::Chars;

use ast::Json;
use stack::{Scope, Stack};

// ToJson trait /////////////////////////////////////////////////////////////

pub trait ToJson {
    fn encode<W: Write>(&self, e: &mut Encoder<W>) -> EncodeResult<()>;
}

macro_rules! instance {
    ($name: ident) => {
        impl ToJson for $name {
            fn encode<W: Write>(&self, e: &mut Encoder<W>) -> EncodeResult<()> {
                e.$name(*self)
            }
        }
    };
}

instance!(bool);
instance!(u8);
instance!(u16);
instance!(u32);
instance!(u64);
instance!(usize);
instance!(i8);
instance!(i16);
instance!(i32);
instance!(i64);
instance!(isize);
instance!(i128);
instance!(u128);

impl ToJson for str {
    fn encode<W: Write>(&self, e: &mut Encoder<W>) -> EncodeResult<()> {
        e.string(self)
    }
}

impl ToJson for String {
    fn encode<W: Write>(&self, e: &mut Encoder<W>) -> EncodeResult<()> {
        e.string(self.as_str())
    }
}

impl ToJson for Json {
    fn encode<W: Write>(&self, e: &mut Encoder<W>) -> EncodeResult<()> {
        e.encode(self)
    }
}

impl<'a, T: ToJson> ToJson for &'a T {
    fn encode<W: Write>(&self, e: &mut Encoder<W>) -> EncodeResult<()> {
        (*self).encode(e)
    }
}

impl<'a, T: ToJson + Clone> ToJson for Cow<'a, T> {
    fn encode<W: Write>(&self, e: &mut Encoder<W>) -> EncodeResult<()> {
        (**self).encode(e)
    }
}

impl<T: ToJson> ToJson for Option<T> {
    fn encode<W: Write>(&self, e: &mut Encoder<W>) -> EncodeResult<()> {
        e.optional(self.as_ref())
    }
}

impl<'a, T: ToJson> ToJson for &'a [T] {
    fn encode<W: Write>(&self, e: &mut Encoder<W>) -> EncodeResult<()> {
        e.array()?;
        for x in *self {
            x.encode(e)?
        }
        e.end()
    }
}

// Encoder //////////////////////////////////////////////////////////////////

/// JSON encoder over any `Write`-type.
pub struct Encoder<W> {
    writer: W,
    stack: Stack,
}

// Macros ///////////////////////////////////////////////////////////////////

macro_rules! number {
    ($name: ident, i128) => {
        pub fn $name(&mut self, x: i128) -> EncodeResult<()> {
            // if x.is_nan() || x.is_infinite() {
            //     return Err(EncodeError::InvalidFloat)
            // }
            self.comma_array()?;
            self.writer.write_all(x.to_string().as_bytes())?;
            Ok(())
        }
    };
    ($name: ident, $ty: ty) => {
        pub fn $name(&mut self, x: $ty) -> EncodeResult<()> {
            self.comma_array()?;
            self.writer.write_all(x.to_string().as_bytes())?;
            Ok(())
        }
    };
}

impl<W: Write> Encoder<W> {
    pub fn new(w: W) -> Encoder<W> {
        Encoder {
            writer: w,
            stack: Stack::new(),
        }
    }

    pub fn into_writer(self) -> W {
        self.writer
    }

    pub fn writer_mut(&mut self) -> &mut W {
        &mut self.writer
    }

    pub fn to_json<T: ToJson>(&mut self, t: T) -> EncodeResult<()> {
        t.encode(self)
    }

    pub fn encode(&mut self, j: &Json) -> EncodeResult<()> {
        match *j {
            Json::Null => self.null()?,
            Json::Bool(x) => self.bool(x)?,
            Json::I128(x) => self.i128(x)?,
            Json::U128(x) => self.u128(x)?,
            Json::String(ref x) => self.string(x.as_ref())?,
            Json::Array(ref xs) => {
                self.array()?;
                for x in xs {
                    self.encode(x)?
                }
                self.end()?
            }
            Json::Object(ref xs) => {
                self.object()?;
                for (k, v) in xs {
                    self.key(k.as_ref())?;
                    self.encode(v)?
                }
                self.end()?
            }
        }
        Ok(())
    }

    number!(u8, u8);
    number!(u16, u16);
    number!(u32, u32);
    number!(u64, u64);
    number!(usize, usize);

    number!(i8, i8);
    number!(i16, i16);
    number!(i32, i32);
    number!(i64, i64);
    number!(isize, isize);

    number!(i128, i128);
    number!(u128, u128);

    pub fn bool(&mut self, x: bool) -> EncodeResult<()> {
        self.comma_array()?;
        self.writer.write_all(if x { b"true" } else { b"false" })?;
        Ok(())
    }

    pub fn null(&mut self) -> EncodeResult<()> {
        self.comma_array()?;
        self.writer.write_all(b"null")?;
        Ok(())
    }

    pub fn optional<T: ToJson>(&mut self, val: Option<T>) -> EncodeResult<()> {
        match val {
            None => self.null(),
            Some(ref v) => self.to_json(v),
        }
    }

    pub fn string<S: Borrow<str>>(&mut self, s: S) -> EncodeResult<()> {
        self.comma_array()?;
        self.writer.write_all(b"\"")?;
        for x in Bytes::new(EscapedChars::new(s.borrow())) {
            self.writer.write_all(&[x])?;
        }
        self.writer.write_all(b"\"")?;
        Ok(())
    }

    pub fn key<S: Borrow<str>>(&mut self, key: S) -> EncodeResult<()> {
        self.comma_object()?;
        self.string(key.borrow())?;
        self.writer.write_all(b":")?;
        Ok(())
    }

    /// Begin encoding a new JSON array.
    ///
    /// Must be paired with a call to `Encoder::end()`.
    pub fn array(&mut self) -> EncodeResult<()> {
        self.comma_array()?;
        self.writer.write_all(b"[")?;
        self.stack.push(Scope::A(false));
        Ok(())
    }

    /// Begin encoding a new JSON object.
    ///
    /// Must be paired with a call to `Encoder::end()`.
    pub fn object(&mut self) -> EncodeResult<()> {
        self.comma_array()?;
        self.writer.write_all(b"{")?;
        self.stack.push(Scope::O(false));
        Ok(())
    }

    /// End a JSON array or object.
    pub fn end(&mut self) -> EncodeResult<()> {
        match self.stack.pop() {
            Some(Scope::A(_)) => self.writer.write_all(b"]").map_err(From::from),
            Some(Scope::O(_)) => self.writer.write_all(b"}").map_err(From::from),
            None => Ok(()),
        }
    }

    fn comma_array(&mut self) -> EncodeResult<()> {
        match self.stack.top() {
            Some(Scope::A(true)) => self.writer.write_all(b",").map_err(From::from),
            Some(Scope::A(false)) => {
                self.stack.set();
                Ok(())
            }
            _ => Ok(()),
        }
    }

    fn comma_object(&mut self) -> EncodeResult<()> {
        match self.stack.top() {
            Some(Scope::O(true)) => self.writer.write_all(b",").map_err(From::from),
            Some(Scope::O(false)) => {
                self.stack.set();
                Ok(())
            }
            _ => Ok(()),
        }
    }
}

// Encoder Error Type ///////////////////////////////////////////////////////

pub type EncodeResult<A> = Result<A, EncodeError>;

#[derive(Debug)]
pub enum EncodeError {
    Io(io::Error),
    /// A float value such as `NAN` or `INFINITY` was used.
    InvalidFloat,
    /// Generic error message.
    Message(&'static str),
    /// Some other error trait impl.
    Other(Box<dyn Error + Send + Sync>),
}

impl fmt::Display for EncodeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match *self {
            EncodeError::Io(ref e) => write!(f, "i/o: {:?}", e),
            EncodeError::InvalidFloat => write!(f, "invalid f64 (NaN | Infinity)"),
            EncodeError::Message(m) => write!(f, "error: {}", m),
            EncodeError::Other(ref e) => write!(f, "other: {}", e),
        }
    }
}

impl Error for EncodeError {
    fn description(&self) -> &str {
        match *self {
            EncodeError::Io(_) => "i/o error",
            EncodeError::InvalidFloat => "invalid float value (e.g. NAN or INFINITY)",
            EncodeError::Message(_) => "generic error message",
            EncodeError::Other(_) => "other error",
        }
    }

    fn cause(&self) -> Option<&dyn Error> {
        match *self {
            EncodeError::Io(ref e) => Some(e),
            EncodeError::Other(ref e) => Some(&**e),
            _ => None,
        }
    }
}

impl From<io::Error> for EncodeError {
    fn from(e: io::Error) -> EncodeError {
        EncodeError::Io(e)
    }
}

// Character conversion support /////////////////////////////////////////////

struct EscapedChars<'r> {
    source: Chars<'r>,
    buffer: [u8; 5],
    index: Option<(usize, usize)>,
}

impl<'r> EscapedChars<'r> {
    fn new(s: &'r str) -> EscapedChars<'r> {
        EscapedChars {
            source: s.chars(),
            buffer: [0; 5],
            index: None,
        }
    }

    fn chr(x: u8) -> u8 {
        match x {
            0x0..=0x9 => b'0' + x,
            0xA..=0xF => b'A' + x - 0xA,
            _ => panic!("{} > 0xF", x),
        }
    }
}

impl<'r> Iterator for EscapedChars<'r> {
    type Item = char;

    fn next(&mut self) -> Option<char> {
        match self.index {
            None => (),
            Some((i, e)) => {
                if i < e {
                    self.index = Some((i + 1, e));
                    return Some(self.buffer[i] as char);
                } else {
                    self.index = None
                }
            }
        }
        match self.source.next() {
            Some(x @ '\\') | Some(x @ '"') => {
                self.buffer[0] = x as u8;
                self.index = Some((0, 1));
                Some('\\')
            }
            Some('\n') => {
                self.buffer[0] = b'n';
                self.index = Some((0, 1));
                Some('\\')
            }
            Some('\t') => {
                self.buffer[0] = b't';
                self.index = Some((0, 1));
                Some('\\')
            }
            Some('\r') => {
                self.buffer[0] = b'r';
                self.index = Some((0, 1));
                Some('\\')
            }
            Some(x @ '\x00'..='\x1F') | Some(x @ '\x7F') => {
                self.buffer[0] = b'u';
                self.buffer[1] = b'0';
                self.buffer[2] = b'0';
                self.buffer[3] = Self::chr(x as u8 >> 4);
                self.buffer[4] = Self::chr(x as u8 & 0x0F);
                self.index = Some((0, 5));
                Some('\\')
            }
            x => x,
        }
    }
}

struct Bytes<I> {
    src: I,
    buf: [u8; 4],
    pos: usize,
    end: usize,
}

impl<I> Bytes<I> {
    pub fn new(i: I) -> Bytes<I> {
        Bytes {
            src: i,
            buf: [0; 4],
            pos: 0,
            end: 0,
        }
    }
}

impl<I: Iterator<Item = char>> Iterator for Bytes<I> {
    type Item = u8;

    fn next(&mut self) -> Option<u8> {
        if self.pos == self.end {
            match self.src.next() {
                Some(c) => {
                    self.end = c.encode_utf8(&mut self.buf).len();
                    debug_assert!(self.end > 0);
                    self.pos = 0
                }
                None => return None,
            }
        }
        let x = self.buf[self.pos];
        self.pos += 1;
        Some(x)
    }
}
