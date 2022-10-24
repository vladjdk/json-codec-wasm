//! JSON ([RFC 7159](http://tools.ietf.org/html/rfc7159))
//! decoder implementation.
//!
//! The decoder supports direct decoding into Rust types (providing
//! helper macros such as `object!`) as well as generic decoding
//! using an intermediate representation.
//!
//! # Example 1: Generic decoding
//!
//! ```
//! use json::{Decoder, Json};
//! use json::ast::Ref;
//!
//! let json = r#"
//! { "field1": true,
//!   "field2": { "nested": [42, 73] }
//! }"#;
//!
//! let mut d = Decoder::default(json.chars());
//! let     v = d.decode().unwrap();
//! let     r = Ref::new(&v);
//! assert_eq!(true, r.get("field1").bool().unwrap());
//! assert_eq!(73i128, r.get("field2").get("nested").at(1).i128().unwrap());
//!
//! ```
//! # Example 2: Direct decoding using macros
//!
//! ```
//! #
//! #[macro_use] extern crate json;
//! # fn main() {
//!
//! use json::Decoder;
//!
//! const JSON: &'static str =
//! r#"
//! {
//!     "Width":  800,
//!     "Height": 600,
//!     "Title":  "View from 15th Floor",
//!     "Thumbnail": {
//!         "Url":    "http://www.example.com/image/481989943",
//!         "Height": 125,
//!         "Width":  100
//!     },
//!     "Animated" : false,
//!     "IDs": [116, 943, 234, 38793]
//! }
//! "#;
//!
//! struct Image {
//!     width:     usize,
//!     height:    usize,
//!     title:     String,
//!     thumbnail: Thumbnail,
//!     animated:  bool,
//!     ids:       Vec<u32>,
//!     geo:       Option<(i128, i128)>
//! }
//!
//! struct Thumbnail {
//!     url:    String,
//!     height: u16,
//!     width:  u16
//! }
//!
//! let mut d = Decoder::default(JSON.chars());
//! let image = object! {
//!     let decoder = d;
//!     Image {
//!         width:     req. "Width"     => d.usize(),
//!         height:    req. "Height"    => d.usize(),
//!         title:     req. "Title"     => d.string(),
//!         thumbnail: req. "Thumbnail" => object! {
//!             let decoder = d;
//!             Thumbnail {
//!                 url:    req. "Url"    => d.string(),
//!                 height: req. "Height" => d.u16(),
//!                 width:  req. "Width"  => d.u16()
//!             }
//!         },
//!         animated:  req. "Animated" => d.bool(),
//!         ids:       req. "IDs"      => array!(d, d.u32()),
//!         geo:       opt. "Geo"      => d.optional(|d| {
//!             let lat = d.i128()?;
//!             let lon = d.i128()?;
//!             Ok((lat, lon))
//!         })
//!     }
//! };
//! assert!(image.is_ok());
//! # }
//! ```

use std::borrow::Cow;
use std::char;
use std::collections::HashMap;
use std::error::Error;
use std::fmt;
use std::io::Read;
use std::marker::PhantomData;
use std::str;
use std::{i16, i32, i64, i8, isize};
use std::{u16, u32, u64, u8, usize};

use ast::Json;
use buffer::{Buffer, Utf8Buffer};
use stack::{Scope, Stack};
use utf8;
pub use utf8::ReadError;

// FromJson trait ///////////////////////////////////////////////////////////

pub trait FromJson {
    fn decode<I: Iterator<Item = char>>(d: &mut Decoder<I>) -> DecodeResult<Self>
    where
        Self: Sized;
}

macro_rules! instance {
    ($name: ident) => {
        impl FromJson for $name {
            fn decode<I: Iterator<Item = char>>(d: &mut Decoder<I>) -> DecodeResult<Self> {
                d.$name()
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

impl FromJson for String {
    fn decode<I: Iterator<Item = char>>(d: &mut Decoder<I>) -> DecodeResult<Self> {
        d.string()
    }
}

impl FromJson for Json {
    fn decode<I: Iterator<Item = char>>(d: &mut Decoder<I>) -> DecodeResult<Self> {
        d.decode()
    }
}

impl<T: FromJson> FromJson for Option<T> {
    fn decode<I: Iterator<Item = char>>(d: &mut Decoder<I>) -> DecodeResult<Self> {
        d.optional(FromJson::decode)
    }
}

impl<'a, T: FromJson + Clone> FromJson for Cow<'a, T> {
    fn decode<I: Iterator<Item = char>>(d: &mut Decoder<I>) -> DecodeResult<Self> {
        Ok(Cow::Owned(FromJson::decode(d)?))
    }
}

impl<T: FromJson> FromJson for Vec<T> {
    fn decode<I: Iterator<Item = char>>(d: &mut Decoder<I>) -> DecodeResult<Self> {
        d.array()?;
        let mut v = Vec::new();
        while d.has_more()? {
            let x = d.from_json()?;
            v.push(x)
        }
        Ok(v)
    }
}

// Decoder //////////////////////////////////////////////////////////////////

/// JSON decoder over `char` iterators.
pub struct Decoder<I: Iterator> {
    chars: Source<I>,
    config: Config,
    buffer: [u8; 512],
    stack: Stack,
}

#[derive(Clone, Debug, PartialEq, Eq)]
/// Decoder configuration.
pub struct Config {
    /// Maximum recursion steps when decoding generic `Json`
    pub max_nesting: usize,
}

const DEFAULT_CONFIG: Config = Config { max_nesting: 16 };

impl Config {
    /// Create default configuration with
    /// - `max_nesting` = 16
    pub fn default() -> Config {
        DEFAULT_CONFIG
    }
}

// Macros ///////////////////////////////////////////////////////////////////

macro_rules! require {
    ($e: expr) => {
        match $e {
            Some(c) => c,
            None => return Err(DecodeError::EndOfInput),
        }
    };
}

macro_rules! integral {
    ($name: ident, $ty: ty, false) => {
        pub fn $name(&mut self) -> DecodeResult<$ty> {
            self.skip_whitespace();
            let digit = require!(self.chars.next())
                .to_digit(10)
                .ok_or(DecodeError::Expected("digit"))?;
            let mut dec = digit as $ty;
            while let Some(c) = self.chars.next() {
                match c.to_digit(10) {
                    Some(n) => {
                        if dec > ($name::MAX - n as $ty) / 10 {
                            return Err(DecodeError::IntOverflow);
                        }
                        dec = dec * 10 + n as $ty;
                    }
                    None => {
                        self.chars.put_back(c);
                        break;
                    }
                }
            }
            Ok(dec)
        }
    };
    ($name: ident, $ty: ty, true) => {
        pub fn $name(&mut self) -> DecodeResult<$ty> {
            self.skip_whitespace();
            let is_neg = match self.chars.peek() {
                Some('-') => {
                    self.chars.next();
                    true
                }
                _ => false,
            };
            let digit = require!(self.chars.next())
                .to_digit(10)
                .ok_or(DecodeError::Expected("digit"))?;
            let mut dec = -(digit as $ty);
            while let Some(c) = self.chars.next() {
                match c.to_digit(10) {
                    Some(n) => {
                        if dec < ($name::MIN + n as $ty) / 10 {
                            return Err(DecodeError::IntOverflow);
                        }
                        dec = dec * 10 - n as $ty;
                    }
                    None => {
                        self.chars.put_back(c);
                        break;
                    }
                }
            }
            Ok(if is_neg { dec } else { -dec })
        }
    };
}

impl<I: Iterator<Item = char>> Decoder<I> {
    pub fn new(c: Config, i: I) -> Decoder<I> {
        Decoder {
            chars: Source::new(i),
            config: c,
            buffer: [0; 512],
            stack: Stack::new(),
        }
    }

    /// Create decoder with default `Config`.
    pub fn default(i: I) -> Decoder<I> {
        Decoder::new(Config::default(), i)
    }

    /// Have we exhausted the iterator?
    pub fn is_end(&mut self) -> bool {
        self.skip_whitespace();
        self.chars.peek().is_none()
    }

    pub fn into_iter(self) -> I {
        self.chars.into_iter()
    }

    pub fn iter_mut(&mut self) -> &mut I {
        self.chars.iter_mut()
    }

    /// Generic conversion from JSON to an instance of `FromJson`.
    pub fn from_json<T: FromJson>(&mut self) -> DecodeResult<T> {
        FromJson::decode(self)
    }

    /// Decode into `Json` AST value.
    pub fn decode(&mut self) -> DecodeResult<Json> {
        let n = self.config.max_nesting;
        self.decode_json(n)
    }

    fn decode_json(&mut self, level: usize) -> DecodeResult<Json> {
        if level == 0 {
            return Err(DecodeError::MaxRecursion);
        }
        self.skip_whitespace();
        match require!(self.chars.peek()) {
            '"' => self.string().map(Json::String),
            't' | 'f' => self.bool().map(Json::Bool),
            'n' => self.null().map(|_| Json::Null),
            '0'..='9' | '-' => self.i128().map(Json::I128),
            '[' => {
                self.array()?;
                let mut v = Vec::new();
                while self.has_more()? {
                    let x = self.decode_json(level - 1)?;
                    v.push(x)
                }
                Ok(Json::Array(v))
            }
            '{' => {
                self.object()?;
                let mut m = HashMap::new();
                while self.has_more()? {
                    let k = self.key()?;
                    let v = self.decode_json(level - 1)?;
                    m.insert(k, v);
                }
                Ok(Json::Object(m))
            }
            chr => return Err(DecodeError::Unexpected(chr)),
        }
    }

    /// Decode as generic Json but ignore the result.
    ///
    /// Semantically this method is equivalent to `Decoder::decode`
    /// but potentially more efficient as it tries to avoid allocating
    /// intermediate values.
    pub fn skip(&mut self) -> DecodeResult<()> {
        let n = self.config.max_nesting;
        let mut b = [0; 0];
        let mut u = Utf8Buffer::new(&mut b);
        self.skip_json(&mut u, n)
    }

    fn skip_json(&mut self, b: &mut Utf8Buffer, level: usize) -> DecodeResult<()> {
        if level == 0 {
            return Err(DecodeError::MaxRecursion);
        }
        self.skip_whitespace();
        match require!(self.chars.peek()) {
            '"' => self.str(b, false).map(|_| ()),
            't' | 'f' => self.bool().map(|_| ()),
            'n' => self.null().map(|_| ()),
            '0'..='9' | '-' => self.i128().map(|_| ()),
            '[' => {
                self.array()?;
                while self.has_more()? {
                    self.skip_json(b, level - 1)?;
                }
                Ok(())
            }
            '{' => {
                self.object()?;
                while self.has_more()? {
                    self.key_str(b, false)?;
                    self.skip_json(b, level - 1)?;
                }
                Ok(())
            }
            chr => return Err(DecodeError::Unexpected(chr)),
        }
    }

    integral!(u8, u8, false);
    integral!(u16, u16, false);
    integral!(u32, u32, false);
    integral!(u64, u64, false);
    integral!(u128, u128, false);
    integral!(usize, usize, false);

    integral!(i8, i8, true);
    integral!(i16, i16, true);
    integral!(i32, i32, true);
    integral!(i64, i64, true);
    integral!(i128, i128, true);
    integral!(isize, isize, true);

    // pub fn i128(&mut self) -> DecodeResult<i128> {
    //     fn is_valid(x: char) -> bool {
    //         match x {
    //             '0'..='9' | '+' | '-' => true,
    //             _ => false,
    //         }
    //     }
    //     self.skip_whitespace();
    //     let is_neg = match self.chars.peek() {
    //         Some('-') => {
    //             self.chars.next();
    //             true
    //         }
    //         _ => false,
    //     };
    //     let d = require!(self.chars.next());
    //     if !d.is_digit(10) {
    //         return Err(DecodeError::Unexpected(d));
    //     }
    //     let mut buf = Utf8Buffer::new(&mut self.buffer);
    //     buf.push(d);
    //     while let Some(c) = self.chars.next() {
    //         if is_valid(c) {
    //             buf.push(c)
    //         } else {
    //             self.chars.put_back(c);
    //             break;
    //         }
    //     }
    //     match buf.as_str().parse::<i128>() {
    //         Err(_) => Err(DecodeError::Number),
    //         Ok(n) => Ok(if is_neg { -n } else { n }),
    //     }
    // }

    pub fn null(&mut self) -> DecodeResult<()> {
        self.skip_whitespace();
        self.matches("null")
    }

    pub fn bool(&mut self) -> DecodeResult<bool> {
        self.skip_whitespace();
        match require!(self.chars.next()) {
            't' => self.matches("rue").map(|_| true),
            'f' => self.matches("alse").map(|_| false),
            chr => Err(DecodeError::Unexpected(chr)),
        }
    }

    pub fn string(&mut self) -> DecodeResult<String> {
        let mut s = String::new();
        self.string_into(&mut s, false)?;
        Ok(s)
    }

    /// Decode a JSON string into the given `Utf8Buffer`.
    ///
    /// If the actual string does not fit into the provided buffer
    /// and `overflow_err` is `true`, `DecodeError::BufferOverflow`
    /// is returned immediately. If `overflow_err` is false we
    /// continue decoding the string, but the buffer will only
    /// contain as much as fits into it.
    pub fn str(&mut self, b: &mut Utf8Buffer, overflow_err: bool) -> DecodeResult<()> {
        self.string_into(b, overflow_err)
    }

    fn string_into<B: Buffer>(&mut self, s: &mut B, overflow_err: bool) -> DecodeResult<()> {
        self.skip_whitespace();
        if self.chars.next() != Some('"') {
            return Err(DecodeError::Expected("\""));
        }
        let mut escaped = false;
        loop {
            match require!(self.chars.next()) {
                chr if escaped => {
                    match chr {
                        '"' => s.push('"'),
                        '/' => s.push('/'),
                        '\\' => s.push('\\'),
                        'b' => s.push('\x08'),
                        'f' => s.push('\x0C'),
                        'n' => s.push('\n'),
                        'r' => s.push('\r'),
                        't' => s.push('\t'),
                        'u' => match self.hex_unicode()? {
                            hi @ 0xD800..=0xDBFF => {
                                self.matches("\\u")?;
                                let lo = self.hex_unicode()?;
                                if lo < 0xDC00 || lo > 0xDFFF {
                                    return Err(DecodeError::UnicodeEscape);
                                }
                                let c =
                                    (((hi - 0xD800) as u32) << 10 | (lo - 0xDC00) as u32) + 0x10000;
                                s.push(char::from_u32(c).unwrap())
                            }
                            0xDC00..=0xDFFF => return Err(DecodeError::UnicodeEscape),
                            x => match char::from_u32(x as u32) {
                                Some(c) => s.push(c),
                                None => return Err(DecodeError::UnicodeEscape),
                            },
                        },
                        c => return Err(DecodeError::Unexpected(c)),
                    }
                    escaped = false
                }
                '\\' => escaped = true,
                '"' => break,
                chr => s.push(chr),
            }
            if overflow_err && s.is_full() {
                return Err(DecodeError::BufferOverflow);
            }
        }
        Ok(())
    }

    /// Decode `null` (which is mapped to `None`) or some other
    /// JSON value (mapped to `Some`).
    pub fn optional<A, F>(&mut self, mut f: F) -> DecodeResult<Option<A>>
    where
        F: FnMut(&mut Decoder<I>) -> DecodeResult<A>,
    {
        self.skip_whitespace();
        match require!(self.chars.peek()) {
            'n' => self.null().map(|_| None),
            _ => f(self).map(Some),
        }
    }

    /// When parsing JSON arrays and objects this needs to be
    /// called in between to check if the array / object end has been
    /// reached. E.g.
    ///
    /// ```
    /// use json::{Decoder, DecodeResult};
    ///
    /// fn foo<I: Iterator<Item=char>>(d: &mut Decoder<I>) -> DecodeResult<Vec<u8>> {
    ///     d.array()?;
    ///     let mut v = Vec::new();
    ///     while d.has_more()? {
    ///         v.push(d.u8()?)
    ///     }
    ///     Ok(v)
    /// }
    /// ```
    pub fn has_more(&mut self) -> DecodeResult<bool> {
        self.skip_whitespace();
        match self.stack.top() {
            Some(Scope::A(false)) => match self.chars.peek() {
                Some(']') => {
                    self.chars.next();
                    self.stack.pop();
                    Ok(false)
                }
                Some(_) => {
                    self.stack.set();
                    Ok(true)
                }
                None => Err(DecodeError::EndOfInput),
            },
            Some(Scope::A(true)) => match self.chars.next() {
                Some(',') => Ok(true),
                Some(']') => {
                    self.stack.pop();
                    Ok(false)
                }
                _ => Err(DecodeError::Expected("',' or ']'")),
            },
            Some(Scope::O(false)) => match self.chars.peek() {
                Some('}') => {
                    self.chars.next();
                    self.stack.pop();
                    Ok(false)
                }
                Some(_) => {
                    self.stack.set();
                    Ok(true)
                }
                None => Err(DecodeError::EndOfInput),
            },
            Some(Scope::O(true)) => match self.chars.next() {
                Some(',') => Ok(true),
                Some('}') => {
                    self.stack.pop();
                    Ok(false)
                }
                _ => Err(DecodeError::Expected("',' or '}'")),
            },
            None => Ok(false),
        }
    }

    /// Begin parsing a JSON array.
    ///
    /// Before each element is parsed, `Decoder::has_more`
    /// needs to be queried.
    pub fn array(&mut self) -> DecodeResult<()> {
        self.skip_whitespace();
        self.matches("[")?;
        self.stack.push(Scope::A(false));
        Ok(())
    }

    /// Create a JSON array iterator to decode a homogenous array.
    ///
    /// ```
    /// use json::Decoder;
    ///
    /// let mut d = Decoder::default("[1,2,3,4]".chars());
    /// let mut v: Vec<u8> = Vec::new();
    ///
    /// for i in d.array_iter().unwrap() {
    ///     v.push(i.unwrap())
    /// }
    /// ```
    pub fn array_iter<A: FromJson>(&mut self) -> DecodeResult<ArrayIter<A, I>> {
        self.array()?;
        Ok(ArrayIter::new(self))
    }

    /// Begin parsing a JSON object.
    ///
    /// Before each key is parsed, `Decoder::has_more`
    /// needs to be queried.
    pub fn object(&mut self) -> DecodeResult<()> {
        self.skip_whitespace();
        self.matches("{")?;
        self.stack.push(Scope::O(false));
        Ok(())
    }

    /// Decode a JSON object key.
    pub fn key(&mut self) -> DecodeResult<String> {
        let mut s = String::new();
        self.key_into(&mut s, false)?;
        Ok(s)
    }

    /// Decode a JSON object key into the given buffer.
    pub fn key_str(&mut self, b: &mut Utf8Buffer, overflow_err: bool) -> DecodeResult<()> {
        self.key_into(b, overflow_err)
    }

    fn key_into<B: Buffer>(&mut self, s: &mut B, overflow_err: bool) -> DecodeResult<()> {
        self.string_into(s, overflow_err)?;
        self.skip_whitespace();
        if self.chars.next() != Some(':') {
            return Err(DecodeError::Expected(":"));
        }
        Ok(())
    }

    fn skip_whitespace(&mut self) {
        while let Some(c) = self.chars.next() {
            if !c.is_whitespace() {
                self.chars.put_back(c);
                break;
            }
        }
    }

    fn hex_unicode(&mut self) -> DecodeResult<u16> {
        let a = hex_byte(require!(self.chars.next()))?;
        let b = hex_byte(require!(self.chars.next()))?;
        let c = hex_byte(require!(self.chars.next()))?;
        let d = hex_byte(require!(self.chars.next()))?;
        Ok(a as u16 * 0x1000 + b as u16 * 0x100 + c as u16 * 0x10 + d as u16)
    }

    fn matches(&mut self, pattern: &str) -> DecodeResult<()> {
        for a in pattern.chars() {
            let b = require!(self.chars.next());
            if a != b {
                return Err(DecodeError::Unexpected(b));
            }
        }
        Ok(())
    }
}

fn hex_byte(digit: char) -> DecodeResult<u8> {
    match digit {
        '0' => Ok(0),
        '1' => Ok(1),
        '2' => Ok(2),
        '3' => Ok(3),
        '4' => Ok(4),
        '5' => Ok(5),
        '6' => Ok(6),
        '7' => Ok(7),
        '8' => Ok(8),
        '9' => Ok(9),
        'A' | 'a' => Ok(10),
        'B' | 'b' => Ok(11),
        'C' | 'c' => Ok(12),
        'D' | 'd' => Ok(13),
        'E' | 'e' => Ok(14),
        'F' | 'f' => Ok(15),
        chr => Err(DecodeError::Unexpected(chr)),
    }
}

// DecodeError //////////////////////////////////////////////////////////////

pub type DecodeResult<A> = Result<A, DecodeError>;

#[derive(Debug)]
pub enum DecodeError {
    /// The underlying iterator stopped giving us new values.
    EndOfInput,
    /// An expectation was not met while decoding.
    Expected(&'static str),
    /// During generic JSON decoding too many nesting levels had
    /// been encountered. See `Config` for details.
    MaxRecursion,
    /// When decoding integer values, the actual JSON digits exceeded
    /// the possible value range.
    IntOverflow,
    /// An unexpected character was encountered.
    Unexpected(char),
    /// An invalid unicode escape sequence was found when
    /// decoding a JSON string.
    UnicodeEscape,
    /// Decoding a numeric value failed.
    Number,
    /// A JSON string did not fit into the provided `Utf8Buffer`.
    BufferOverflow,
    /// Generic error message.
    Message(&'static str),
    /// Some other `Error` trait impl.
    Other(Box<dyn Error + Send + Sync>),
}

impl fmt::Display for DecodeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match *self {
            DecodeError::EndOfInput => write!(f, "end of input"),
            DecodeError::Expected(e) => write!(f, "expected \"{}\"", e),
            DecodeError::MaxRecursion => write!(f, "max. number of recursions reached"),
            DecodeError::IntOverflow => write!(f, "integer overflow"),
            DecodeError::Unexpected(c) => write!(f, "unexpected \"{}\"", c),
            DecodeError::UnicodeEscape => write!(f, "invalid unicode escape"),
            DecodeError::Number => write!(f, "failed to parse number"),
            DecodeError::BufferOverflow => write!(f, "buffer overflow"),
            DecodeError::Message(m) => write!(f, "error: {}", m),
            DecodeError::Other(ref e) => write!(f, "other: {}", e),
        }
    }
}

impl Error for DecodeError {
    fn description(&self) -> &str {
        match *self {
            DecodeError::EndOfInput => "end of input",
            DecodeError::Expected(_) => "expected some string",
            DecodeError::MaxRecursion => "objects/arrays are too deeply nested",
            DecodeError::IntOverflow => "integer overflow",
            DecodeError::Unexpected(_) => "unexpected char",
            DecodeError::UnicodeEscape => "invalid unicode escape sequence",
            DecodeError::Number => "failed to decode number",
            DecodeError::BufferOverflow => "buffer too small to hold value",
            DecodeError::Message(_) => "generic error message",
            DecodeError::Other(_) => "other error",
        }
    }

    fn cause(&self) -> Option<&dyn Error> {
        match *self {
            DecodeError::Other(ref e) => Some(&**e),
            _ => None,
        }
    }
}

// Source ///////////////////////////////////////////////////////////////////

struct Source<I: Iterator> {
    iter: I,
    front: Option<I::Item>,
}

impl<I: Iterator> Source<I> {
    fn new(i: I) -> Source<I> {
        Source {
            iter: i,
            front: None,
        }
    }

    fn put_back(&mut self, i: I::Item) {
        self.front = Some(i)
    }

    fn peek(&mut self) -> Option<I::Item>
    where
        I::Item: Copy,
    {
        self.next().map(|c| {
            self.put_back(c);
            c
        })
    }

    fn into_iter(self) -> I {
        self.iter
    }

    fn iter_mut(&mut self) -> &mut I {
        &mut self.iter
    }
}

impl<I: Iterator> Iterator for Source<I> {
    type Item = I::Item;

    fn next(&mut self) -> Option<I::Item> {
        self.front.take().or_else(|| self.iter.next())
    }
}

// ArrayIter /////////////////////////////////////////////////////////////////

/// Iterator over JSON array elements.
///
/// Used in conjunction with homogenous JSON arrays.
pub struct ArrayIter<'r, A, I>
where
    I: Iterator<Item = char> + 'r,
{
    dec: &'r mut Decoder<I>,
    _ty: PhantomData<A>,
}

impl<'r, A, I> ArrayIter<'r, A, I>
where
    I: Iterator<Item = char> + 'r,
{
    fn new(d: &'r mut Decoder<I>) -> ArrayIter<'r, A, I> {
        ArrayIter {
            dec: d,
            _ty: PhantomData,
        }
    }
}

impl<'r, A, I> Iterator for ArrayIter<'r, A, I>
where
    I: Iterator<Item = char> + 'r,
    A: FromJson,
{
    type Item = DecodeResult<A>;

    fn next(&mut self) -> Option<DecodeResult<A>> {
        match self.dec.has_more() {
            Ok(true) => Some(self.dec.from_json()),
            Ok(false) => None,
            Err(e) => Some(Err(e)),
        }
    }
}

// ReadIter /////////////////////////////////////////////////////////////////

/// Iterator over characters read from any `Read`-type.
///
/// Uses the `chars` method of the `Read` interface. Since `Decoder`s
/// expect iterators over plain `char`s this iterator yields `None`
/// whenever the underlying `Chars` iterator returned an error.
pub struct ReadIter<R: Read> {
    iter: utf8::Chars<R>,
    error: Option<ReadError>,
}

impl<R: Read> ReadIter<R> {
    pub fn new(r: R) -> ReadIter<R> {
        ReadIter {
            iter: utf8::Chars::new(r),
            error: None,
        }
    }

    /// Get the error that has been encountered (if any).
    pub fn error(&self) -> Option<&utf8::ReadError> {
        self.error.as_ref()
    }

    /// Get and remove the error that has been encountered (if any).
    pub fn take_error(&mut self) -> Option<utf8::ReadError> {
        self.error.take()
    }
}

impl<R: Read> Iterator for ReadIter<R> {
    type Item = char;

    fn next(&mut self) -> Option<char> {
        match self.iter.next() {
            Some(Ok(c)) => Some(c),
            Some(Err(e)) => {
                self.error = Some(e);
                None
            }
            None => None,
        }
    }
}

// Tests ////////////////////////////////////////////////////////////////////

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty1() {
        let mut d = Decoder::default(r#"[{}]"#.chars());
        d.decode().unwrap();
    }

    #[test]
    fn empty2() {
        let mut d = Decoder::default(r#"[]"#.chars());
        d.array().unwrap();
        assert!(!d.has_more().unwrap())
    }

    #[test]
    fn object() {
        let mut d = Decoder::default(r#" {"outer": {"inner": 32 } } "#.chars());
        d.object().unwrap();
        assert!(d.has_more().unwrap());
        let k = d.key().unwrap();
        assert_eq!("outer", &k);
        d.object().unwrap();
        assert!(d.has_more().unwrap());
        let k = d.key().unwrap();
        assert_eq!("inner", &k);
        let v = d.isize().unwrap();
        assert_eq!(32, v);
        assert!(!d.has_more().unwrap());
        assert!(!d.has_more().unwrap());
    }

    #[test]
    fn array() {
        let mut d = Decoder::default(" [ [   [1, 2  ,3], 42 ] ]   ".chars());
        d.array().unwrap();
        assert!(d.has_more().unwrap());
        d.array().unwrap();
        assert!(d.has_more().unwrap());
        d.array().unwrap();
        assert!(d.has_more().unwrap());
        let a = d.isize().unwrap();
        assert!(d.has_more().unwrap());
        let b = d.isize().unwrap();
        assert!(d.has_more().unwrap());
        let c = d.isize().unwrap();
        assert!(!d.has_more().unwrap());
        assert!(d.has_more().unwrap());
        let x = d.isize().unwrap();
        assert!(!d.has_more().unwrap());
        assert!(!d.has_more().unwrap());
        assert_eq!((1, 2, 3, 42), (a, b, c, x))
    }

    #[test]
    fn array_iter() {
        let mut d = Decoder::new(Config::default(), "[ true, false, true ]".chars());
        let mut v = Vec::new();
        for x in d.array_iter().unwrap() {
            v.push(x.unwrap())
        }
        assert_eq!(vec![true, false, true], v)
    }

    #[test]
    fn array_macro() {
        fn read_array() -> DecodeResult<Vec<bool>> {
            let mut d = Decoder::new(Config::default(), "[ true, false, true ]".chars());
            array!(d, d.bool())
        }
        assert_eq!(vec![true, false, true], read_array().unwrap())
    }

    #[test]
    fn numbers() {
        let mut d =
            Decoder::default("1 0 -1 18446744073709551615 -9223372036854775808 255 256".chars());
        assert_eq!(1, d.u8().unwrap());
        assert_eq!(0, d.u8().unwrap());
        assert_eq!(-1, d.i8().unwrap());
        assert_eq!(18446744073709551615, d.u64().unwrap());
        assert_eq!(-9223372036854775808, d.i64().unwrap());
        assert_eq!(255, d.u8().unwrap());
        match d.u8() {
            Err(DecodeError::IntOverflow) => (),
            other => panic!("unexpected result: {:?}", other),
        }
    }

    #[test]
    fn generic() {
        let mut d = Decoder::default("null".chars());
        assert_eq!(None, d.from_json::<Option<u8>>().unwrap());

        let mut d = Decoder::default("100".chars());
        assert_eq!(Some(100u8), d.from_json().unwrap())
    }
}
