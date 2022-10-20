//! JSON ([RFC 7159](http://tools.ietf.org/html/rfc7159)) encoder
//! and decoder implementations.

#[macro_use]
pub mod macros;

pub mod ast;
mod buffer;
pub mod decoder;
pub mod encoder;
mod stack;
mod utf8;

pub use ast::Json;
pub use buffer::Utf8Buffer;
pub use decoder::{Config, DecodeError, DecodeResult, Decoder, FromJson};
pub use encoder::{EncodeError, EncodeResult, Encoder, ToJson};
