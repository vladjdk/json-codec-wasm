//! JSON ([RFC 7159](http://tools.ietf.org/html/rfc7159)) encoder
//! and decoder implementations.

#[macro_use]
pub mod macros;

mod buffer;
mod stack;
mod utf8;
pub mod ast;
pub mod decoder;
pub mod encoder;

pub use ast::Json;
pub use buffer::Utf8Buffer;
pub use decoder::{FromJson, Decoder, DecodeError, DecodeResult, Config};
pub use encoder::{ToJson, Encoder, EncodeError, EncodeResult};
