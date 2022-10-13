extern crate json;
extern crate quickcheck;

use json::{Json, Encoder, Decoder, Config, EncodeResult};
use json::decoder::ReadIter;
use quickcheck::{quickcheck, Arbitrary, Gen};
use std::collections::HashMap;
use std::io::Cursor;

#[test]
pub fn identity_json() {
    fn prop(x: SomeJson) -> bool {
        id(|e| e.encode(&x.0), |mut d| d.decode().map(|y| x.0 == y).unwrap_or(false))
    }
    quickcheck(prop as fn(SomeJson) -> bool)
}

#[test]
pub fn identity_null() {
    fn prop() -> bool {
        id(|e| e.null(), |mut d| d.null().map(|_| true).unwrap_or(false))
    }
    quickcheck(prop as fn() -> bool)
}

#[test]
pub fn identity_bool() {
    fn prop(x: bool) -> bool {
        id(|e| e.bool(x), |mut d| d.bool().map(|y| x == y).unwrap_or(false))
    }
    quickcheck(prop as fn(bool) -> bool)
}

#[test]
pub fn identity_string() {
    fn prop(x: String) -> bool {
        id(|e| e.string(x.as_str()), |mut d| d.string().map(|y| &x == &y).unwrap_or(false))
    }
    quickcheck(prop as fn(String) -> bool)
}

#[test]
pub fn identity_u8() {
    fn prop(x: u8) -> bool {
        id(|e| e.u8(x), |mut d| d.u8().map(|y| x == y).unwrap_or(false))
    }
    quickcheck(prop as fn(u8) -> bool)
}

#[test]
pub fn identity_u16() {
    fn prop(x: u16) -> bool {
        id(|e| e.u16(x), |mut d| d.u16().map(|y| x == y).unwrap_or(false))
    }
    quickcheck(prop as fn(u16) -> bool)
}

#[test]
pub fn identity_u32() {
    fn prop(x: u32) -> bool {
        id(|e| e.u32(x), |mut d| d.u32().map(|y| x == y).unwrap_or(false))
    }
    quickcheck(prop as fn(u32) -> bool)
}

#[test]
pub fn identity_u64() {
    fn prop(x: u64) -> bool {
        id(|e| e.u64(x), |mut d| d.u64().map(|y| x == y).unwrap_or(false))
    }
    quickcheck(prop as fn(u64) -> bool)
}

#[test]
pub fn identity_i8() {
    fn prop(x: i8) -> bool {
        id(|e| e.i8(x), |mut d| d.i8().map(|y| x == y).unwrap_or(false))
    }
    quickcheck(prop as fn(i8) -> bool)
}

#[test]
pub fn identity_i16() {
    fn prop(x: i16) -> bool {
        id(|e| e.i16(x), |mut d| d.i16().map(|y| x == y).unwrap_or(false))
    }
    quickcheck(prop as fn(i16) -> bool)
}

#[test]
pub fn identity_i32() {
    fn prop(x: i32) -> bool {
        id(|e| e.i32(x), |mut d| d.i32().map(|y| x == y).unwrap_or(false))
    }
    quickcheck(prop as fn(i32) -> bool)
}

#[test]
pub fn identity_i64() {
    fn prop(x: i64) -> bool {
        id(|e| e.i64(x), |mut d| d.i64().map(|y| x == y).unwrap_or(false))
    }
    quickcheck(prop as fn(i64) -> bool)
}

#[test]
pub fn identity_f64() {
    fn prop(x: f64) -> bool {
        id(|e| e.f64(x), |mut d| d.f64().map(|y| x == y).unwrap_or(false))
    }
    quickcheck(prop as fn(f64) -> bool)
}

// Helpers //////////////////////////////////////////////////////////////////

fn id<F, G>(enc: F, dec: G) -> bool
    where F: Fn(&mut Encoder<Cursor<Vec<u8>>>) -> EncodeResult<()>,
          G: Fn(Decoder<ReadIter<Cursor<Vec<u8>>>>) -> bool
{
    let mut e = Encoder::new(Cursor::new(Vec::new()));
    match enc(&mut e) {
        Ok(()) => {
            let mut c = e.into_writer();
            c.set_position(0);
            dec(Decoder::new(Config::default(), ReadIter::new(c)))
        }
        Err(err) => panic!("encoder failure: {:?}", err)
    }
}

fn gen_json<G: Gen>(level: u16, g: &mut G) -> Json {
    match g.gen_range(1, 8) {
        1 => Json::Bool(true),
        2 => Json::Bool(false),
        3 => Json::Number(g.gen()),
        4 => Json::String(Arbitrary::arbitrary(g)),
        5 => Json::Array(
            if level > 0 {
                gen_array(level - 1, g)
            } else {
                Vec::new()
            }),
        6 => Json::Object(
            if level > 0 {
                gen_object(level - 1, g)
            } else {
                HashMap::new()
            }),
        _ => Json::Null
    }
}

fn gen_array<G: Gen>(level: u16, g: &mut G) -> Vec<Json> {
    let     len = g.gen_range(0, 64);
    let mut vec = Vec::with_capacity(len);
    for _ in 0 .. len {
        vec.push(gen_json(level, g))
    }
    vec
}

fn gen_object<G: Gen>(level: u16, g: &mut G) -> HashMap<String, Json> {
    let     len = g.gen_range(0, 64);
    let mut obj = HashMap::new();
    for _ in 0 .. len {
        obj.insert(Arbitrary::arbitrary(g), gen_json(level, g));
    }
    obj
}

#[derive(Clone, Debug)]
pub struct SomeJson(pub Json);

impl Arbitrary for SomeJson {
    fn arbitrary<G: Gen>(g: &mut G) -> SomeJson {
        SomeJson(gen_json(1, g))
    }
}
