#[macro_export]
/// Macro to support extraction of subsets of JSON object fields.
///
/// Optionally `extract!` accepts a `Utf8Buffer` to use when
/// decoding object keys.
///
/// # Example:
///
/// ```
/// #
/// #[macro_use] extern crate json_codec_wasm;
/// # fn main() {
///
/// use json_codec_wasm::Decoder;
///
/// let mut d = Decoder::default(r#"{"x": 0, "y": 1}"#.chars());
///
/// let p = extract! {
///     let decoder = d;
///     x: req. u32 = "x" => d.from_json(),
///     y: req. u32 = "y" => d.from_json()
/// }.unwrap();
///
/// assert_eq!(0, p.x);
/// assert_eq!(1, p.y);
/// # }
/// ```
macro_rules! extract {
    (
      let decoder = $dec: ident;
      let buffer  = $buf: expr;
      $($name: ident: $modus: ident. $typ: ty = $key: expr => $action: expr),+
    ) => {{
        struct X {
            $($name: $typ),+
        }
        object! {
            let decoder = $dec;
            let buffer  = &mut $buf;
            X {
                $($name: $modus. $key => $action),+
            }
        }
    }};
    (
      let decoder = $dec: ident;
      $($name: ident: $modus: ident. $typ: ty = $key: expr => $action: expr),+
    ) => {{
        struct X {
            $($name: $typ),+
        }
        object! {
            let decoder = $dec;
            X {
                $($name: $modus. $key => $action),+
            }
        }
    }};
}

#[macro_export]
/// Macro to support declarative decoding into struct types.
///
/// Optionally `object!` accepts a `Utf8Buffer` to use when
/// decoding object keys.
///
/// # Example:
///
/// ```
/// #
/// #[macro_use] extern crate json_codec_wasm;
/// # fn main() {
///
/// use json_codec_wasm::Decoder;
///
/// #[derive(Debug, PartialEq)]
/// struct Point {
///     x: u32,
///     y: u32
/// }
///
/// let mut d = Decoder::default(r#"{"x": 0, "y": 1}"#.chars());
///
/// let p = object! {
///     let decoder = d;
///     Point {
///         x: req. "x" => d.u32(),
///         y: req. "y" => d.u32()
///     }
/// };
///
/// assert_eq!(Some(Point { x: 0, y: 1}), p.ok());
/// # }
/// ```
macro_rules! object {
    (
      let decoder = $dec: ident;
      let buffer  = $buf: expr;
      $T: ident {
          $($name: ident: $modus: ident. $key: expr => $action: expr),+
      }
    ) => {{
        $dec.object().and_then(|()| {
            $(let mut $name = None;)+
            while $dec.has_more()? {
                $buf.reset();
                $dec.key_str($buf, false)?;
                match $buf.as_str() {
                    $($key => { $name = Some($action?) })+
                    _      => { $dec.skip()? }
                }
            }
            Ok($T {
                $($name: to_field!($key, $name, $modus),)+
            })
        })
    }};
    (
      let decoder = $dec: ident;
      $T: ident {
          $($name: ident: $modus: ident. $key: expr => $action: expr),+
      }
    ) => {{
        $dec.object().and_then(|()| {
            $(let mut $name = None;)+
            while $dec.has_more()? {
                match $dec.key()?.as_ref() {
                    $($key => { $name = Some($action?) })+
                    _      => { $dec.skip()? }
                }
            }
            Ok($T {
                $($name: to_field!($key, $name, $modus),)+
            })
        })
    }};
}

#[macro_export]
macro_rules! to_field {
    ($msg: expr, $e: expr, opt) => {
        match $e {
            Some(e) => e,
            None => None,
        }
    };
    ($msg: expr, $e: expr, req) => {
        match $e {
            Some(e) => e,
            None => return Err($crate::DecodeError::Expected($msg)),
        }
    };
}

#[macro_export]
/// Macro to support declarative decoding into `Vec`.
///
/// This only supports homogenous JSON arrays. To decode
/// arrays with different element types use `Decoder::array`.
macro_rules! array {
    ($dec: ident, $action: expr) => {{
        $dec.array().and_then(|()| {
            let mut v = Vec::new();
            while $dec.has_more()? {
                v.push($action?)
            }
            Ok(v)
        })
    }};
}
