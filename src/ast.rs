//! JSON AST definition.
use std::borrow::Borrow;
use std::collections::HashMap;

#[derive(Clone, Debug, PartialEq)]
pub enum Json {
    Bool(bool),
    I128(i128),
    U128(u128),
    String(String),
    Array(Vec<Json>),
    Object(HashMap<String, Json>),
    Null,
}

/// A reference to some `Json` value.
///
/// Mostly used for navigating complex `Json` values
/// and extracting values from specific locations.
pub struct Ref<'r> {
    value: Option<&'r Json>,
}

impl<'r> Ref<'r> {
    pub fn new(v: &'r Json) -> Ref<'r> {
        Ref { value: Some(v) }
    }

    fn of(v: Option<&'r Json>) -> Ref<'r> {
        Ref { value: v }
    }

    pub fn at(&self, i: usize) -> Ref<'r> {
        match self.value {
            Some(&Json::Array(ref a)) => Ref::of(a.get(i)),
            _ => Ref::of(None),
        }
    }

    pub fn get<K: Borrow<str>>(&self, k: K) -> Ref<'r> {
        match self.value {
            Some(&Json::Object(ref m)) => Ref::of(m.get(k.borrow())),
            _ => Ref::of(None),
        }
    }

    pub fn value(&self) -> Option<&Json> {
        self.value
    }

    pub fn opt(&self) -> Option<Ref<'r>> {
        match self.value {
            Some(&Json::Null) => None,
            Some(ref v) => Some(Ref::new(v)),
            _ => None,
        }
    }

    pub fn bool(&self) -> Option<bool> {
        match self.value {
            Some(&Json::Bool(x)) => Some(x),
            _ => None,
        }
    }

    pub fn string(&self) -> Option<&str> {
        match self.value {
            Some(&Json::String(ref x)) => Some(x),
            _ => None,
        }
    }

    pub fn i128(&self) -> Option<i128> {
        match self.value {
            Some(&Json::I128(x)) => Some(x),
            _ => None,
        }
    }

    pub fn u128(&self) -> Option<u128> {
        match self.value {
            Some(&Json::U128(x)) => Some(x),
            _ => None,
        }
    }

    pub fn slice(&self) -> Option<&[Json]> {
        match self.value {
            Some(&Json::Array(ref v)) => Some(v),
            _ => None,
        }
    }
}
