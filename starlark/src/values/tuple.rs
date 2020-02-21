// Copyright 2018 The Starlark in Rust Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Define the tuple type for Starlark.
use crate::values::error::ValueError;
use crate::values::iter::TypedIterable;
use crate::values::*;
use std::cmp::Ordering;
use std::collections::hash_map::DefaultHasher;
use std::hash::Hasher;

pub(crate) fn slice_vector<'a, V: ValueLike + 'static, I: Iterator<Item = &'a V>>(
    start: i64,
    stop: i64,
    stride: i64,
    content: I,
) -> Vec<Value> {
    let (low, take, astride) = if stride < 0 {
        (stop + 1, start - stop, -stride)
    } else {
        (start, stop - start, stride)
    };
    if take <= 0 {
        return Vec::new();
    }
    let mut v: Vec<Value> = content
        .skip(low as usize)
        .take(take as usize)
        .map(|e| e.clone_value())
        .collect();
    if stride < 0 {
        v.reverse();
    }
    v.into_iter()
        .enumerate()
        .filter_map(|x| {
            if 0 == (x.0 as i64 % astride) {
                Some(x.1)
            } else {
                None
            }
        })
        .collect()
}

impl Tuple {
    pub fn new(values: Vec<Value>) -> Tuple {
        Tuple { content: values }
    }
}

impl From<()> for Tuple {
    fn from(_a: ()) -> Tuple {
        Tuple { content: vec![] }
    }
}

// TODO: Can we do that with macro? i.e. generating the index number automatically?
impl<T: Into<Value>> From<(T,)> for Tuple {
    fn from(a: (T,)) -> Tuple {
        Tuple {
            content: vec![a.0.into()],
        }
    }
}

impl<T1: Into<Value>, T2: Into<Value>> From<(T1, T2)> for Tuple {
    fn from(a: (T1, T2)) -> Tuple {
        Tuple {
            content: vec![a.0.into(), a.1.into()],
        }
    }
}

impl<T1: Into<Value>, T2: Into<Value>, T3: Into<Value>> From<(T1, T2, T3)> for Tuple {
    fn from(a: (T1, T2, T3)) -> Tuple {
        Tuple {
            content: vec![a.0.into(), a.1.into(), a.2.into()],
        }
    }
}

impl<T1: Into<Value>, T2: Into<Value>, T3: Into<Value>, T4: Into<Value>> From<(T1, T2, T3, T4)>
    for Tuple
{
    fn from(a: (T1, T2, T3, T4)) -> Tuple {
        Tuple {
            content: vec![a.0.into(), a.1.into(), a.2.into(), a.3.into()],
        }
    }
}

impl<T1: Into<Value>, T2: Into<Value>, T3: Into<Value>, T4: Into<Value>, T5: Into<Value>>
    From<(T1, T2, T3, T4, T5)> for Tuple
{
    fn from(a: (T1, T2, T3, T4, T5)) -> Tuple {
        Tuple {
            content: vec![a.0.into(), a.1.into(), a.2.into(), a.3.into(), a.4.into()],
        }
    }
}

impl<
        T1: Into<Value>,
        T2: Into<Value>,
        T3: Into<Value>,
        T4: Into<Value>,
        T5: Into<Value>,
        T6: Into<Value>,
    > From<(T1, T2, T3, T4, T5, T6)> for Tuple
{
    fn from(a: (T1, T2, T3, T4, T5, T6)) -> Tuple {
        Tuple {
            content: vec![
                a.0.into(),
                a.1.into(),
                a.2.into(),
                a.3.into(),
                a.4.into(),
                a.5.into(),
            ],
        }
    }
}

impl<
        T1: Into<Value>,
        T2: Into<Value>,
        T3: Into<Value>,
        T4: Into<Value>,
        T5: Into<Value>,
        T6: Into<Value>,
        T7: Into<Value>,
    > From<(T1, T2, T3, T4, T5, T6, T7)> for Tuple
{
    fn from(a: (T1, T2, T3, T4, T5, T6, T7)) -> Tuple {
        Tuple {
            content: vec![
                a.0.into(),
                a.1.into(),
                a.2.into(),
                a.3.into(),
                a.4.into(),
                a.5.into(),
                a.6.into(),
            ],
        }
    }
}

impl<
        T1: Into<Value>,
        T2: Into<Value>,
        T3: Into<Value>,
        T4: Into<Value>,
        T5: Into<Value>,
        T6: Into<Value>,
        T7: Into<Value>,
        T8: Into<Value>,
    > From<(T1, T2, T3, T4, T5, T6, T7, T8)> for Tuple
{
    fn from(a: (T1, T2, T3, T4, T5, T6, T7, T8)) -> Tuple {
        Tuple {
            content: vec![
                a.0.into(),
                a.1.into(),
                a.2.into(),
                a.3.into(),
                a.4.into(),
                a.5.into(),
                a.6.into(),
                a.7.into(),
            ],
        }
    }
}

impl<
        T1: Into<Value>,
        T2: Into<Value>,
        T3: Into<Value>,
        T4: Into<Value>,
        T5: Into<Value>,
        T6: Into<Value>,
        T7: Into<Value>,
        T8: Into<Value>,
        T9: Into<Value>,
    > From<(T1, T2, T3, T4, T5, T6, T7, T8, T9)> for Tuple
{
    fn from(a: (T1, T2, T3, T4, T5, T6, T7, T8, T9)) -> Tuple {
        Tuple {
            content: vec![
                a.0.into(),
                a.1.into(),
                a.2.into(),
                a.3.into(),
                a.4.into(),
                a.5.into(),
                a.6.into(),
                a.7.into(),
                a.8.into(),
            ],
        }
    }
}

impl<
        T1: Into<Value>,
        T2: Into<Value>,
        T3: Into<Value>,
        T4: Into<Value>,
        T5: Into<Value>,
        T6: Into<Value>,
        T7: Into<Value>,
        T8: Into<Value>,
        T9: Into<Value>,
        T10: Into<Value>,
    > From<(T1, T2, T3, T4, T5, T6, T7, T8, T9, T10)> for Tuple
{
    fn from(a: (T1, T2, T3, T4, T5, T6, T7, T8, T9, T10)) -> Tuple {
        Tuple {
            content: vec![
                a.0.into(),
                a.1.into(),
                a.2.into(),
                a.3.into(),
                a.4.into(),
                a.5.into(),
                a.6.into(),
                a.7.into(),
                a.8.into(),
                a.9.into(),
            ],
        }
    }
}

impl From<Tuple> for Value {
    fn from(t: Tuple) -> Value {
        Value::new_mutable(t)
    }
}

#[derive(Clone, Default)]
pub struct TupleGen<T: ValueLike> {
    content: Vec<T>,
}

pub type Tuple = TupleGen<Value>;
pub type FrozenTuple = TupleGen<FrozenValue>;

pub trait TupleLike {
    fn len(&self) -> usize;
    fn iter<'a>(&'a self) -> Box<dyn Iterator<Item = Value> + 'a>;
}

impl<T: ValueLike> TupleGen<T> {
    fn content(&self) -> &Vec<T> {
        &self.content
    }
}

pub trait TupleBase {
    fn content_mut(&mut self) -> &mut Vec<Value>;
}

impl TupleBase for Tuple {
    fn content_mut(&mut self) -> &mut Vec<Value> {
        &mut self.content
    }
}

impl TupleBase for FrozenTuple {
    fn content_mut(&mut self) -> &mut Vec<Value> {
        panic!()
    }
}

impl<T: ValueLike> TupleLike for TupleGen<T> {
    fn len(&self) -> usize {
        self.content.len()
    }

    fn iter<'a>(&'a self) -> Box<dyn Iterator<Item = Value> + 'a> {
        Box::new(self.content.iter().map(|e| e.clone_value()))
    }
}

impl MutableValue for Tuple {
    fn freeze(&self) -> Result<FrozenValue, ValueError> {
        let mut frozen = Vec::new();
        for v in self.content() {
            frozen.push(v.freeze()?)
        }
        Ok(FrozenValue::make_immutable(FrozenTuple { content: frozen }))
    }
    fn as_dyn_any_mut(&mut self) -> &mut dyn Any {
        self
    }
}

impl ImmutableValue for FrozenTuple {
    fn as_owned_value(&self) -> Box<dyn MutableValue> {
        let vals: Vec<_> = self.content.iter().map(|e| e.shared()).collect();
        Box::new(Tuple { content: vals })
    }
}

pub trait ValueAsTuple {
    fn as_tuple(&self) -> Option<VRef<dyn TupleLike>>;
}

pub trait ValueAsTupleMut {
    fn as_tuple_mut(&mut self) -> Result<Option<VRefMut<Tuple>>, ValueError>;
}

impl ValueAsTupleMut for Value {
    fn as_tuple_mut(&mut self) -> Result<Option<VRefMut<Tuple>>, ValueError> {
        self.downcast_mut::<Tuple>()
    }
}

impl<T: ValueLike> ValueAsTuple for T {
    fn as_tuple(&self) -> Option<VRef<dyn TupleLike>> {
        self.downcast_ref::<FrozenTuple>()
            .map(|o| VRef::map(o, |e| e as &dyn TupleLike))
            .or_else(|| {
                self.downcast_ref::<Tuple>()
                    .map(|o| VRef::map(o, |e| e as &dyn TupleLike))
            })
    }
}

impl<T: ValueLike + 'static> TypedValue for TupleGen<T>
where
    TupleGen<T>: TupleBase,
{
    fn naturally_mutable(&self) -> bool {
        true
    }

    fn as_dyn_any(&self) -> &dyn Any {
        self
    }
    fn collect_repr(&self, s: &mut String) {
        s.push('(');
        let mut first = true;
        for v in &self.content {
            if first {
                first = false;
            } else {
                s.push_str(", ");
            }
            v.collect_repr(s);
        }

        if self.content.len() == 1 {
            s.push(',');
        }
        s.push(')');
    }
    fn get_type(&self) -> &'static str {
        "tuple"
    }
    fn to_bool(&self) -> bool {
        !self.content.is_empty()
    }
    fn get_hash(&self) -> Result<u64, ValueError> {
        let mut s = DefaultHasher::new();
        for v in self.content.iter() {
            s.write_u64(v.get_hash()?)
        }
        Ok(s.finish())
    }

    fn equals(&self, other: &Value) -> Result<bool, ValueError> {
        if let Some(other) = other.as_tuple() {
            if self.content.len() != other.len() {
                return Ok(false);
            }

            let mut self_iter = TupleLike::iter(self);
            let mut other_iter = other.iter();

            loop {
                match (self_iter.next(), other_iter.next()) {
                    (Some(a), Some(b)) => {
                        if !a.equals(&b)? {
                            return Ok(false);
                        }
                    }
                    (None, None) => {
                        return Ok(true);
                    }
                    _ => unreachable!(),
                }
            }
        } else {
            Err(unsupported!(self, "==", Some(other)))
        }
    }

    fn compare(&self, other: &Value) -> Result<Ordering, ValueError> {
        if let Some(other) = other.as_tuple() {
            let mut iter1 = self.content.iter();
            let mut iter2 = other.iter();
            loop {
                match (iter1.next(), iter2.next()) {
                    (None, None) => return Ok(Ordering::Equal),
                    (None, Some(..)) => return Ok(Ordering::Less),
                    (Some(..), None) => return Ok(Ordering::Greater),
                    (Some(v1), Some(v2)) => {
                        let r = v1.compare(&v2)?;
                        if r != Ordering::Equal {
                            return Ok(r);
                        }
                    }
                }
            }
        } else {
            Err(unsupported!(self, "cmp()", Some(other)))
        }
    }

    fn at(&self, index: Value) -> ValueResult {
        let i = index.convert_index(self.length()?)? as usize;
        Ok(self.content[i].clone_value())
    }

    fn length(&self) -> Result<i64, ValueError> {
        Ok(self.content.len() as i64)
    }

    fn is_in(&self, other: &Value) -> Result<bool, ValueError> {
        for x in self.content.iter() {
            if x.equals(other)? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn slice(
        &self,
        start: Option<Value>,
        stop: Option<Value>,
        stride: Option<Value>,
    ) -> ValueResult {
        let (start, stop, stride) =
            Value::convert_slice_indices(self.length()?, start, stop, stride)?;
        Ok(Value::new_mutable(Tuple::new(slice_vector(
            start,
            stop,
            stride,
            self.content.iter(),
        ))))
    }

    fn iter(&self) -> Result<&dyn TypedIterable, ValueError> {
        Ok(self)
    }

    /// Concatenate `other` to the current value.
    ///
    /// `other` has to be a tuple.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use starlark::values::*;
    /// # use starlark::values::tuple::Tuple;
    /// # assert!(
    /// // (1, 2, 3) + (2, 3) == (1, 2, 3, 2, 3)
    /// Value::from((1,2,3)).add(Value::from((2,3))).unwrap() == Value::from((1, 2, 3, 2, 3))
    /// # );
    /// ```
    fn add(&self, other: &Value) -> Result<Value, ValueError> {
        if let Some(other) = other.as_tuple() {
            let mut result = Tuple {
                content: Vec::with_capacity(self.content.len() + other.len()),
            };
            for x in TupleLike::iter(self) {
                result.content.push(x.clone());
            }
            for x in other.iter() {
                result.content.push(x.clone());
            }
            Ok(result.into())
        } else {
            Err(unsupported!(self, "a", Some(other)))
        }
    }

    fn add_assign(&mut self, other: &Value) -> Result<(), ValueError> {
        if let Some(other) = other.as_tuple() {
            self.content_mut().extend(other.iter());
            Ok(())
        } else {
            Err(unsupported!(self, "+=", Some(other)))
        }
    }

    /// Repeat `other` times this tuple.
    ///
    /// `other` has to be an int or a boolean.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use starlark::values::*;
    /// # use starlark::values::tuple::Tuple;
    /// # assert!(
    /// // (1, 2, 3) * 3 == (1, 2, 3, 1, 2, 3, 1, 2, 3)
    /// Value::from((1,2,3)).mul(Value::from(3)).unwrap()
    ///              == Value::from((1, 2, 3, 1, 2, 3, 1, 2, 3))
    /// # );
    /// ```
    fn mul(&self, other: Value) -> ValueResult {
        match other.downcast_ref::<i64>() {
            Some(l) => {
                let mut result = Tuple {
                    content: Vec::new(),
                };
                for _i in 0..*l {
                    result
                        .content
                        .extend(self.content.iter().map(|e| e.clone_value()));
                }
                Ok(Value::new_mutable(result))
            }
            None => Err(ValueError::IncorrectParameterType),
        }
    }
}

impl<T: ValueLike + 'static> TypedIterable for TupleGen<T> {
    fn to_iter<'a>(&'a self) -> Box<dyn Iterator<Item = Value> + 'a> {
        TupleLike::iter(self)
    }
}

impl From<()> for Value {
    fn from(_a: ()) -> Value {
        Value::new_mutable(Tuple::from(()))
    }
}

macro_rules! from_tuple {
    ($x: ty) => {
        impl From<$x> for Value {
            fn from(a: $x) -> Value {
                Value::new(a)
            }
        }
    };
    ($x: ty, $y: tt) => {
        impl<T: Into<Value> + Clone> From<$x> for Value {
            fn from(a: $x) -> Value {
                Value::new_mutable($y::from(a))
            }
        }
    };
    ($x: ty, $y: tt, noT) => {
        impl From<$x> for Value {
            fn from(a: $x) -> Value {
                Value::new(a as $y)
            }
        }
    };
    ($y: tt, $($x: tt),+) => {
        impl<$($x: Into<Value> + Clone),+> From<($($x),+)> for Value {
            fn from(a: ($($x),+)) -> Value {
                Value::new_mutable($y::from(a))
            }
        }

    };
}

from_tuple!((T,), Tuple);
from_tuple!(Tuple, T1, T2);
from_tuple!(Tuple, T1, T2, T3);
from_tuple!(Tuple, T1, T2, T3, T4);
from_tuple!(Tuple, T1, T2, T3, T4, T5);
from_tuple!(Tuple, T1, T2, T3, T4, T5, T6);
from_tuple!(Tuple, T1, T2, T3, T4, T5, T6, T7);
from_tuple!(Tuple, T1, T2, T3, T4, T5, T6, T7, T8);
from_tuple!(Tuple, T1, T2, T3, T4, T5, T6, T7, T8, T9);
from_tuple!(Tuple, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_to_str() {
        assert_eq!("(1, 2, 3)", Value::from((1, 2, 3)).to_str());
        assert_eq!("(1, (2, 3))", Value::from((1, (2, 3))).to_str());
        assert_eq!("(1,)", Value::from((1,)).to_str());
        assert_eq!("()", Value::from(()).to_str());
    }

    #[test]
    fn test_arithmetic_on_tuple() {
        // (1, 2, 3) + (2, 3) == (1, 2, 3, 2, 3)
        assert_eq!(
            Value::from((1, 2, 3)).add(Value::from((2, 3))).unwrap(),
            Value::from((1, 2, 3, 2, 3))
        );
        // (1, 2, 3) * 3 == (1, 2, 3, 1, 2, 3, 1, 2, 3)
        assert_eq!(
            Value::from((1, 2, 3)).mul(Value::from(3)).unwrap(),
            Value::from((1, 2, 3, 1, 2, 3, 1, 2, 3))
        );
    }

    #[test]
    fn test_is_descendant() {
        let v1 = Value::from((1, 2, 3));
        let v2 = Value::from((1, 2, v1.clone()));
        let v3 = Value::from((1, 2, v2.clone()));
        assert!(v3.is_descendant_value(&v2));
        assert!(v3.is_descendant_value(&v1));
        assert!(v3.is_descendant_value(&v3));

        assert!(v2.is_descendant_value(&v1));
        assert!(v2.is_descendant_value(&v2));
        assert!(!v2.is_descendant_value(&v3));

        assert!(v1.is_descendant_value(&v1));
        assert!(!v1.is_descendant_value(&v2));
        assert!(!v1.is_descendant_value(&v3));
    }
}
