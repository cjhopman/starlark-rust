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

//! Define the list type of Starlark
use crate::stdlib::list::LIST_REMOVE_ELEMENT_NOT_FOUND_ERROR_CODE;
use crate::values::error::{RuntimeError, ValueError};
use crate::values::iter::TypedIterable;
use crate::values::*;
use std::{cmp::Ordering, ops::Deref};

#[derive(Clone, Default)]
struct FrozenList {
    content: Vec<FrozenValue>,
}

#[derive(Clone, Default)]
pub struct List {
    content: Vec<Value>,
}

impl<T: Into<Value>> From<Vec<T>> for List {
    fn from(a: Vec<T>) -> List {
        List {
            content: a.into_iter().map(Into::into).collect(),
        }
    }
}

impl<T: Into<Value>> From<Vec<T>> for Value {
    fn from(a: Vec<T>) -> Value {
        Value::new_mutable(List::from(a))
    }
}

impl From<Vec<FrozenValue>> for FrozenValue {
    fn from(a: Vec<FrozenValue>) -> FrozenValue {
        FrozenValue::make_immutable(FrozenList { content: a })
    }
}

impl From<List> for Value {
    fn from(a: List) -> Value {
        Value::make_mutable(a)
    }
}

impl From<FrozenList> for Value {
    fn from(a: FrozenList) -> Value {
        FrozenValue::make_immutable(a).into()
    }
}

#[derive(Clone, Default)]
struct ListGen<T : ValueLike> {
    content: Vec<T>,
}



impl ListGen<FrozenValue> {

}


pub trait ListBase {
    type Item: ValueLike;

    fn content(&self) -> &Vec<Self::Item>;

    fn content_mut(&mut self) -> &mut Vec<Value>;
}

pub trait ListLike {
    fn len(&self) -> usize;
    fn iter<'a>(&'a self) -> Box<dyn Iterator<Item = Value> + 'a>;
}

impl ListLike for FrozenList {
    fn len(&self) -> usize {
        self.content().len()
    }
    fn iter<'a>(&'a self) -> Box<dyn Iterator<Item = Value> + 'a> {
        Box::new(self.content().iter().map(|e| Value::from_frozen(e.clone())))
    }
}

impl ListLike for List {
    fn len(&self) -> usize {
        unimplemented!()
    }
    fn iter<'a>(&'a self) -> Box<dyn Iterator<Item = Value> + 'a> {
        Box::new(self.content().iter().cloned())
    }
}

pub trait ValueAsList {
    fn as_list(&self) -> Option<VRef<dyn ListLike>>;
}

pub trait ValueAsListMut {
    fn as_list_mut(&self) -> Result<Option<VRefMut<List>>, ValueError>;
}

impl ValueAsListMut for Value {
    fn as_list_mut(&self) -> Result<Option<VRefMut<List>>, ValueError> {
        self.downcast_mut::<List>()
    }
}

impl<T: ValueLike> ValueAsList for T {
    fn as_list(&self) -> Option<VRef<dyn ListLike>> {
        self.downcast_ref::<FrozenList>()
            .map(|o| VRef::map(o, |e| e as &dyn ListLike))
            .or_else(|| {
                self.downcast_ref::<List>()
                    .map(|o| VRef::map(o, |e| e as &dyn ListLike))
            })
    }
}

impl List {
    pub fn new() -> Value {
        Value::new_mutable(List {
            content: Vec::new(),
        })
    }

    pub fn push(&mut self, value: Value) -> Result<(), ValueError> {
        let value = value.clone_for_container(self)?;
        self.content.push(value);
        Ok(())
    }

    pub fn extend(&mut self, other: Value) -> Result<(), ValueError> {
        let other: Vec<Value> = other
            .iter()?
            .iter()
            .map(|v| v.clone_for_container(self))
            .collect::<Result<_, _>>()?;
        self.content.extend(other);
        Ok(())
    }

    pub fn clear(&mut self) {
        self.content.clear();
    }

    pub fn insert(&mut self, index: usize, value: Value) -> Result<(), ValueError> {
        let value = value.clone_for_container(self)?;
        self.content.insert(index, value);
        Ok(())
    }

    pub fn pop(&mut self, index: i64) -> Result<Value, ValueError> {
        if index < 0 || index >= self.content.len() as i64 {
            return Err(ValueError::IndexOutOfBound(index));
        }
        Ok(self.content.remove(index as usize))
    }

    pub fn remove(&mut self, needle: Value) -> Result<(), ValueError> {
        let position = match self.content.iter().position(|v| v == &needle) {
            Some(position) => position,
            None => {
                return Err(RuntimeError {
                    code: LIST_REMOVE_ELEMENT_NOT_FOUND_ERROR_CODE,
                    message: format!("Element '{}' not found in '{}'", needle, self.to_str_slow()),
                    label: "not found".to_owned(),
                }
                .into());
            }
        };
        self.content.remove(position);
        Ok(())
    }

    pub fn remove_at(&mut self, index: usize) -> Value {
        self.content.remove(index)
    }
}

impl CloneForCell for List {
    fn clone_for_cell(&self) -> Self {
        let vals: Vec<_> = self.content.iter().map(|e| e.shared()).collect();
        Self { content: vals }
    }
}


impl ListBase for List {
    type Item = Value;
    fn content(&self) -> &Vec<Self::Item> {
        &self.content
    }
    fn content_mut(&mut self) -> &mut Vec<Value> {
        &mut self.content
    }
}

impl MutableValue for List {
    fn freeze(&self) -> Result<FrozenValue, ValueError> {
        let mut frozen = Vec::new();
        for v in self.content() {
            frozen.push(v.freeze()?)
        }
        Ok(FrozenValue::from(frozen))
    }
}

impl ImmutableValue for FrozenList {}

impl ListBase for FrozenList {
    type Item = FrozenValue;
    fn content(&self) -> &Vec<Self::Item> {
        &self.content
    }

    fn content_mut(&mut self) -> &mut Vec<Value> {
        panic!()
    }
}

impl<T: ListBase + TypedValueMulti<Outer=dyn ListLike> + 'static> TypedValue for T {
    fn naturally_mutable(&self) -> bool {
        true
    }

    /// Returns a string representation for the list
    ///
    /// # Examples:
    /// ```
    /// # use starlark::values::*;
    /// # use starlark::values::list::List;
    /// assert_eq!("[1, 2, 3]", Value::from(vec![1, 2, 3]).to_str());
    /// assert_eq!("[1, [2, 3]]",
    ///            Value::from(vec![Value::from(1), Value::from(vec![2, 3])]).to_str());
    /// assert_eq!("[1]", Value::from(vec![1]).to_str());
    /// assert_eq!("[]", Value::from(Vec::<i64>::new()).to_str());
    /// ```
    fn collect_repr(&self, s: &mut String) {
        s.push('[');
        let mut first = true;
        for v in self.content() {
            if first {
                first = false;
            } else {
                s.push_str(", ");
            }
            v.collect_repr(s);
        }
        s.push(']');
    }

    fn to_json(&self) -> String {
        format!(
            "[{}]",
            self.content().iter().map(|e| e.to_json()).enumerate().fold(
                "".to_string(),
                |accum, s| if s.0 == 0 {
                    accum + &s.1
                } else {
                    accum + ", " + &s.1
                },
            )
        )
    }

    fn get_type(&self) -> &'static str {
        "list"
    }
    fn to_bool(&self) -> bool {
        !self.content().is_empty()
    }

    fn equals(&self, other: &Value) -> Result<bool, ValueError> {
        let other = other.as_list();
        match other {
            None => {
                return Err(unsupported!(self, "==", Some(other)));
            }
            Some(ref other) => {
                if self.content().len() != other.len() {
                    return Ok(false);
                }
                let mut left_iter = self.content().iter();
                let mut right_iter = other.iter();
                loop {
                    match (left_iter.next(), right_iter.next()) {
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
            }
        }
    }

    fn compare(&self, other: &Value) -> Result<Ordering, ValueError> {
        if let Some(other) = other.as_list() {
            let mut iter1 = self.content().iter();
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
        Ok(self.content()[i].clone_value())
    }

    fn length(&self) -> Result<i64, ValueError> {
        Ok(self.content().len() as i64)
    }

    fn is_in(&self, other: &Value) -> Result<bool, ValueError> {
        for x in self.content().iter() {
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
        let vec = tuple::slice_vector(start, stop, stride, self.content().iter());

        Ok(Value::new_mutable(List::from(vec)))
    }

    fn iter(&self) -> Result<&dyn TypedIterable, ValueError> {
        Ok(self)
    }

    /// Concatenate `other` to the current value.
    ///
    /// `other` has to be a list.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use starlark::values::*;
    /// # use starlark::values::list::List;
    /// # assert!(
    /// // [1, 2, 3] + [2, 3] == [1, 2, 3, 2, 3]
    /// Value::from(vec![1,2,3]).add(Value::from(vec![2,3])).unwrap()
    ///     == Value::from(vec![1, 2, 3, 2, 3])
    /// # );
    /// ```
    fn add(&self, other: &Value) -> Result<Value, ValueError> {
        if let Some(other) = other.as_list() {
            let mut result = List {
                content: Vec::new(),
            };
            for x in self.content() {
                result.content.push(x.clone_value());
            }
            for x in other.iter() {
                result.content.push(x.clone());
            }
            Ok(Value::from(result))
        } else {
            Err(unsupported!(self, "+", Some(other)))
        }
    }

    fn add_assign(&mut self, other: &Value) -> Result<(), ValueError> {
        if let Some(other) = other.as_list() {
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
    /// # use starlark::values::list::List;
    /// # assert!(
    /// // [1, 2, 3] * 3 == [1, 2, 3, 1, 2, 3, 1, 2, 3]
    /// Value::from(vec![1,2,3]).mul(Value::from(3)).unwrap()
    ///              == Value::from(vec![1, 2, 3, 1, 2, 3, 1, 2, 3])
    /// # );
    /// ```
    fn mul(&self, other: Value) -> ValueResult {
        match other.downcast_ref::<i64>() {
            Some(l) => {
                let mut result = List {
                    content: Vec::new(),
                };
                for _i in 0..*l {
                    result
                        .content
                        .extend(self.content().iter().map(ValueLike::clone_value));
                }
                Ok(Value::new_mutable(result))
            }
            None => Err(ValueError::IncorrectParameterType),
        }
    }

    /// Set the value at `index` to `new_value`
    ///
    /// # Example
    /// ```
    /// # use starlark::values::*;
    /// # use starlark::values::list::List;
    /// let mut v = Value::from(vec![1, 2, 3]);
    /// v.set_at(Value::from(1), Value::from(1)).unwrap();
    /// v.set_at(Value::from(2), Value::from(vec![2, 3])).unwrap();
    /// assert_eq!(&v.to_repr(), "[1, 1, [2, 3]]");
    /// ```
    fn set_at(&mut self, index: Value, new_value: Value) -> Result<(), ValueError> {
        let i = index.convert_index(self.length()?)? as usize;
        self.content_mut()[i] = new_value.clone_for_container(self)?;
        Ok(())
    }

    fn as_dyn_any(&self) -> &dyn Any {
        self
    }
}

impl<T: ListBase + 'static> TypedIterable for T {
    fn to_iter<'a>(&'a self) -> Box<dyn Iterator<Item = Value> + 'a> {
        Box::new(self.content().iter().map(ValueLike::clone_value))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_to_str() {
        assert_eq!("[1, 2, 3]", Value::from(vec![1, 2, 3]).to_str());
        assert_eq!(
            "[1, [2, 3]]",
            Value::from(vec![Value::from(1), Value::from(vec![2, 3])]).to_str()
        );
        assert_eq!("[1]", Value::from(vec![1]).to_str());
        assert_eq!("[]", Value::from(Vec::<i64>::new()).to_str());
    }

    #[test]
    fn test_mutate_list() {
        let mut v = Value::from(vec![1, 2, 3]);
        v.set_at(Value::from(1), Value::from(1)).unwrap();
        v.set_at(Value::from(2), Value::from(vec![2, 3])).unwrap();
        assert_eq!(&v.to_repr(), "[1, 1, [2, 3]]");
    }

    #[test]
    fn test_arithmetic_on_list() {
        // [1, 2, 3] + [2, 3] == [1, 2, 3, 2, 3]
        assert_eq!(
            Value::from(vec![1, 2, 3])
                .add(Value::from(vec![2, 3]))
                .unwrap(),
            Value::from(vec![1, 2, 3, 2, 3])
        );
        // [1, 2, 3] * 3 == [1, 2, 3, 1, 2, 3, 1, 2, 3]
        assert_eq!(
            Value::from(vec![1, 2, 3]).mul(Value::from(3)).unwrap(),
            Value::from(vec![1, 2, 3, 1, 2, 3, 1, 2, 3])
        );
    }

    #[test]
    fn test_value_alias() {
        let v1 = Value::from(vec![1, 2, 3]);
        let mut v2 = v1.clone();
        v2.set_at(Value::from(2), Value::from(4)).unwrap();
        assert_eq!(v2.to_str(), "[1, 2, 4]");
        assert_eq!(v1.to_str(), "[1, 2, 4]");
    }

    #[test]
    fn test_is_descendant() {
        let v1 = Value::from(vec![1, 2, 3]);
        let v2 = Value::from(vec![Value::new(1), Value::new(2), v1.clone()]);
        let v3 = Value::from(vec![Value::new(1), Value::new(2), v2.clone()]);
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
