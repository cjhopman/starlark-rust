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

//! Module define the Starlark type Dictionary
use crate::small_map::SmallMap;
use crate::values::error::ValueError;
use crate::values::hashed_value::HashedValue;
use crate::values::iter::TypedIterable;
use crate::values::none::NoneType;
use crate::values::*;
use std::collections::HashMap;
use std::convert::TryFrom;
use std::hash::Hash;

/// The Dictionary type
#[derive(Default, Clone)]
pub struct Dictionary {
    content: SmallMap<Value, Value>,
}

impl Dictionary {
    pub fn from(map: SmallMap<Value, Value>) -> Dictionary {
        Dictionary { content: map }
    }

    pub fn new_typed() -> Dictionary {
        Dictionary::default()
    }

    pub fn new() -> Value {
        Value::new_mutable(Dictionary::new_typed())
    }

    pub fn get_content(&self) -> &SmallMap<Value, Value> {
        &self.content
    }

    pub fn get(&self, key: &Value) -> Result<Option<&Value>, ValueError> {
        Ok(self.content.get(key))
    }

    pub fn clear(&mut self) {
        self.content.clear();
    }

    pub fn remove(&mut self, key: &Value) -> Result<Option<Value>, ValueError> {
        Ok(self.content.remove(key))
    }

    pub fn items(&self) -> Vec<(Value, Value)> {
        self.content
            .iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect()
    }

    pub fn values(&self) -> Vec<Value> {
        self.content.values().cloned().collect()
    }

    /*
    pub fn get_hashed(&self, key: &HashedValue) -> Option<&Value> {
        self.content.get(key)
    }
    */

    pub fn insert(&mut self, key: Value, value: Value) -> Result<Value, ValueError> {
        let key = key.clone_for_container(self)?;
        let value = value.clone_for_container(self)?;
        self.content.insert(key, value);
        Ok(Value::new(NoneType::None))
    }
}

impl<T1: Into<Value> + Hash + Eq + Clone, T2: Into<Value> + Eq + Clone> TryFrom<HashMap<T1, T2>>
    for Dictionary
{
    type Error = ValueError;

    fn try_from(a: HashMap<T1, T2>) -> Result<Dictionary, ValueError> {
        let mut result = Dictionary {
            content: SmallMap::new(),
        };
        for (k, v) in a.iter() {
            result.content.insert(k.clone().into(), v.clone().into());
        }
        Ok(result)
    }
}

impl<T1: Into<Value> + Hash + Eq + Clone, T2: Into<Value> + Eq + Clone> TryFrom<SmallMap<T1, T2>>
    for Dictionary
{
    type Error = ValueError;

    fn try_from(a: SmallMap<T1, T2>) -> Result<Dictionary, ValueError> {
        let mut result = Dictionary {
            content: SmallMap::new(),
        };
        for (k, v) in a.iter() {
            result.content.insert(k.clone().into(), v.clone().into());
        }
        Ok(result)
    }
}

impl CloneForCell for Dictionary {
    fn clone_for_cell(&self) -> Self {
        let mut items = SmallMap::with_capacity(self.content.len());
        for (k, v) in &self.content {
            items.insert(k.shared(), v.shared());
        }
        Self { content: items }
    }
}

impl From<Dictionary> for Value {
    fn from(d: Dictionary) -> Value {
        Value::make_mutable(d)
    }
}

impl MutableValue for Dictionary {   
    fn freeze(&self) -> Result<FrozenValue, ValueError> { 
        let mut frozen: SmallMap<FrozenValue, FrozenValue> = SmallMap::new();
        for (k, v) in &self.content {
            frozen.insert(k.freeze()?, v.freeze()?);
        }
        panic!()
        // Ok(FrozenValue::make_immutable(Dictionary::from(frozen)))
    }
}

/// Define the Dictionary type
impl TypedValue for Dictionary {
    fn naturally_mutable(&self) -> bool {
        true
    }

    fn as_dyn_any(&self) -> &dyn Any {
        self
    }

    fn collect_repr(&self, r: &mut String) {
        r.push_str("{");
        for (i, (name, value)) in self.content.iter().enumerate() {
            if i != 0 {
                r.push_str(", ");
            }
            name.collect_repr(r);
            r.push_str(": ");
            value.collect_repr(r);
        }
        r.push_str(")");
    }

    fn to_json(&self) -> String {
        format!(
            "{{{}}}",
            self.content
                .iter()
                .map(|(k, v)| format!("{}: {}", k.to_json(), v.to_json()))
                .enumerate()
                .fold("".to_string(), |accum, s| if s.0 == 0 {
                    accum + &s.1
                } else {
                    accum + ", " + &s.1
                })
        )
    }

    fn get_type(&self) -> &'static str {
        "dict"
    }
    fn to_bool(&self) -> bool {
        !self.content.is_empty()
    }

    fn equals(&self, other: &Value) -> Result<bool, ValueError> {
        if let Some(other) = other.downcast_ref::<Self>() {
            if self.content.len() != other.content.len() {
                return Ok(false);
            }

            for (k, v) in &self.content {
                match other.content.get(k) {
                    None => return Ok(false),
                    Some(w) => {
                        if !v.equals(w)? {
                            return Ok(false);
                        }
                    }
                }
            }

            return Ok(true);
        }
        Err(unsupported!(self, "==", Some(other)))
    }

    fn at(&self, index: Value) -> ValueResult {
        match self.content.get(&index) {
            Some(v) => Ok(v.clone()),
            None => Err(ValueError::KeyNotFound(index)),
        }
    }

    fn length(&self) -> Result<i64, ValueError> {
        Ok(self.content.len() as i64)
    }

    fn is_in(&self, other: &Value) -> Result<bool, ValueError> {
        Ok(self.content.contains_key(other))
    }

    fn iter(&self) -> Result<&dyn TypedIterable, ValueError> {
        Ok(self)
    }

    fn set_at(&mut self, index: Value, new_value: Value) -> Result<(), ValueError> {
        let new_value = new_value.clone_for_container(self)?;
        {
            if let Some(x) = self.content.get_mut(&index) {
                *x = new_value;
                return Ok(());
            }
        }
        self.content.insert(index, new_value);
        Ok(())
    }

    fn add(&self, other: &Value) -> Result<Value, ValueError> {
        if let Some(other) = other.downcast_ref::<Self>() {
            let mut result = Dictionary {
                content: SmallMap::new(),
            };
            for (k, v) in &self.content {
                result.content.insert(k.clone(), v.clone());
            }
            for (k, v) in &other.content {
                result.content.insert(k.clone(), v.clone());
            }
            return Ok(Value::from(result));
        }
        Err(unsupported!(self, "+", Some(other)))
    }
}

impl TypedIterable for Dictionary {
    fn to_iter<'a>(&'a self) -> Box<dyn Iterator<Item = Value> + 'a> {
        Box::new(self.content.iter().map(|x| x.0.clone()))
    }
}

impl<T1: Into<Value> + Eq + Hash + Clone, T2: Into<Value> + Eq + Clone> TryFrom<HashMap<T1, T2>>
    for Value
{
    type Error = ValueError;

    fn try_from(a: HashMap<T1, T2>) -> Result<Value, ValueError> {
        Ok(Value::new_mutable(dict::Dictionary::try_from(a)?))
    }
}

impl<T1: Into<Value> + Eq + Hash + Clone, T2: Into<Value> + Eq + Clone> TryFrom<SmallMap<T1, T2>>
    for Value
{
    type Error = ValueError;

    fn try_from(a: SmallMap<T1, T2>) -> Result<Value, ValueError> {
        Ok(Value::new_mutable(dict::Dictionary::try_from(a)?))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mutate_dict() {
        let mut map = SmallMap::<HashedValue, Value>::new();
        map.insert(HashedValue::new(Value::from(1)).unwrap(), Value::from(2));
        map.insert(HashedValue::new(Value::from(2)).unwrap(), Value::from(4));
        let mut d = Value::try_from(map).unwrap();
        assert_eq!("{1: 2, 2: 4}", d.to_str());
        d.set_at(Value::from(2), Value::from(3)).unwrap();
        assert_eq!("{1: 2, 2: 3}", d.to_str());
        d.set_at(Value::from((3, 4)), Value::from(5)).unwrap();
        assert_eq!("{1: 2, 2: 3, (3, 4): 5}", d.to_str());
    }

    #[test]
    fn test_is_descendant() {
        let mut map = SmallMap::<HashedValue, Value>::new();
        map.insert(HashedValue::new(Value::from(1)).unwrap(), Value::from(2));
        map.insert(HashedValue::new(Value::from(2)).unwrap(), Value::from(4));
        let v1 = Value::try_from(map.clone()).unwrap();
        map.insert(HashedValue::new(Value::from(3)).unwrap(), v1.clone());
        let v2 = Value::try_from(map.clone()).unwrap();
        map.insert(HashedValue::new(Value::from(3)).unwrap(), v2.clone());
        let v3 = Value::try_from(map).unwrap();
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
