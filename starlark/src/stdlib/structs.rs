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

//! Implementation of `struct` function.

use crate::environment::ModuleRegistry;
use crate::small_map::SmallMap;
use crate::values::error::ValueError;
use crate::values::*;
use std::collections::hash_map::DefaultHasher;
use std::{any::Any, hash::Hasher, rc::Rc};

/// `struct()` implementation.

impl StarlarkStruct {
    pub fn new(fields: SmallMap<String, Value>) -> Self {
        Self { fields }
    }
}

impl Default for StarlarkStruct {
    fn default() -> Self {
        Self::new(SmallMap::new())
    }
}

impl From<StarlarkStruct> for Value {
    fn from(s: StarlarkStruct) -> Value {
        Value::make_mutable(s)
    }
}

#[derive(Clone, Default)]
pub struct StarlarkStructGen<T: ValueLike> {
    pub fields: SmallMap<String, T>,
}

pub type StarlarkStruct = StarlarkStructGen<Value>;
pub type FrozenStarlarkStruct = StarlarkStructGen<FrozenValue>;

pub trait StarlarkStructLike: TypedValue {
    fn len(&self) -> usize;
    fn get_field(&self, name: &str) -> Option<Value>;
}

impl ModuleRegistry for StarlarkStruct {
    fn set(
        &mut self,
        name: &str,
        value: Value,
    ) -> Result<(), crate::environment::EnvironmentError> {
        self.fields.insert(name.to_owned(), value);
        Ok(())
    }

    fn add_type_value(&mut self, _obj: &str, _attr: &str, _value: FrozenValue) {
        unimplemented!("Cannot register type values on a struct.")
    }
}

pub trait StarlarkStructMut {
    fn fields_mut(&mut self) -> &mut SmallMap<String, Value>;
}

impl StarlarkStructMut for StarlarkStruct {
    fn fields_mut(&mut self) -> &mut SmallMap<String, Value> {
        &mut self.fields
    }
}

impl StarlarkStructMut for FrozenStarlarkStruct {
    fn fields_mut(&mut self) -> &mut SmallMap<String, Value> {
        panic!()
    }
}

impl<T: ValueLike + 'static> StarlarkStructLike for StarlarkStructGen<T>
where
    StarlarkStructGen<T>: StarlarkStructMut,
{
    fn len(&self) -> usize {
        self.fields.len()
    }
    fn get_field(&self, name: &str) -> Option<Value> {
        self.fields.get(name).map(|e| e.clone_value())
    }
}

impl MutableValue for StarlarkStruct {
    fn freeze(&self) -> Result<FrozenValue, ValueError> {
        let mut frozen = SmallMap::new();

        for (k, v) in &self.fields {
            frozen.insert(k.to_string(), v.freeze()?);
        }

        // TODO
        Ok(FrozenValue::make_immutable(FrozenStarlarkStruct {
            fields: frozen,
        }))
        /*
        return Ok(FrozenValue::new(StarlarkStruct {
            bound: true,
            fields: frozen,
        }));
        */
    }
    fn as_dyn_any_mut(&mut self) -> &mut dyn Any {
        self
    }
}

impl ImmutableValue for FrozenStarlarkStruct {
    fn as_owned_value(&self) -> Box<dyn MutableValue> {
        let mut items = SmallMap::with_capacity(self.fields.len());
        for (k, v) in &self.fields {
            items.insert(k.to_string(), v.shared());
        }
        Box::new(StarlarkStruct { fields: items })
    }
}

pub trait ValueAsStarlarkStruct {
    fn as_struct(&self) -> Option<VRef<dyn StarlarkStructLike>>;
}

pub trait ValueAsStarlarkStructMut {
    fn as_struct_mut(&mut self) -> Result<Option<VRefMut<StarlarkStruct>>, ValueError>;
}

impl ValueAsStarlarkStructMut for Value {
    fn as_struct_mut(&mut self) -> Result<Option<VRefMut<StarlarkStruct>>, ValueError> {
        self.downcast_mut::<StarlarkStruct>()
    }
}

impl<T: ValueLike> ValueAsStarlarkStruct for T {
    fn as_struct(&self) -> Option<VRef<dyn StarlarkStructLike>> {
        self.downcast_ref::<FrozenStarlarkStruct>()
            .map(|o| VRef::map(o, |e| e as &dyn StarlarkStructLike))
            .or_else(|| {
                self.downcast_ref::<StarlarkStruct>()
                    .map(|o| VRef::map(o, |e| e as &dyn StarlarkStructLike))
            })
    }
}

impl<T: ValueLike + 'static> TypedValue for StarlarkStructGen<T>
where
    StarlarkStructGen<T>: StarlarkStructMut,
{
    fn naturally_mutable(&self) -> bool {
        true
    }

    fn as_dyn_any(&self) -> &dyn Any {
        self
    }

    fn to_json(&self) -> String {
        let mut s = "{".to_string();
        s += &self
            .fields
            .iter()
            .map(|(k, v)| format!("{}: {}", k, v.to_json()))
            .collect::<Vec<String>>()
            .join(", ");
        s += "}";
        s
    }

    fn collect_repr(&self, r: &mut String) {
        r.push_str("struct(");
        for (i, (name, value)) in self.fields.iter().enumerate() {
            if i != 0 {
                r.push_str(", ");
            }
            r.push_str(&name);
            r.push_str("=");
            value.collect_repr(r);
        }
        r.push_str(")");
    }

    fn get_type(&self) -> &'static str {
        "struct"
    }
    fn equals(&self, other: &Value) -> Result<bool, ValueError> {
        if let Some(ref other) = other.as_struct() {
            if self.fields.len() != other.len() {
                return Ok(false);
            }

            for (field, a) in &self.fields {
                match other.get_field(field) {
                    None => return Ok(false),
                    Some(b) => {
                        if !a.equals(&b)? {
                            return Ok(false);
                        }
                    }
                }
            }

            return Ok(true);
        }

        Err(unsupported!(self, "==", Some(other)))
    }

    fn get_attr(&self, attribute: &str) -> Result<Value, ValueError> {
        match self.fields.get(attribute) {
            Some(v) => Ok(v.clone_value()),
            None => Err(ValueError::OperationNotSupported {
                op: attribute.to_owned(),
                left: self.to_repr_slow(),
                right: None,
            }),
        }
    }

    fn get_hash(&self) -> Result<u64, ValueError> {
        let mut s = DefaultHasher::new();
        for (k, v) in self.fields.iter() {
            s.write_u64(k.get_hash()?);
            s.write_u64(v.get_hash()?);
        }
        Ok(s.finish())
    }

    fn has_attr(&self, attribute: &str) -> Result<bool, ValueError> {
        Ok(self.fields.contains_key(attribute))
    }

    fn dir_attr(&self) -> Result<Vec<String>, ValueError> {
        Ok(self.fields.keys().cloned().collect())
    }
}

starlark_module! { global =>
    /// Creates a struct.
    ///
    /// `struct` creates a struct. It accepts keyword arguments, keys become struct field names,
    /// and values become field values.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default("(
    /// struct(host='localhost', port=80).port == 80
    /// # )").unwrap());
    /// # assert!(starlark_default("(
    /// dir(struct(host='localhost', port=80)) == ['host', 'port']
    /// # )").unwrap());
    /// # assert!(starlark_default("(
    /// dir(struct()) == []
    /// # )").unwrap());
    /// ```
    struct_(**kwargs) {
        Ok(Value::new_mutable(StarlarkStruct {
            fields: kwargs
        }))
    }

    struct_.to_json(this) {
        let this = this.as_struct().unwrap();
        Ok(Value::new(this.to_json()))
    }
}
