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

use crate::small_map::SmallMap;
use crate::values::error::ValueError;
use crate::values::*;

/// `struct()` implementation.
pub struct StarlarkStruct {
    bound: bool,
    pub fields: SmallMap<String, Value>,
}

impl StarlarkStruct {
    pub fn new(fields : SmallMap<String, Value>) -> Self {
        Self {
            bound: false,
            fields
        }
    }
}

impl TypedValue for StarlarkStruct {
    type Holder = ImmutableCell<StarlarkStruct>;

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

    fn values_for_descendant_check_and_freeze<'a>(
        &'a self,
    ) -> Box<dyn Iterator<Item = Value> + 'a> {
        Box::new(self.fields.values().cloned())
    }

    fn bind(&self, vars: &dyn Binder) -> Result<Option<Value>, ValueError> {
        if self.bound {
            return Ok(None);
        }

        // println!("binding struct");

        let mut bound = SmallMap::new();
        let mut changed = false;

        for (k, v) in &self.fields {
            let b = v.bind(vars)?;
            changed |= b.is_some();
            bound.insert(k.to_string(), b);
        }

        if !changed {
            return Ok(None);
        }

        let mut bound_fields = SmallMap::new();
        for (k, v) in &self.fields {
            match bound.remove(k).unwrap() {
                Some(v) => {
                    bound_fields.insert(k.to_string(), v);
                }
                None => {
                    bound_fields.insert(k.to_string(), v.clone());
                }
            }
        }
        return Ok(Some(Value::new(StarlarkStruct {
            bound: true,
            fields: bound_fields,
        })));
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

    const TYPE: &'static str = "struct";

    fn equals(&self, other: &StarlarkStruct) -> Result<bool, ValueError> {
        if self.fields.len() != other.fields.len() {
            return Ok(false);
        }

        for (field, a) in &self.fields {
            match other.fields.get(field) {
                None => return Ok(false),
                Some(b) => {
                    if !a.equals(b)? {
                        return Ok(false);
                    }
                }
            }
        }

        Ok(true)
    }

    fn get_attr(&self, attribute: &str) -> Result<Value, ValueError> {
        match self.fields.get(attribute) {
            Some(v) => Ok(v.clone()),
            None => Err(ValueError::OperationNotSupported {
                op: attribute.to_owned(),
                left: self.to_repr_slow(),
                right: None,
            }),
        }
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
        Ok(Value::new(StarlarkStruct {
            bound: false,
            fields: kwargs
        }))
    }

    struct_.to_json(this) {
        let this = this.downcast_ref::<StarlarkStruct>().unwrap();
        Ok(Value::new(this.to_json()))
    }
}
