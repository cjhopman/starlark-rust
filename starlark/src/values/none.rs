// Copyright 2019 The Starlark in Rust Authors
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

//! Define the None type for Starlark.

use crate::values::error::ValueError;
use crate::values::*;
use std::cmp::Ordering;
use std::iter;

/// Define the NoneType type
#[derive(Debug, Clone)]
pub enum NoneType {
    None,
}

impl ImmutableValue for NoneType {}

/// Define the NoneType type
impl TypedValue for NoneType {
    fn as_dyn_any(&self) -> &dyn Any { self }
    fn get_type(&self) -> &'static str {
        "NoneType"
    }

    fn equals(&self, other: &Value) -> Result<bool, ValueError> {
        if let Some(_) = other.downcast_ref::<Self>() {
            Ok(true)
        } else {
            Err(unsupported!(self, "==", Some(other)))
        }
    }

    fn compare(&self, other: &Value) -> Result<Ordering, ValueError> {
        if let Some(_) = other.downcast_ref::<Self>() {
            Ok(Ordering::Equal)
        } else {
            Err(unsupported!(self, "cmp()", Some(other)))
        }
    }

    fn collect_repr(&self, s: &mut String) {
        s.push_str("None");
    }

    fn to_json(&self) -> String {
        "None".to_string()
    }
    fn to_bool(&self) -> bool {
        false
    }
    // just took the result of hash(None) in macos python 2.7.10 interpreter.
    fn get_hash(&self) -> Result<u64, ValueError> {
        Ok(9_223_380_832_852_120_682)
    }
}

impl From<NoneType> for Value {
    fn from(NoneType::None: NoneType) -> Self {
        Value::new(NoneType::None)
    }
}
