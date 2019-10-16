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

//! The enviroment, called "Module" in [this spec](
//! https://github.com/google/skylark/blob/a0e5de7e63b47e716cca7226662a4c95d47bf873/doc/spec.md)
//! is the list of variable in the current scope. It can be frozen, after which all values from
//! this environment become immutable.

use crate::values::error::{RuntimeError, ValueError};
use crate::values::*;
use std::ops::Deref;
use std::sync::Arc;
use std::{collections::HashMap, sync::Weak};

// TODO: move that code in some common error code list?
// CM prefix = Critical Module
const FROZEN_ENV_ERROR_CODE: &str = "CM00";
const NOT_FOUND_ERROR_CODE: &str = "CM01";
const LOCAL_VARIABLE_REFERENCED_BEFORE_ASSIGNMENT: &str = "CM03";
pub(crate) const LOAD_NOT_SUPPORTED_ERROR_CODE: &str = "CM02";
const CANNOT_IMPORT_ERROR_CODE: &str = "CE02";

#[derive(Debug)]
#[doc(hidden)]
pub enum EnvironmentError {
    /// Raised when trying to change a variable on a frozen environment.
    TryingToMutateFrozenEnvironment,
    /// Variables was no found.
    VariableNotFound(String),
    LocalVariableReferencedBeforeAssignment(String),
    /// Cannot import private symbol, i.e. underscore prefixed
    CannotImportPrivateSymbol(String),
}

impl Into<RuntimeError> for EnvironmentError {
    fn into(self) -> RuntimeError {
        RuntimeError {
            code: match self {
                EnvironmentError::TryingToMutateFrozenEnvironment => FROZEN_ENV_ERROR_CODE,
                EnvironmentError::VariableNotFound(..) => NOT_FOUND_ERROR_CODE,
                EnvironmentError::CannotImportPrivateSymbol(..) => CANNOT_IMPORT_ERROR_CODE,
                EnvironmentError::LocalVariableReferencedBeforeAssignment(..) => {
                    LOCAL_VARIABLE_REFERENCED_BEFORE_ASSIGNMENT
                }
            },
            label: match self {
                EnvironmentError::TryingToMutateFrozenEnvironment => {
                    "This value belong to a frozen environment".to_owned()
                }
                EnvironmentError::VariableNotFound(..) => "Variable was not found".to_owned(),
                EnvironmentError::LocalVariableReferencedBeforeAssignment(..) => {
                    "Local variable referenced before assignment".to_owned()
                }
                EnvironmentError::CannotImportPrivateSymbol(ref s) => {
                    format!("Symbol '{}' is private", s)
                }
            },
            message: match self {
                EnvironmentError::TryingToMutateFrozenEnvironment => {
                    "Cannot mutate a frozen environment".to_owned()
                }
                EnvironmentError::VariableNotFound(s) => format!("Variable '{}' not found", s),
                EnvironmentError::LocalVariableReferencedBeforeAssignment(ref s) => {
                    format!("Local variable '{}' referenced before assignment", s)
                }
                EnvironmentError::CannotImportPrivateSymbol(s) => {
                    format!("Cannot import private symbol '{}'", s)
                }
            },
        }
    }
}

impl From<EnvironmentError> for ValueError {
    fn from(e: EnvironmentError) -> Self {
        ValueError::Runtime(e.into())
    }
}

pub trait Environment {
    fn env(&self) -> &EnvironmentContent;

    /// Get a type value if it exists (e.g. list.index).
    fn get_type_value(&self, obj_type: &str, id: &str) -> Option<Value> {
        self.env().get_type_value(obj_type, id)
    }

    /// List the attribute of a type
    fn list_type_value(&self, obj: &Value) -> Vec<String> {
        self.env().list_type_value(obj)
    }

    /// Return the name of this module
    fn name(&self) -> String {
        self.env().name_.clone()
    }

    /// Get the value of the variable `name`
    fn get(&self, name: &str) -> Result<Value, EnvironmentError> {
        self.env().get(name)
    }

    /// Return the parent environment (or `None` if there is no parent).
    fn get_parent(&self) -> Option<&FrozenEnvironment> {
        self.env().get_parent()
    }
}

#[derive(Clone, Debug)]
pub struct FrozenEnvironment {
    env: Arc<EnvironmentContent>,
}

pub struct WeakFrozenEnvironment {
    ptr: Weak<EnvironmentContent>,
}

impl WeakFrozenEnvironment {
    pub fn upgrade(&self) -> FrozenEnvironment {
        FrozenEnvironment {
            env: self.ptr.upgrade().unwrap(),
        }
    }
}

impl FrozenEnvironment {
    /// Create a new child environment for this environment
    pub fn child(&self, name: &str) -> LocalEnvironment {
        LocalEnvironment::new_child(name, self.clone())
    }

    pub fn downgrade(&self) -> WeakFrozenEnvironment {
        WeakFrozenEnvironment {
            ptr: Arc::downgrade(&self.env),
        }
    }
}

impl Environment for FrozenEnvironment {
    fn env(&self) -> &EnvironmentContent {
        &*self.env
    }
}

#[derive(Debug)]
pub struct LocalEnvironment {
    env: EnvironmentContent,
}

#[derive(Debug)]
pub struct EnvironmentContent {
    /// A name for this environment, used mainly for debugging.
    name_: String,
    /// Whether the environment is frozen or not.
    frozen: bool,
    /// Super environment that represent a higher scope than the current one
    parent: Option<FrozenEnvironment>,
    /// List of variable bindings
    ///
    /// These bindings include methods for native types, e.g. `string.isalnum`.
    variables: HashMap<String, Value>,
    /// List of static values of an object per type
    type_objs: HashMap<String, HashMap<String, Value>>,
}

impl Environment for LocalEnvironment {
    fn env(&self) -> &EnvironmentContent {
        &self.env
    }
}

impl LocalEnvironment {
    /// Create a new environment
    pub fn new(name: &str) -> Self {
        Self {
            env: EnvironmentContent::new(name, None),
        }
    }

    pub fn new_child(name: &str, parent: FrozenEnvironment) -> Self {
        Self {
            env: EnvironmentContent::new(name, Some(parent)),
        }
    }

    /// Get the object of type `obj_type`, and create it if none exists
    /// Get the object of type `obj_type`, and create it if none exists
    pub fn add_type_value(&mut self, obj: &str, attr: &str, value: Value) {
        self.env.add_type_value(obj, attr, value)
    }

    /// Freeze the environment, all its value will become immutable after that
    pub fn frozen(mut self) -> Result<FrozenEnvironment, ValueError> {
        let mut take = EnvironmentContent::new("", None);
        self.env.freeze();
        self.env.bind()?;
        std::mem::swap(&mut self.env, &mut take);
        Ok(FrozenEnvironment {
            env: Arc::new(take),
        })
    }

    /// Set the value of a variable in that environment.
    pub fn set(&mut self, name: &str, value: Value) -> Result<(), EnvironmentError> {
        self.env.set(name, value)
    }

    pub fn import_symbol(
        &mut self,
        env: &dyn Environment,
        symbol: &str,
        new_name: &str,
    ) -> Result<(), EnvironmentError> {
        let first = symbol.chars().next();
        match first {
            Some('_') | None => Err(EnvironmentError::CannotImportPrivateSymbol(
                symbol.to_owned(),
            )),
            _ => self.set(new_name, env.get(symbol)?),
        }
    }
}

impl Binder for EnvironmentContent {
    fn get(&self, name: &str) -> Result<Option<Value>, ValueError> {
        match EnvironmentContent::get(self, name).ok() {
            Some(v) => match v.bind(self)? {
                Some(b) => Ok(Some(b)),
                None => Ok(Some(v)),
            },
            None => {
                // println!("binding {} failed. not found in env {}", name, self.name_);
                Ok(None)
            }
        }
    }
}

impl EnvironmentContent {
    fn new(name: &str, parent: Option<FrozenEnvironment>) -> Self {
        Self {
            name_: name.to_owned(),
            frozen: false,
            parent,
            variables: HashMap::new(),
            type_objs: HashMap::new(),
        }
    }

    /// Freeze the environment, all its value will become immutable after that
    pub fn freeze(&mut self) {
        if self.frozen {
            panic!("already frozen :/")
        }

        self.frozen = true;
        for v in self.variables.values_mut() {
            v.freeze();
        }
    }

    pub fn bind(&mut self) -> Result<(), ValueError> {
        if !self.frozen {
            panic!("not yet frozen");
        }

        let mut changed: HashMap<String, Value> = HashMap::new();
        for (k, v) in &self.variables {
            match v.bind(self)? {
                Some(n) => {
                    changed.insert(k.to_string(), n);
                }
                None => {}
            }
        }
        self.variables.extend(changed);

        Ok(())
    }

    pub fn for_each_var<F: FnMut(&String, &Value)>(&self, mut func: F) {
        for v in self.vars() {
            func(v.0, v.1);
        }
        if let Some(p) = self.get_parent() {
            p.env().for_each_var(func);
        }
    }

    /// Set the value of a variable in that environment.
    pub fn set(&mut self, name: &str, value: Value) -> Result<(), EnvironmentError> {
        if self.frozen {
            Err(EnvironmentError::TryingToMutateFrozenEnvironment)
        } else {
            self.variables.insert(name.to_string(), value);
            Ok(())
        }
    }

    pub fn vars(&self) -> impl Iterator<Item = (&String, &Value)> {
        self.variables.iter()
    }

    /// Get the value of the variable `name`
    pub fn get(&self, name: &str) -> Result<Value, EnvironmentError> {
        match self.variables.get(name) {
            Some(v) => Ok(v.clone()),
            None => match self.parent {
                Some(ref p) => p.env().get(name),
                None => Err(EnvironmentError::VariableNotFound(name.to_owned())),
            },
        }
    }

    /// Get the object of type `obj_type`, and create it if none exists
    pub fn add_type_value(&mut self, obj: &str, attr: &str, value: Value) {
        if let Some(ref mut v) = self.type_objs.get_mut(obj) {
            v.insert(attr.to_owned(), value);
            // Do not use a else case for the borrow checker to realize that type_objs is no
            // longer borrowed when inserting.
            return;
        }
        let mut dict = HashMap::new();
        dict.insert(attr.to_owned(), value);
        self.type_objs.insert(obj.to_owned(), dict);
    }

    /// Get a type value if it exists (e.g. list.index).
    fn get_type_value(&self, obj_type: &str, id: &str) -> Option<Value> {
        match self.type_objs.get(obj_type) {
            Some(ref d) => match d.get(id) {
                Some(v) => Some(v.clone()),
                None => match self.parent {
                    Some(ref p) => p.env().get_type_value(obj_type, id),
                    None => None,
                },
            },
            None => match self.parent {
                Some(ref p) => p.env().get_type_value(obj_type, id),
                None => None,
            },
        }
    }

    /// List the attribute of a type
    pub fn list_type_value(&self, obj: &Value) -> Vec<String> {
        if let Some(ref d) = self.type_objs.get(obj.get_type()) {
            let mut r = Vec::new();
            for k in d.keys() {
                r.push(k.clone());
            }
            r
        } else if let Some(ref p) = self.parent {
            p.env().list_type_value(obj)
        } else {
            Vec::new()
        }
    }

    /// Return the parent environment (or `None` if there is no parent).
    pub fn get_parent(&self) -> Option<&FrozenEnvironment> {
        self.parent.as_ref()
    }
}

/// Environment passed to `call` calls.
///
/// Function implementations are only allowed to access
/// type values from "type values" from the caller context,
/// so this struct is passed instead of full `Environment`.
#[derive(Clone)]
pub struct TypeValues {
    env: FrozenEnvironment,
}

impl TypeValues {
    /// Wrap environment.
    pub fn new(env: FrozenEnvironment) -> TypeValues {
        TypeValues { env }
    }

    /// Return the underlying `Environment` name.
    pub fn name(&self) -> String {
        self.env.name()
    }

    /// Get a type value if it exists (e.g. list.index).
    pub fn get_type_value(&self, obj_type: &str, id: &str) -> Option<Value> {
        self.env.get_type_value(obj_type, id)
    }

    /// List the attribute of a type
    pub fn list_type_value(&self, obj: &Value) -> Vec<String> {
        self.env.list_type_value(obj)
    }
}
