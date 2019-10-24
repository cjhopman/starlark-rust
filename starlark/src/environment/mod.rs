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
    /// Return the name of this module
    fn name(&self) -> String;

    /// Get the value of the variable `name`
    fn get(&self, name: &str) -> Result<Value, EnvironmentError>;

    /// Return the parent environment (or `None` if there is no parent).
    fn get_parent(&self) -> Option<&FrozenEnvironment>;

    fn find_module(&self, name: &str) -> Option<&FrozenEnvironment>;

    fn get_modules(&self) -> &HashMap<String, FrozenEnvironment>;
    // fn get_type_values(&self) -> &Arc<TypeValues>;
}

#[derive(Clone, Debug)]
pub struct FrozenEnvironment {
    env: Arc<EnvironmentContent<FrozenValue>>,
    modules: HashMap<String, FrozenEnvironment>,
    global: TypeValues,
}

trait Ensure : Send + Sync {}

impl Ensure for FrozenEnvironment {}

impl FrozenEnvironment {
    /// Create a new child environment for this environment
    pub fn child(&self, name: &str) -> LocalEnvironment {
        LocalEnvironment::new_child(name, self.clone())
    }
}

impl Environment for FrozenEnvironment {
    /// Return the name of this module
    fn name(&self) -> String {
        self.env.name.clone()
    }

    fn get_modules(&self) -> &HashMap<String, FrozenEnvironment> {
        &self.modules
    }

    /// Get the value of the variable `name`
    fn get(&self, name: &str) -> Result<Value, EnvironmentError> {
        self.env.get(name).map(|e| e.into())
    }

    fn find_module(&self, name: &str) -> Option<&FrozenEnvironment> {
        self.modules.get(name)
    }

    /// Return the parent environment (or `None` if there is no parent).
    fn get_parent(&self) -> Option<&FrozenEnvironment> {
        self.env.get_parent()
    }
}

#[derive(Debug)]
pub struct LocalEnvironment {
    env: EnvironmentContent<LocalValue>,
    modules: HashMap<String, FrozenEnvironment>,
    global: TypeValues,
}

#[derive(Clone, Debug)]
pub struct GlobalEnvironment {
    env: FrozenEnvironment,
    type_objs: TypeValues,
}

pub struct GlobalEnvironmentBuilder {
    env: EnvironmentContent<Value>,
    type_objs: HashMap<String, HashMap<String, FrozenValue>>,
}

impl GlobalEnvironment {
    pub fn for_each_var<F: FnMut(&String, &Value)>(&self, mut func: F) {
        self.env.env.for_each_var(func);
    }

    pub fn get_type_values(&self) -> TypeValues {
        self.type_objs.clone()
    }
    /// Get a type value if it exists (e.g. list.index).
    pub fn get_type_value(&self, obj_type: &str, id: &str) -> Option<Value> {
        self.type_objs.get_type_value(obj_type, id)
    }

    pub fn child(&self, name: &str) -> LocalEnvironment {
        self.env.child(name)
    }

    /// List the attribute of a type
    pub fn list_type_value(&self, obj: &Value) -> Vec<String> {
        self.type_objs.list_type_value(obj)
    }
}

impl GlobalEnvironmentBuilder {
    pub fn for_each_var<F: FnMut(&String, &Value)>(&self, mut func: F) {
        self.env.for_each_var(func);
    }

    pub fn new() -> Self {
        Self {
            env: EnvironmentContent::new("global", None),
            type_objs: HashMap::new(),
        }
    }

    pub fn build(mut self) -> GlobalEnvironment {
        let type_objs = TypeValues::new(std::mem::replace(&mut self.type_objs, HashMap::new()));
        GlobalEnvironment {
            env: LocalEnvironment::wrap(
                std::mem::replace(&mut self.env, EnvironmentContent::new("", None)),
                type_objs.clone(),
            )
            .frozen()
            .unwrap(),
            type_objs: type_objs,
        }
    }

    pub fn set(&mut self, name: &str, value: Value) -> Result<(), EnvironmentError> {
        self.env.variables.insert(name.to_string(), value);
        Ok(())
    }

    /// Get the object of type `obj_type`, and create it if none exists
    pub fn add_type_value(&mut self, obj: &str, attr: &str, value: FrozenValue) {
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
}

#[derive(Debug)]
pub struct EnvironmentContent<ValueType> {
    /// A name for this environment, required to be unique.
    name: String,

    /// Super environment that represent a higher scope than the current one
    parent: Option<FrozenEnvironment>,

    /// List of variable bindings
    variables: HashMap<String, ValueType>,
}

impl Environment for LocalEnvironment {
    /// Return the name of this module
    fn name(&self) -> String {
        self.env.name.clone()
    }

    /// Get the value of the variable `name`
    fn get(&self, name: &str) -> Result<Value, EnvironmentError> {
        self.env.get(name).map(|e| e.clone())
    }

    fn find_module(&self, name: &str) -> Option<&FrozenEnvironment> {
        self.modules.get(name)
    }

    fn get_modules(&self) -> &HashMap<String, FrozenEnvironment> {
        &self.modules
    }

    /// Return the parent environment (or `None` if there is no parent).
    fn get_parent(&self) -> Option<&FrozenEnvironment> {
        self.env.get_parent()
    }
}

impl LocalEnvironment {
    pub fn for_each_var<F: FnMut(&String, &Value)>(&self, mut func: F) {
        self.env.for_each_var(func);
    }

    pub fn add_modules(&mut self, modules: &HashMap<String, FrozenEnvironment>) {
        for (k, v) in modules {
            self.modules.insert(k.clone(), v.clone());
        }
    }

    /// Create a new environment
    pub fn new(name: &str, global: TypeValues) -> Self {
        Self {
            env: EnvironmentContent::new(name, None),
            modules: HashMap::new(),
            global,
        }
    }

    pub fn wrap(env: EnvironmentContent<Value>, global: TypeValues) -> Self {
        Self {
            env,
            modules: HashMap::new(),
            global,
        }
    }

    pub fn new_child(name: &str, parent: FrozenEnvironment) -> Self {
        Self {
            env: EnvironmentContent::new(name, Some(parent.clone())),
            modules: HashMap::new(),
            global: parent.global.clone(),
        }
    }

    /// Freeze the environment, all its value will become immutable after that
    pub fn frozen(mut self) -> Result<FrozenEnvironment, ValueError> {
        let mut frozen: HashMap<String, FrozenValue> = HashMap::new();
        for (k, v) in std::mem::replace(&mut self.env.variables, Default::default()) {
            frozen.insert(k, v.freeze()?);
        }        

        Ok(FrozenEnvironment {
            env: Arc::new(EnvironmentContent {
                name: self.env.name,
                parent: self.env.parent.clone(),
                variables: frozen,
            }),
            modules: std::mem::replace(&mut self.modules, HashMap::new()),
            global: self.global.clone(),
        })
    }

    /// Set the value of a variable in that environment.
    pub fn set(&mut self, name: &str, value: Value) -> Result<(), EnvironmentError> {
        self.env.variables.insert(name.to_string(), value);
        Ok(())
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

impl<ValueType> EnvironmentContent<ValueType>
where
    ValueType: Clone,
    Value: From<ValueType>,
{
    fn new(name: &str, parent: Option<FrozenEnvironment>) -> Self {
        Self {
            name: name.to_owned(),
            parent,
            variables: HashMap::new(),
        }
    }

    pub fn for_each_var<F: FnMut(&String, &Value)>(&self, mut func: F) {
        for v in self.vars() {
            let val: Value = v.1.clone().into();
            func(v.0, &val);
        }
        if let Some(p) = self.get_parent() {
            p.env.for_each_var(func);
        }
    }

    pub fn vars(&self) -> impl Iterator<Item = (&String, &ValueType)> {
        self.variables.iter()
    }

    /// Get the value of the variable `name`
    pub fn get(&self, name: &str) -> Result<Value, EnvironmentError> {
        match self.variables.get(name) {
            Some(v) => Ok(v.clone().into()),
            None => match self.parent {
                Some(ref p) => p.get(name),
                None => Err(EnvironmentError::VariableNotFound(name.to_owned())),
            },
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
#[derive(Clone, Debug)]
pub struct TypeValues {
    type_objs: Arc<HashMap<String, HashMap<String, FrozenValue>>>,
}

impl TypeValues {
    /// Wrap environment.
    pub fn new(type_objs: HashMap<String, HashMap<String, FrozenValue>>) -> TypeValues {
        TypeValues {
            type_objs: Arc::new(type_objs),
        }
    }

    pub fn get_type_value(&self, obj_type: &str, id: &str) -> Option<Value> {
        self.type_objs
            .get(obj_type)
            .and_then(|d| d.get(id))
            .map(|v| v.clone().into())
    }

    /// List the attribute of a type
    pub fn list_type_value(&self, obj: &Value) -> Vec<String> {
        if let Some(ref d) = self.type_objs.get(obj.get_type()){
            let mut r = Vec::new();
            for k in d.keys() {
                r.push(k.clone());
            }
            r
        } else {
            Vec::new()
        }
    }
}
