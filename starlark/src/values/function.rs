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

//! Function as a TypedValue
use super::*;
use crate::environment::{Environment, EnvironmentError, TypeValues};
use crate::eval::def::DefInvoker;
use crate::eval::EvaluationContext;
use crate::small_map::SmallMap;
use crate::values::error::RuntimeError;
use crate::values::none::NoneType;
use crate::{stdlib::macros::param::TryParamConvertFromValue, values::dict::Dictionary};
use std::convert::TryInto;
use std::iter;
use std::mem;
use std::vec;

#[derive(Debug, Clone)]
#[doc(hidden)]
pub enum FunctionParameter {
    Normal(String),
    Optional(String),
    WithDefaultValue(String, Value),
    ArgsArray(String),
    KWArgsDict(String),
}

impl FunctionParameter {
    pub fn is_normal(&self) -> bool {
        match self {
            FunctionParameter::Normal(..)
            | FunctionParameter::Optional(..)
            | FunctionParameter::WithDefaultValue(..) => true,
            FunctionParameter::ArgsArray(..) | FunctionParameter::KWArgsDict(..) => false,
        }
    }

    pub fn name(&self) -> &str {
        match self {
            FunctionParameter::Normal(name) => name,
            FunctionParameter::Optional(name) => name,
            FunctionParameter::WithDefaultValue(name, _) => name,
            FunctionParameter::ArgsArray(name) => name,
            FunctionParameter::KWArgsDict(name) => name,
        }
    }
}

#[derive(Debug, Clone)]
#[doc(hidden)]
pub enum FunctionType {
    Native(String),
    Def(String, String),
}

#[derive(Debug)]
pub enum FunctionArg {
    Normal(Value),
    Optional(Option<Value>),
    ArgsArray(ArgsArray),
    KWArgsDict(KwargsDict),
}

impl FunctionArg {
    pub fn into_normal<T: TryParamConvertFromValue>(
        self,
        param_name: &'static str,
    ) -> Result<T, ValueError> {
        match self {
            FunctionArg::Normal(v) => {
                T::try_from(v).map_err(|_| ValueError::IncorrectParameterTypeNamed(param_name))
            }
            _ => Err(ValueError::IncorrectParameterType),
        }
    }

    pub fn into_optional<T: TryParamConvertFromValue>(
        self,
        param_name: &'static str,
    ) -> Result<Option<T>, ValueError> {
        match self {
            FunctionArg::Optional(Some(v)) => {
                Ok(Some(T::try_from(v).map_err(|_| {
                    ValueError::IncorrectParameterTypeNamed(param_name)
                })?))
            }
            FunctionArg::Optional(None) => Ok(None),
            _ => Err(ValueError::IncorrectParameterType),
        }
    }

    pub fn into_args_array<T: TryParamConvertFromValue>(
        self,
        param_name: &'static str,
    ) -> Result<Vec<T>, ValueError> {
        match self {
            FunctionArg::ArgsArray(v) => v.into_args_array(),
            _ => Err(ValueError::IncorrectParameterType),
        }
    }

    pub fn into_kw_args_dict<T: TryParamConvertFromValue>(
        self,
        param_name: &'static str,
    ) -> Result<SmallMap<String, T>, ValueError> {
        match self {
            FunctionArg::KWArgsDict(dict) => dict.into_hash_map(),
            _ => Err(ValueError::IncorrectParameterType),
        }
    }
}

impl From<FunctionArg> for Value {
    fn from(a: FunctionArg) -> Value {
        match a {
            FunctionArg::Normal(v) => v,
            FunctionArg::ArgsArray(v) => v.into(),
            FunctionArg::Optional(v) => match v {
                Some(v) => v,
                None => Value::new(NoneType::None),
            },
            FunctionArg::KWArgsDict(v) => {
                // `unwrap` does not panic, because key is a string which hashable
                v.try_into().unwrap()
            }
        }
    }
}

pub type StarlarkFunctionPrototype =
    dyn Fn(&EvaluationContext, Vec<FunctionArg>) -> ValueResult;
// Wrapper for method that have been affected the self object
pub(crate) struct WrappedMethod {
    method: Value,
    self_obj: Value,
}

// TODO: move that code in some common error code list?
// CV prefix = Critical Function call
const NOT_ENOUGH_PARAMS_ERROR_CODE: &str = "CF00";
const WRONG_ARGS_IDENT_ERROR_CODE: &str = "CF01";
const ARGS_NOT_ITERABLE_ERROR_CODE: &str = "CF02";
const KWARGS_NOT_MAPPABLE_ERROR_CODE: &str = "CF03";
// Not an error: const KWARGS_KEY_IDENT_ERROR_CODE: &str = "CF04";
const EXTRA_PARAMETER_ERROR_CODE: &str = "CF05";

#[derive(Debug, Clone)]
pub enum FunctionError {
    NotEnoughParameter {
        missing: String,
        function_type: FunctionType,
        signature: Vec<FunctionParameter>,
    },
    ArgsValueIsNotString,
    ArgsArrayIsNotIterable,
    KWArgsDictIsNotMappable,
    ExtraParameter,
}

impl Into<RuntimeError> for FunctionError {
    fn into(self) -> RuntimeError {
        RuntimeError {
            code: match self {
                FunctionError::NotEnoughParameter { .. } => NOT_ENOUGH_PARAMS_ERROR_CODE,
                FunctionError::ArgsValueIsNotString => WRONG_ARGS_IDENT_ERROR_CODE,
                FunctionError::ArgsArrayIsNotIterable => ARGS_NOT_ITERABLE_ERROR_CODE,
                FunctionError::KWArgsDictIsNotMappable => KWARGS_NOT_MAPPABLE_ERROR_CODE,
                FunctionError::ExtraParameter => EXTRA_PARAMETER_ERROR_CODE,
            },
            label: match self {
                FunctionError::NotEnoughParameter { .. } => {
                    "Not enough parameters in function call".to_owned()
                }
                FunctionError::ArgsValueIsNotString => "not an identifier for *args".to_owned(),
                FunctionError::ArgsArrayIsNotIterable => "*args is not iterable".to_owned(),
                FunctionError::KWArgsDictIsNotMappable => "**kwargs is not mappable".to_owned(),
                FunctionError::ExtraParameter => "Extraneous parameter in function call".to_owned(),
            },
            message: match self {
                FunctionError::NotEnoughParameter {
                    missing,
                    function_type,
                    signature,
                } => format!(
                    "Missing parameter {} for call to {}",
                    missing.trim_start_matches('$'),
                    repr_slow(&function_type, &signature)
                ),
                FunctionError::ArgsValueIsNotString => {
                    "The argument provided for *args is not an identifier".to_owned()
                }
                FunctionError::ArgsArrayIsNotIterable => {
                    "The argument provided for *args is not iterable".to_owned()
                }
                FunctionError::KWArgsDictIsNotMappable => {
                    "The argument provided for **kwargs is not mappable".to_owned()
                }
                FunctionError::ExtraParameter => {
                    "Extraneous parameter passed to function call".to_owned()
                }
            },
        }
    }
}

impl From<FunctionError> for ValueError {
    fn from(e: FunctionError) -> Self {
        ValueError::Runtime(e.into())
    }
}

impl WrappedMethod {
    pub fn new(self_obj: Value, method: Value) -> Value {
        Value::new(WrappedMethod { method, self_obj })
    }
}

impl FunctionType {
    fn to_str(&self) -> String {
        match self {
            FunctionType::Native(ref name) => name.clone(),
            FunctionType::Def(ref name, ..) => name.clone(),
        }
    }

    fn to_repr(&self) -> String {
        match self {
            FunctionType::Native(ref name) => format!("<native function {}>", name),
            FunctionType::Def(ref name, ref module, ..) => {
                format!("<function {} from {}>", name, module)
            }
        }
    }
}

fn repr_slow(function_type: &FunctionType, signature: &[FunctionParameter]) -> String {
    let mut s = String::new();
    collect_repr(function_type, signature, &mut s);
    s
}

pub(crate) fn collect_repr(
    function_type: &FunctionType,
    signature: &[FunctionParameter],
    collector: &mut String,
) {
    let v: Vec<String> = signature
        .iter()
        .map(|x| -> String {
            match x {
                FunctionParameter::Normal(ref name) => name.clone(),
                FunctionParameter::Optional(ref name) => format!("?{}", name),
                FunctionParameter::WithDefaultValue(ref name, ref value) => {
                    format!("{} = {}", name, value.to_repr())
                }
                FunctionParameter::ArgsArray(ref name) => format!("*{}", name),
                FunctionParameter::KWArgsDict(ref name) => format!("**{}", name),
            }
        })
        .collect();
    collector.push_str(&format!("{}({})", function_type.to_repr(), v.join(", ")));
}

pub(crate) fn collect_str(
    function_type: &FunctionType,
    signature: &[FunctionParameter],
    collector: &mut String,
) {
    let v: Vec<String> = signature
        .iter()
        .map(|x| -> String {
            match x {
                FunctionParameter::Normal(ref name) => name.clone(),
                FunctionParameter::Optional(ref name) => name.clone(),
                FunctionParameter::WithDefaultValue(ref name, ref value) => {
                    format!("{} = {}", name, value.to_repr())
                }
                FunctionParameter::ArgsArray(ref name) => format!("*{}", name),
                FunctionParameter::KWArgsDict(ref name) => format!("**{}", name),
            }
        })
        .collect();
    collector.push_str(&format!("{}({})", function_type.to_str(), v.join(", ")));
}

#[derive(Debug)]
pub struct ArgsArray {
    index: usize,
    args_len: i64,
    positional: Vec<Value>,
    args: Option<Value>,
}

impl ArgsArray {
    pub fn new(positional: Vec<Value>, args: Option<Value>) -> Self {
        Self {
            index: 0,
            args_len: args.as_ref().and_then(|e| e.length().ok()).unwrap_or(0),
            positional,
            args,
        }
    }
    pub fn next(&mut self) -> Option<Value> {
        let mut idx = self.index;
        self.index += 1;
        if idx < self.positional.len() {
            return Some(self.positional[idx].clone());
        }

        idx -= self.positional.len();
        if idx < self.args_len as usize {
            if let Some(ref v) = self.args {
                return v.at(Value::new(idx as i64)).ok();
            }
        }
        None
    }

    pub fn into_args_array<T: TryParamConvertFromValue>(mut self) -> Result<Vec<T>, ValueError> {
        let mut res = Vec::with_capacity(self.remaining());
        let mut skip = 0;
        if self.index < self.positional.len() {
            for v in self.positional.into_iter().skip(self.index) {
                res.push(T::try_from(v).map_err(|_| ValueError::IncorrectParameterTypeNamed(""))?);
            }
        } else {
            skip = self.index - self.positional.len();
        }

        if let Some(ref args) = self.args.take() {
            for k in args.iter() {
                for v in k.into_iter().skip(skip) {
                    res.push(
                        T::try_from(v).map_err(|_| ValueError::IncorrectParameterTypeNamed(""))?,
                    );
                }
            }
        }

        Ok(res)
        /*
        Ok(v
                .into_iter()
                .map(T::try_from)
                .collect::<Result<Vec<T>, _>>()
                .map_err()
                */
    }

    pub fn remaining(&self) -> usize {
        self.positional.len() + self.args_len as usize - self.index
    }

    fn make_list(&self) -> Vec<Value> {
        let mut list = Vec::with_capacity(self.remaining());
        if self.index < self.positional.len() {
            for v in self.positional.iter().skip(self.index) {
                list.push(v.clone());
            }
            if let Some(ref args) = self.args {
                let inner = args.iter().unwrap();
                for v in inner.into_iter() {
                    list.push(v);
                }
            }
        } else {
            if let Some(ref args) = self.args {
                let inner = args.iter().unwrap();
                for v in inner.into_iter().skip(self.index - self.positional.len()) {
                    list.push(v);
                }
            }
        }
        list
    }

    fn check_no_more_args(&self) -> Result<(), ValueError> {
        Ok(())
    }
}

impl TypedValue for ArgsArray {
    type Holder = ImmutableCell<Self>;

    /// Return a string describing the type of self, as returned by the type() function.
    const TYPE: &'static str = "argsarray";

    fn values_for_descendant_check_and_freeze<'a>(
        &'a self,
    ) -> Box<dyn Iterator<Item = Value> + 'a> {
        // TODO
        Box::new(iter::empty())
    }

    /// Return a string representation of self, as returned by the repr() function.
    fn collect_repr(&self, s: &mut String) {
        s.push('<');
        s.push_str(Self::TYPE);
        s.push('>');
    }

    fn to_json(&self) -> String {
        panic!("unsupported for type {}", Self::TYPE)
    }

    /// Convert self to a Boolean truth value, as returned by the bool() function.
    fn to_bool(&self) -> bool {
        // TODO
        true
    }

    /// Perform an array or dictionary indirection.
    ///
    /// This returns the result of `a[index]` if `a` is indexable.
    fn at(&self, index: Value) -> ValueResult {
        let index = index.convert_index(self.remaining() as i64)?;
        let mut idx = self.index + (index as usize);
        if idx < self.positional.len() {
            return Ok(self.positional[idx].clone());
        }

        idx -= self.positional.len();
        if let Some(ref a) = self.args {
            return a.at(Value::new(idx as i64));
        }
        unreachable!()
    }

    fn slice(
        &self,
        _start: Option<Value>,
        _stop: Option<Value>,
        _stride: Option<Value>,
    ) -> ValueResult {
        unimplemented!("could be done")
    }

    /// Returns an iterable over the value of this container if this value hold an iterable
    /// container.
    fn iter(&self) -> Result<&dyn TypedIterable, ValueError> {
        Ok(self)
    }

    /// Returns the length of the value, if this value is a sequence.
    fn length(&self) -> Result<i64, ValueError> {
        unimplemented!("length")
    }

    fn is_in(&self, other: &Value) -> Result<bool, ValueError> {
        unimplemented!("?")
    }

    fn add_special(&self, other: Value) -> Result<Value, ValueError> {
        let mut list = self.make_list();
        list.extend(other.iter().unwrap().into_iter());
        Ok(Value::from(list))
    }
}

impl TypedIterable for ArgsArray {
    fn to_iter<'a>(&'a self) -> Box<dyn Iterator<Item = Value> + 'a> {
        if self.index < self.positional.len() {
            let iter = self.positional.iter().skip(self.index).cloned();
            if let Some(ref args) = self.args {
                let inner = args.iter().unwrap();
                let vec: Vec<_> = inner.into_iter().collect();
                return Box::new(iter.chain(vec.into_iter()));
            }
            return Box::new(iter);
        } else {
            if let Some(ref args) = self.args {
                let inner = args.iter().unwrap();
                let vec: Vec<_> = inner
                    .into_iter()
                    .skip(self.index - self.positional.len())
                    .collect();
                return Box::new(vec.into_iter());
            }
        }
        Box::new(std::iter::empty())
    }
}

impl CloneForCell for ArgsArray {
    fn clone_for_cell(&self) -> Self {
        let list = self.make_list();
        ArgsArray::new(Vec::new(), Some(Value::from(list)))
    }
}

impl From<ArgsArray> for Value {
    fn from(a: ArgsArray) -> Value {
        let mut v = Value::new(a);
        v.freeze();
        v.shared()
    }
}

#[derive(Debug)]
pub struct KwargsData {}

pub struct KwargsIter {
    data: Rc<KwargsData>,
    pos: usize,
}

/*
impl Iterator<Item=Value> for KwargsIter {

}
*/

#[derive(Debug)]
pub struct KwargsDict {
    index: usize,
    // TODO: mark taken?
    named: SmallMap<String, Value>,
    kwargs_arg: Option<Value>,
}

impl TypedIterable for KwargsDict {
    fn to_iter<'a>(&'a self) -> Box<dyn Iterator<Item = Value> + 'a> {
        if self.index < self.named.len() {
            let iter = self
                .named
                .keys()
                .skip(self.index)
                .map(|e| Value::new(e.clone()));
            if let Some(ref args) = self.kwargs_arg {
                let inner = args.iter().unwrap();
                let vec: Vec<_> = inner.into_iter().collect();
                return Box::new(iter.chain(vec.into_iter()));
            }
            return Box::new(iter);
        } else {
            if let Some(ref args) = self.kwargs_arg {
                let inner = args.iter().unwrap();
                let vec: Vec<_> = inner.into_iter().collect();
                return Box::new(vec.into_iter());
            }
        }
        Box::new(std::iter::empty())
    }
}

impl CloneForCell for KwargsDict {
    fn clone_for_cell(&self) -> Self {
        let kwargs_arg = self.kwargs_arg.as_ref().map(|v| {
            Self::map_kwargs_arg(
                &v,
                |dict| Value::new(dict.clone_for_cell()),
                |kwargsdict| Value::new(kwargsdict.clone_for_cell()),
            )
        });

        let mut named = SmallMap::with_capacity(self.named.len());
        for (k, v) in &self.named {
            named.insert(k.clone(), v.shared());
        }

        Self::new(named, kwargs_arg)
    }
}

/*
impl std::ops::Deref for KwargsDict {
    type Target = KwargsData;

    fn deref(&self) -> &Self::Target {
        &self.data
    }
}
*/

impl KwargsDict {
    fn map_kwargs_arg<T, FL: FnOnce(&Dictionary) -> T, FR: FnOnce(&KwargsDict) -> T>(
        kwargs: &Value,
        left: FL,
        right: FR,
    ) -> T {
        if let Some(dict) = kwargs.downcast_ref::<Dictionary>() {
            return left(&*dict);
        }

        if let Some(dict) = kwargs.downcast_ref::<KwargsDict>() {
            return right(&*dict);
        }

        unreachable!()
    }

    fn map_kwargs_arg_mut<T, FL: FnOnce(&mut Dictionary) -> T, FR: FnOnce(&mut KwargsDict) -> T>(
        kwargs: &mut Value,
        left: FL,
        right: FR,
    ) -> T {
        if let Some(mut dict) = kwargs.downcast_mut::<Dictionary>().unwrap() {
            return left(&mut *dict);
        }

        if let Some(mut dict) = kwargs.downcast_mut::<KwargsDict>().unwrap() {
            return right(&mut *dict);
        }

        unreachable!()
    }

    fn new(named: SmallMap<String, Value>, kwargs_arg: Option<Value>) -> Self {
        Self {
            index: 0,
            named,
            kwargs_arg: kwargs_arg.map(|a| a.shared()),
        }
    }
    fn next(&mut self, name: &str) -> Option<Value> {
        if let Some(v) = self.named.remove(name) {
            return Some(v);
        }
        if let Some(ref mut kwargs) = self.kwargs_arg {
            return Self::map_kwargs_arg_mut(
                kwargs,
                |dict| {
                    dict.remove(&Value::new(name.to_string()))
                        .ok()
                        .and_then(|e| e)
                },
                |kwargsdict| {
                    kwargsdict
                        .remove(&Value::new(name.to_string()))
                        .ok()
                        .and_then(|e| e)
                },
            );
        }
        None
    }
    pub fn insert(&mut self, key: Value, value: Value) -> Result<Value, ValueError> {
        if let Some(ref mut kwargs) = self.kwargs_arg {
            self.named.remove(&key.to_string());
            let key1 = &key;
            let key2 = &key;
            let val1 = &value;
            let val2 = &value;
            return Self::map_kwargs_arg_mut(
                kwargs,
                |dict| dict.insert(key1.clone(), val1.clone()),
                |kwargsdict| kwargsdict.insert(key2.clone(), val2.clone()),
            );
        } else {
            return Ok(self
                .named
                .insert(key.to_string(), value)
                .unwrap_or(Value::new(NoneType::None)));
        }
    }

    fn remaining(&self) -> usize {
        self.named.len()
    }

    fn check_no_more_args(&self) -> Result<(), ValueError> {
        Ok(())
    }

    fn into_hash_map<T: TryParamConvertFromValue>(
        mut self,
    ) -> Result<SmallMap<String, T>, ValueError> {
        let mut r = SmallMap::with_capacity(self.remaining());

        for (k, v) in self.named.into_iter() {
            let v: Result<_, _> = T::try_from(v);
            let v = v.map_err(|_| ValueError::IncorrectParameterTypeNamed(""))?;
            r.insert(k, v);
        }
        if let Some(ref kwargs) = self.kwargs_arg.take() {
            let kwargs: &Value = kwargs;
            for k in kwargs.iter() {
                for k in k.iter() {
                    let k: Value = k;
                    r.insert(
                        k.to_str(),
                        T::try_from(kwargs.at(k)?)
                            .map_err(|_| ValueError::IncorrectParameterTypeNamed(""))?,
                    );
                }
            }
        }
        Ok(r)
    }

    pub fn items(&self) -> Vec<(Value, Value)> {
        let mut r = Vec::with_capacity(self.remaining());
        for (k, v) in self.named.iter() {
            r.push((Value::new(k.clone()), v.clone()));
        }
        if let Some(ref kwargs) = self.kwargs_arg {
            let kwargs: &Value = kwargs;
            for k in kwargs.iter() {
                for k in k.iter() {
                    let k: Value = k;
                    let v = kwargs.at(k.clone()).unwrap();
                    r.push((k, v));
                }
            }
        }
        r
    }

    pub fn remove(&mut self, key: &Value) -> Result<Option<Value>, ValueError> {
        if let Some(v) = self.named.remove(&key.to_str()) {
            return Ok(Some(v));
        }

        if let Some(ref mut kwargs) = self.kwargs_arg {
            return Self::map_kwargs_arg_mut(
                kwargs,
                |dict| dict.remove(&key),
                |kwargsdict| kwargsdict.remove(&key),
            );
        }

        Ok(None)
    }
}

impl TypedValue for KwargsDict {
    type Holder = MutableCell<Self>;

    /// Return a string describing the type of self, as returned by the type() function.
    const TYPE: &'static str = "kwargsdict";

    fn values_for_descendant_check_and_freeze<'a>(
        &'a self,
    ) -> Box<dyn Iterator<Item = Value> + 'a> {
        // TODO
        Box::new(iter::empty())
    }

    fn set_at(&mut self, attribute: Value, new_value: Value) -> Result<(), ValueError> {
        self.insert(attribute, new_value)?;
        Ok(())
    }

    /// Return a string representation of self, as returned by the repr() function.
    fn collect_repr(&self, s: &mut String) {
        s.push('<');
        s.push_str(Self::TYPE);
        s.push('>');
    }

    fn to_json(&self) -> String {
        panic!("unsupported for type {}", Self::TYPE)
    }

    /// Convert self to a Boolean truth value, as returned by the bool() function.
    fn to_bool(&self) -> bool {
        // TODO
        true
    }

    fn get_attr(&self, attr: &str) -> ValueResult {
        panic!("no attr {}", attr)
    }

    /// Perform an array or dictionary indirection.
    ///
    /// This returns the result of `a[index]` if `a` is indexable.
    fn at(&self, index: Value) -> ValueResult {
        if let Some(ref v) = index.value_holder().find_in(&self.named) {
            return Ok((*v).clone());
        }

        if let Some(ref kw) = self.kwargs_arg {
            return kw.at(index);
        }

        Err(ValueError::KeyNotFound(index))
    }

    fn slice(
        &self,
        _start: Option<Value>,
        _stop: Option<Value>,
        _stride: Option<Value>,
    ) -> ValueResult {
        unimplemented!("could be done")
    }

    /// Returns an iterable over the value of this container if this value hold an iterable
    /// container.
    fn iter(&self) -> Result<&dyn TypedIterable, ValueError> {
        Ok(self)
    }

    /// Returns the length of the value, if this value is a sequence.
    fn length(&self) -> Result<i64, ValueError> {
        unimplemented!("len")
    }

    fn is_in(&self, other: &Value) -> Result<bool, ValueError> {
        if let Some(ref v) = other.value_holder().find_in(&self.named) {
            return Ok(true);
        }

        if let Some(ref kw) = self.kwargs_arg {
            return kw.is_in(other);
        }

        return Ok(false);
    }

    fn add(&self, _other: &Self) -> Result<Self, ValueError> {
        unimplemented!("add")
    }
}

impl From<KwargsDict> for Value {
    fn from(a: KwargsDict) -> Value {
        let mut v = Value::new(a);
        v.freeze();
        v.shared()
    }
}

pub enum FunctionInvoker<'a> {
    Native(NativeFunctionInvoker<'a>),
    Def(DefInvoker<'a>),
}

impl<'a> FunctionInvoker<'a> {
    pub fn invoke(self, context: &EvaluationContext) -> ValueResult {
        match self {
            FunctionInvoker::Native(inv) => inv.invoke(context),
            FunctionInvoker::Def(inv) => inv.invoke(context),
        }
    }

    pub fn push_pos(&mut self, v: Value) {
        match self {
            FunctionInvoker::Native(ref mut inv) => inv.push_pos(v),
            FunctionInvoker::Def(ref mut inv) => inv.push_pos(v),
        }
    }

    pub fn push_args(&mut self, v: Value) {
        match self {
            FunctionInvoker::Native(ref mut inv) => inv.push_args(v),
            FunctionInvoker::Def(ref mut inv) => inv.push_args(v),
        }
    }

    pub fn push_named(&mut self, name: &str, v: Value) {
        match self {
            FunctionInvoker::Native(ref mut inv) => inv.push_named(name, v),
            FunctionInvoker::Def(ref mut inv) => inv.push_named(name, v),
        }
    }

    pub fn push_kwargs(&mut self, v: Value) {
        match self {
            FunctionInvoker::Native(ref mut inv) => inv.push_kwargs(v),
            FunctionInvoker::Def(ref mut inv) => inv.push_kwargs(v),
        }
    }
}

#[doc(hidden)]
pub struct ParameterParser<'a> {
    // signature: &'a [FunctionParameter],
    // current parameter index in function signature
    signature: &'a [FunctionParameter],
    index: usize,
    function_type: &'a FunctionType,
    args: ArgsArray,
    kwargs: KwargsDict,
}

impl<'a> ParameterParser<'a> {
    pub fn new(
        signature: &'a [FunctionParameter],
        function_type: &'a FunctionType,
        positional: Vec<Value>,
        named: SmallMap<String, Value>,
        args: Option<Value>,
        kwargs_arg: Option<Value>,
    ) -> Result<ParameterParser<'a>, ValueError> {
        /*
        // Collect args
        let mut av = positional;
        if let Some(x) = args {
            match x.iter() {
                Ok(y) => av.extend(y.iter()),
                Err(..) => return Err(FunctionError::ArgsArrayIsNotIterable.into()),
            }
        };
        let positional = av.into_iter();
        // Collect kwargs
        let mut kwargs = named;
        if let Some(x) = kwargs_arg {
            match x.iter() {
                Ok(y) => {
                    for n in &y {
                        if n.get_type() == "string" {
                            let k = n.to_str();
                            if let Ok(v) = x.at(n) {
                                kwargs.insert(k, v);
                            } else {
                                return Err(FunctionError::KWArgsDictIsNotMappable.into());
                            }
                        } else {
                            return Err(FunctionError::ArgsValueIsNotString.into());
                        }
                    }
                }
                Err(..) => return Err(FunctionError::KWArgsDictIsNotMappable.into()),
            }
        }

        Ok(ParameterParser {
            signature,
            index: 0,
            function_type,
            positional,
            kwargs,
        })
        */
        Ok(ParameterParser {
            signature,
            function_type,
            index: 0,
            args: ArgsArray::new(positional, args),
            kwargs: KwargsDict::new(named, kwargs_arg),
        })
    }

    pub fn next_normal(&mut self, name: &str) -> Result<Value, ValueError> {
        self.next_optional(name).ok_or_else(|| {
            FunctionError::NotEnoughParameter {
                missing: name.to_string(),
                function_type: self.function_type.clone(),
                signature: self.signature.to_owned(),
            }
            .into()
        })
    }

    pub fn next_optional(&mut self, name: &str) -> Option<Value> {
        if let Some(x) = self.args.next() {
            Some(x)
        } else if let Some(r) = self.kwargs.next(name) {
            Some(r.clone())
        } else {
            None
        }
    }

    pub fn next_with_default_value(&mut self, name: &str, default_value: &Value) -> Value {
        self.next_optional(name)
            .unwrap_or_else(|| default_value.clone())
    }

    pub fn next_args_array(&mut self) -> ArgsArray {
        mem::replace(&mut self.args, ArgsArray::new(Vec::new(), None))
    }
    /*
            index: usize,
        positional: Vec<Value>,
        args: Option<Value>,
    }

    pub struct KwargsDict {
        index: usize,
        named: SmallMap<String, Value>,
        kwargs_arg: Option<Value>,

    */

    pub fn next_kwargs_dict(&mut self) -> KwargsDict {
        mem::replace(&mut self.kwargs, KwargsDict::new(SmallMap::new(), None))
    }

    pub fn check_no_more_args(&mut self) -> Result<(), ValueError> {
        self.args.check_no_more_args()?;
        self.kwargs.check_no_more_args()?;
        Ok(())
    }

    /// This function is only called from macros
    pub fn next_arg(&mut self) -> Result<FunctionArg, ValueError> {
        // Macros call this function exactly once for each signature item.
        // So it's safe to panic here.
        let idx = self.index;
        self.index += 1;
        Ok(match &self.signature[idx] {
            FunctionParameter::Normal(ref name) => FunctionArg::Normal(self.next_normal(name)?),
            FunctionParameter::Optional(ref name) => {
                FunctionArg::Optional(self.next_optional(name))
            }
            FunctionParameter::WithDefaultValue(ref name, ref value) => {
                FunctionArg::Normal(self.next_with_default_value(name, value))
            }
            FunctionParameter::ArgsArray(..) => FunctionArg::ArgsArray(self.next_args_array()),
            FunctionParameter::KWArgsDict(..) => FunctionArg::KWArgsDict(self.next_kwargs_dict()),
        })
    }
}

pub struct NativeFunctionInvoker<'a> {
    function: &'a dyn Fn(&EvaluationContext, ParameterParser) -> ValueResult,
    signature: &'a [FunctionParameter],
    function_type: &'a FunctionType,
    positional: Vec<Value>,
    named: SmallMap<String, Value>,
    args: Option<Value>,
    kwargs_arg: Option<Value>,
}

impl<'a> NativeFunctionInvoker<'a> {
    pub fn new<F: Fn(&EvaluationContext, ParameterParser) -> ValueResult>(
        func: &'a NativeFunction<F>,
    ) -> Self {
        Self {
            function: &func.function,
            signature: &func.signature,
            function_type: &func.function_type,
            positional: Vec::new(),
            named: SmallMap::new(),
            args: None,
            kwargs_arg: None,
        }
    }

    pub fn invoke(self, context: &EvaluationContext) -> ValueResult {
        let parser = ParameterParser::new(
            self.signature,
            self.function_type,
            self.positional,
            self.named,
            self.args,
            self.kwargs_arg,
        )?;
        (*self.function)(context, parser)
    }

    pub fn push_pos(&mut self, v: Value) {
        self.positional.push(v);
    }

    pub fn push_args(&mut self, v: Value) {
        self.args = Some(v);
    }

    pub fn push_named(&mut self, name: &str, v: Value) {
        self.named.insert(name.to_string(), v);
    }

    pub fn push_kwargs(&mut self, v: Value) {
        self.kwargs_arg = Some(v);
    }
}

/// Function implementation for native (written in Rust) functions.
///
/// Public to be referenced in macros.
#[doc(hidden)]
pub struct NativeFunction<F: Fn(&EvaluationContext, ParameterParser) -> ValueResult> {
    /// Pointer to a native function.
    /// Note it is a function pointer, not `Box<Fn(...)>`
    /// to avoid generic instantiation and allocation for each native function.
    function: F,
    signature: Vec<FunctionParameter>,
    function_type: FunctionType,
}

impl<F: Fn(&EvaluationContext, ParameterParser) -> ValueResult + 'static> NativeFunction<F> {
    pub fn new(name: String, function: F, signature: Vec<FunctionParameter>) -> Value {
        Value::new(NativeFunction {
            function,
            signature,
            function_type: FunctionType::Native(name),
        })
    }
}

/// Define the function type
impl<F: Fn(&EvaluationContext, ParameterParser) -> ValueResult + 'static> TypedValue
    for NativeFunction<F>
{
    type Holder = ImmutableCell<NativeFunction<F>>;

    fn values_for_descendant_check_and_freeze<'a>(
        &'a self,
    ) -> Box<dyn Iterator<Item = Value> + 'a> {
        Box::new(iter::empty())
    }

    fn collect_str(&self, s: &mut String) {
        collect_str(&self.function_type, &self.signature, s);
    }

    fn collect_repr(&self, s: &mut String) {
        collect_repr(&self.function_type, &self.signature, s);
    }

    const TYPE: &'static str = "function";

    fn new_invoker(&self) -> Result<FunctionInvoker, ValueError> {
        Ok(FunctionInvoker::Native(NativeFunctionInvoker::new(self)))
    }
}

impl TypedValue for WrappedMethod {
    type Holder = ImmutableCell<WrappedMethod>;

    fn values_for_descendant_check_and_freeze<'a>(
        &'a self,
    ) -> Box<dyn Iterator<Item = Value> + 'a> {
        Box::new(vec![self.method.clone(), self.self_obj.clone()].into_iter())
    }

    fn function_id(&self) -> Option<FunctionId> {
        Some(FunctionId(self.method.data_ptr()))
    }

    fn collect_str(&self, s: &mut String) {
        self.method.collect_str(s);
    }

    fn collect_repr(&self, s: &mut String) {
        self.method.collect_repr(s);
    }
    const TYPE: &'static str = "function";

    fn new_invoker(&self) -> Result<FunctionInvoker, ValueError> {
        let mut inv = self.method.new_invoker()?;
        inv.push_pos(self.self_obj.clone());
        Ok(inv)
    }
}
