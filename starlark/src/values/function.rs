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
    WithDefaultValue(String, FrozenValue),
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
    ArgsArray(Vec<Value>),
    KWArgsDict(SmallMap<String, Value>),
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
            FunctionArg::ArgsArray(v) => Ok(v
                .into_iter()
                .map(T::try_from)
                .collect::<Result<Vec<T>, _>>()
                .map_err(|_| ValueError::IncorrectParameterTypeNamed(param_name))?),
            _ => Err(ValueError::IncorrectParameterType),
        }
    }

    pub fn into_kw_args_dict<T: TryParamConvertFromValue>(
        self,
        param_name: &'static str,
    ) -> Result<SmallMap<String, T>, ValueError> {
        match self {
            FunctionArg::KWArgsDict(dict) => Ok({
                let mut r = SmallMap::new();
                for (k, v) in dict {
                    r.insert(
                        k,
                        T::try_from(v)
                            .map_err(|_| ValueError::IncorrectParameterTypeNamed(param_name))?,
                    );
                }
                r
            }),
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

pub type StarlarkFunctionPrototype = dyn Fn(&EvaluationContext, Vec<FunctionArg>) -> ValueResult;

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
        Value::make_pseudo(WrappedMethod { method, self_obj })
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
        .take(6)
        .map(|x| -> String {
            match x {
                FunctionParameter::Normal(ref name) => name.clone(),
                FunctionParameter::Optional(ref name) => format!("?{}", name),
                FunctionParameter::WithDefaultValue(ref name, ref value) => {
                    format!("{} = {}", name, Value::from_frozen(value.clone()).to_repr())
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
                    format!("{} = {}", name, Value::from_frozen(value.clone()).to_repr())
                }
                FunctionParameter::ArgsArray(ref name) => format!("*{}", name),
                FunctionParameter::KWArgsDict(ref name) => format!("**{}", name),
            }
        })
        .collect();
    collector.push_str(&format!("{}({})", function_type.to_str(), v.join(", ")));
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
    args: vec::IntoIter<Value>,
    kwargs: SmallMap<String, Value>,
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
        // Collect args
        let mut av = positional;
        if let Some(x) = args {
            match x.iter() {
                Ok(y) => av.extend(y.iter()),
                Err(..) => return Err(FunctionError::ArgsArrayIsNotIterable.into()),
            }
        };
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
            args: av.into_iter(),
            kwargs,
        })
        /*
        Ok(ParameterParser {
            signature,
            function_type,
            index: 0,
            args: ArgsArray::new(positional, args),
            kwargs: KwargsDict::new(named, kwargs_arg),
        })
        */
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
        } else if let Some(r) = self.kwargs.remove(name) {
            Some(r.clone())
        } else {
            None
        }
    }

    pub fn next_with_default_value(&mut self, name: &str, default_value: &FrozenValue) -> Value {
        self.next_optional(name)
            .unwrap_or_else(|| Value::from_frozen(default_value.clone()))
    }

    pub fn next_args_array(&mut self) -> Vec<Value> {
        std::mem::replace(&mut self.args, Vec::new().into_iter()).collect()
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

    pub fn next_kwargs_dict(&mut self) -> SmallMap<String, Value> {
        std::mem::replace(&mut self.kwargs, SmallMap::new())
    }

    pub fn check_no_more_args(&mut self) -> Result<(), ValueError> {
        // self.args.check_no_more_args()?;
        // self.kwargs.check_no_more_args()?;
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

impl<F: Fn(&EvaluationContext, ParameterParser) -> ValueResult + Send + Sync + 'static> NativeFunction<F> {
    pub fn new(name: String, function: F, signature: Vec<FunctionParameter>) -> Value {
        Value::new(NativeFunction {
            function,
            signature,
            function_type: FunctionType::Native(name),
        })
    }
}

impl<F: Fn(&EvaluationContext, ParameterParser) -> ValueResult + Send + Sync + 'static>  ImmutableValue for NativeFunction<F> {}

/// Define the function type
impl<F: Fn(&EvaluationContext, ParameterParser) -> ValueResult + 'static> TypedValue
    for NativeFunction<F>
{
    fn collect_str(&self, s: &mut String) {
        collect_str(&self.function_type, &self.signature, s);
    }

    fn collect_repr(&self, s: &mut String) {
        collect_repr(&self.function_type, &self.signature, s);
    }

    fn get_type(&self) -> &'static str {
        "function"
    }
    fn new_invoker(&self) -> Result<FunctionInvoker, ValueError> {
        Ok(FunctionInvoker::Native(NativeFunctionInvoker::new(self)))
    }

    fn as_dyn_any(&self) -> &dyn Any {
        self
    }
}

impl<F: Fn(&EvaluationContext, ParameterParser) -> ValueResult + 'static> Clone
    for NativeFunction<F>
{
    fn clone(&self) -> Self {
        unimplemented!()
    }
}

// Wrapper for method that have been affected the self object
#[derive(Clone)]
pub(crate) struct WrappedMethod {
    method: Value,
    self_obj: Value,
}

impl MutableValue for WrappedMethod {
    fn freeze(&self) -> Result<FrozenValue, ValueError> { unimplemented!() }
    fn as_dyn_any_mut(&mut self) -> &mut dyn Any { self }
}


impl TypedValue for WrappedMethod {

    fn naturally_mutable(&self) -> bool {
        true
    }

    fn function_id(&self) -> Option<FunctionId> {
        Some(FunctionId(self.method.data_ptr()))
    }

    fn as_dyn_any(&self) -> &dyn Any {
        self
    }

    fn collect_str(&self, s: &mut String) {
        self.method.collect_str(s);
    }

    fn collect_repr(&self, s: &mut String) {
        self.method.collect_repr(s);
    }
    fn get_type(&self) -> &'static str {
        "function"
    }

    fn new_invoker(&self) -> Result<FunctionInvoker, ValueError> {
        let mut inv = self.method.new_invoker()?;
        inv.push_pos(self.self_obj.clone());
        Ok(inv)
    }
}
