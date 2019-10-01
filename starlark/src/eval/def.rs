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

//! Implementation of `def`.

use crate::environment::{Environment, EnvironmentError, TypeValues};
use crate::eval::call_stack::CallStack;
use crate::eval::EvalResult;
use crate::eval::{
    eval_stmt, EvalException, EvaluationContext, EvaluationContextEnvironment, IndexedLocals,
};
use crate::small_map::SmallMap;
use crate::syntax::ast::{AstParameter, AstStatement, AstString, Expr, Parameter, Statement};
use crate::values::error::ValueError;
use crate::values::dict::Dictionary;
use crate::values::function::{*};
use crate::values::none::NoneType;
use crate::values::{function, mutability::ImmutableCell, TypedValue, Value, ValueResult};
use codemap::{CodeMap, Spanned};
use codemap_diagnostic::Diagnostic;
use std::collections::{HashMap, HashSet};
use std::convert::TryInto;
use std::iter;
use std::sync::{Arc, Mutex};

/// `def` AST with post-processing suitable for faster excecution
#[doc(hidden)]
#[derive(Debug, Clone)]
pub struct DefCompiled {
    pub(crate) name: AstString,
    pub(crate) params: Vec<AstParameter>,
    pub(crate) suite: AstStatement,
    local_names_to_indices: HashMap<String, usize>,
}

impl DefCompiled {
    pub fn new(
        name: AstString,
        params: Vec<AstParameter>,
        suite: AstStatement,
    ) -> Result<DefCompiled, Diagnostic> {
        let mut local_names_to_indices = HashMap::new();

        for p in &params {
            let len = local_names_to_indices.len();
            // verification ensures there's no duplicate names
            local_names_to_indices.insert(p.name().to_owned(), len);
        }

        let params: Result<Vec<_>, _> = params.into_iter().map(|p| Parameter::compile(p)).collect();
        let params = params?;

        DefCompiled::collect_locals(&suite, &mut local_names_to_indices);

        let suite = DefCompiled::transform_locals(suite, &local_names_to_indices);

        let suite = Statement::compile(suite)?;

        Ok(DefCompiled {
            name,
            params,
            suite,
            local_names_to_indices,
        })
    }

    fn collect_locals(stmt: &AstStatement, local_names_to_indices: &mut HashMap<String, usize>) {
        match stmt.node {
            Statement::Assign(ref dest, ..) => {
                Expr::collect_locals_from_assign_expr(dest, local_names_to_indices);
            }
            Statement::For(ref dest, _, ref body) => {
                Expr::collect_locals_from_assign_expr(dest, local_names_to_indices);
                DefCompiled::collect_locals(body, local_names_to_indices);
            }
            Statement::Statements(ref stmts) => {
                for stmt in stmts {
                    DefCompiled::collect_locals(stmt, local_names_to_indices);
                }
            }
            Statement::If(_, ref then_block) => {
                DefCompiled::collect_locals(then_block, local_names_to_indices);
            }
            Statement::IfElse(_, ref then_block, ref else_block) => {
                DefCompiled::collect_locals(then_block, local_names_to_indices);
                DefCompiled::collect_locals(else_block, local_names_to_indices);
            }
            Statement::Break
            | Statement::Continue
            | Statement::Pass
            | Statement::Return(..)
            | Statement::Expression(..) => {}
            Statement::Load(..) | Statement::Def(..) | Statement::DefCompiled(..) => unreachable!(),
        }
    }

    /// Transform statement replacing local variables access by name with access by index
    fn transform_locals(stmts: AstStatement, locals: &HashMap<String, usize>) -> AstStatement {
        Box::new(Spanned {
            span: stmts.span,
            node: match stmts.node {
                Statement::Assign(left, op, right) => Statement::Assign(
                    Expr::transform_locals_to_slots(left, locals),
                    op,
                    Expr::transform_locals_to_slots(right, locals),
                ),
                Statement::For(var, collection, body) => Statement::For(
                    Expr::transform_locals_to_slots(var, locals),
                    Expr::transform_locals_to_slots(collection, locals),
                    DefCompiled::transform_locals(body, locals),
                ),
                Statement::Statements(stmts) => Statement::Statements(
                    stmts
                        .into_iter()
                        .map(|stmt| DefCompiled::transform_locals(stmt, locals))
                        .collect(),
                ),
                Statement::If(cond, then_block) => Statement::If(
                    Expr::transform_locals_to_slots(cond, locals),
                    DefCompiled::transform_locals(then_block, locals),
                ),
                Statement::IfElse(cond, then_block, else_block) => Statement::IfElse(
                    Expr::transform_locals_to_slots(cond, locals),
                    DefCompiled::transform_locals(then_block, locals),
                    DefCompiled::transform_locals(else_block, locals),
                ),
                s @ Statement::Break | s @ Statement::Continue | s @ Statement::Pass => s,
                Statement::Def(..) | Statement::Load(..) | Statement::DefCompiled(..) => unreachable!(),
                Statement::Expression(expr) => {
                    Statement::Expression(Expr::transform_locals_to_slots(expr, locals))
                }
                Statement::Return(expr) => Statement::Return(
                    expr.map(|expr| Expr::transform_locals_to_slots(expr, locals)),
                ),
            },
        })
    }
}

/// Starlark function internal representation and implementation of [`TypedValue`].
pub(crate) struct Def {
    signature: Vec<FunctionParameter>,
    function_type: FunctionType,
    param_names: HashSet<String>,
    captured_env: Environment,
    map: Arc<Mutex<CodeMap>>,
    stmt: DefCompiled,
}

impl Def {
    pub fn new(
        module: String,
        signature: Vec<FunctionParameter>,
        stmt: DefCompiled,
        map: Arc<Mutex<CodeMap>>,
        env: Environment,
    ) -> Value {
        // This can be implemented by delegating to `Function::new`,
        // but having a separate type allows slight more efficient implementation
        // and optimizations in the future.
        let param_names = signature
            .iter()
            .filter(|e| e.is_normal())
            .map(|e| e.name().to_string())
            .collect();

        Value::new(Def {
            function_type: FunctionType::Def(stmt.name.node.clone(), module),
            param_names,
            signature,
            stmt,
            captured_env: env,
            map,
        })
    }
}

impl TypedValue for Def {
    type Holder = ImmutableCell<Def>;

    const TYPE: &'static str = "function";

    fn values_for_descendant_check_and_freeze<'a>(
        &'a self,
    ) -> Box<dyn Iterator<Item = Value> + 'a> {
        Box::new(iter::empty())
    }

    fn collect_str(&self, collector: &mut String) {
        function::collect_str(&self.function_type, &self.signature, collector);
    }

    fn collect_repr(&self, collector: &mut String) {
        function::collect_repr(&self.function_type, &self.signature, collector);
    }

    fn new_invoker(&self) -> Result<FunctionInvoker, ValueError> {
        unimplemented!()
    }
}


#[doc(hidden)]
pub struct IndexedParams<'a> {
    // signature: &'a [FunctionParameter],
    // current parameter index in function signature
    signature: &'a [FunctionParameter],
    param_names: &'a std::collections::HashSet<String>,

    args_slot: usize,
    args_start: usize,
    args_len: usize,
    
    extra_positional: Vec<Value>,
    star_args: Option<Value>,

    extra_named: SmallMap<Value, Value>,
    star_kwargs: Option<Value>,
}

impl<'a> IndexedParams<'a> {
    pub fn new(
        signature: &'a [FunctionParameter],
        param_names: &'a std::collections::HashSet<String>,
        positional: Vec<Value>,
        named: SmallMap<String, Value>,
        args: Option<Value>,
        kwargs_arg: Option<Value>,
    ) -> IndexedParams<'a> {
        /*
        let args_len = args.as_ref().map(|v| v.length().unwrap()).unwrap_or(0) as usize;
        IndexedParams {
            signature,
            param_names,
            positional,
            args,
            args_len,
            named,
            kwargs_arg,
        }
        */
        unimplemented!()
    }

    pub fn fill_slot(&mut self, slot: usize, slot_name: &str, slots: &mut Vec<Option<Value>>) -> Option<Value> {
        match self.signature.get(slot) {
            Some(FunctionParameter::Normal(ref name)) => {
                assert!(name == slot_name);
                let v = self.get_normal(slot, name, slots);
                slots[slot] = v.clone();
                v
            }
            Some(FunctionParameter::Optional(..)) => {
                unreachable!("optional params only exist in native functions")
            }
            Some(FunctionParameter::WithDefaultValue(ref name, ref default)) => {
                assert!(name == slot_name);
                let v = self.get_normal(slot, name, slots)
                    .or_else(|| Some(default.clone()));
                slots[slot] = v.clone();
                v
            }
            Some(FunctionParameter::ArgsArray(ref name)) => {
                // A non-obvious property of a function that accepts *args: if there are any named args
                // passed to the function, then either *args will be empty, or there will be an error.

                // TODO: check for the error here.
                assert!(name == slot_name);
                match (self.extra_positional.is_empty(), &self.star_args) {
                    (true, None) => {
                        let v = Value::from(Vec::<Value>::new());
                        slots[slot] = Some(v.clone());
                        Some(v)
                    },
                    (true, Some(..)) => {
                        self.expand_args(slots);
                        slots[slot].clone()
                    },
                    (false, None) => {
                        let v = Value::from(std::mem::replace(&mut self.extra_positional, Vec::new()));
                        slots[slot] = Some(v.clone());
                        Some(v)
                    },
                    (false, Some(star_args)) => {
                        let mut vec = std::mem::replace(&mut self.extra_positional, Vec::new());
                        vec.reserve(vec.len() + (star_args.length().unwrap() as usize));
                        vec.extend(star_args.iter().unwrap().into_iter());
                        let v = Value::from(vec);
                        slots[slot] = Some(v.clone());
                        Some(v)
                    }                    
                }
            }
            Some(FunctionParameter::KWArgsDict(ref name)) => {
                assert!(name == slot_name);
                match (self.extra_named.is_empty(), &self.star_kwargs) {
                    (true, None) => {
                        let v = Dictionary::new();
                        slots[slot] = Some(v.clone());
                        Some(v)
                    },
                    (false, None) => {
                        let v = Value::new(Dictionary::from(std::mem::replace(&mut self.extra_named, SmallMap::new())));
                        slots[slot] = Some(v.clone());
                        Some(v)
                    },
                    _ => {
                        self.expand_kwargs(slots);
                        slots[slot].clone()
                    },                   
                }
            }
            None => None,
        }
    }

    fn expand_kwargs(&self, slots: &mut Vec<Option<Value>>) {

    }

    fn expand_args(&self, slots: &mut Vec<Option<Value>>) {
        let star_args = self.star_args.as_ref().unwrap();
        let iter = star_args.iter().unwrap();
        let mut args_iter = iter.into_iter();
        let idx = self.args_start;

        while idx < self.args_slot {
            match args_iter.next() {
                Some(v) => {
                    if slots[idx].is_none() {
                        slots[idx] = Some(v.clone());
                    }
                },
                None => break
            }
        }

        if self.args_slot < slots.len() {
            let vec : Vec<Value> = args_iter.map(|v| v.clone()).collect();
            slots[self.args_slot] = Some(Value::from(vec));
        } else {
            // TODO: verify consumed args
        }        
    }

    /*
        Normal(String),
        Optional(String),
        WithDefaultValue(String, Value),
        ArgsArray(String),
        KWArgsDict(String),

    */

    pub fn get_normal(&self, slot: usize, name: &str, slots: &mut Vec<Option<Value>>) -> Option<Value> {
        if !self.extra_positional.is_empty() {
            panic!("weird, there shouldn't be extra positional args at this point");
        }

        if self.args_start + self.args_len < slot {
            self.expand_args(slots);
            return slots[slot].clone();
        }

        if let Some(a) = &self.star_kwargs {
            return a.at(Value::new(name.to_string())).ok();
        }

        None
    }
}

pub struct DefInvoker<'a> {
    def: &'a Def,
    name_to_index: &'a HashMap<String, usize>,
    idx: usize,

    args_slot: usize,
    extra_positional: Vec<Value>,
    star_args: Option<Value>,

    kwargs_slot: usize,
    extra_named: SmallMap<String, Value>,
    star_kwargs: Option<Value>,

    slots: Vec<Option<Value>>,
}

impl<'a> DefInvoker<'a> {
    pub fn invoke(mut self, call_stack: &CallStack, type_values: TypeValues) -> ValueResult {
        let lazy_params : IndexedParams<'a>;

        let locals = IndexedLocals::with_state(self.name_to_index, std::mem::replace(&mut self.slots, Vec::new()), lazy_params);

        let mut ctx = EvaluationContext {
            call_stack: call_stack.to_owned(),
            env: EvaluationContextEnvironment::Function(
                self.def.captured_env.clone(),
                locals,
            ),
            type_values,
            map: self.def.map.clone(),
        };

        match eval_stmt(&self.def.stmt.suite, &mut ctx) {
            Err(EvalException::Return(_s, ret)) => Ok(ret),
            Err(x) => Err(ValueError::DiagnosedError(x.into())),
            Ok(..) => Ok(Value::new(NoneType::None)),
        }
    }

    pub fn push_pos(&mut self, v: Value) {
        let idx = self.idx;
        if idx == self.args_slot {
            self.extra_positional.push(v);
        } else {
            self.idx += 1;
            // TODO: verify not set?
            self.slots[idx] = Some(v);
        }
    }

    pub fn push_args(&mut self, v: Value) {
        self.star_args = Some(v);
    }

    pub fn push_named(&mut self, name: &str, v: Value) {
        match self.name_to_index.get(name) {
            Some(sl) => { self.slots[*sl] = Some(v); },
            None => { self.extra_named.insert(name.to_string(), v); },
        }
    }

    pub fn push_kwargs(&mut self, v: Value) {
        self.star_kwargs = Some(v);
    }
}
