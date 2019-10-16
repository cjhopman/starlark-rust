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

use crate::environment::{
    Environment, LocalEnvironment, EnvironmentError, FrozenEnvironment, TypeValues, WeakFrozenEnvironment,
};
use crate::eval::call_stack::CallStack;
use crate::eval::EvalResult;
use crate::eval::{
    eval_stmt, EvalException, EvaluationContext, EvaluationContextEnvironment, IndexedLocals,
};
use crate::small_map::SmallMap;
use crate::syntax::ast::{AstParameter, AstStatement, AstString, Expr, Parameter, Statement};
use crate::values::dict::Dictionary;
use crate::values::error::ValueError;
use crate::values::function::*;
use crate::values::none::NoneType;
use crate::values::{function, mutability::ImmutableCell, Binder, TypedValue, Value, ValueResult};
use codemap::{CodeMap, Spanned};
use codemap_diagnostic::Diagnostic;
use std::cell::RefCell;
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
    non_local_names: HashSet<String>,
    args_slot: usize,
    kwargs_slot: usize,
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

        let mut non_local_names = HashSet::new();
        DefCompiled::collect_locals(&suite, &mut local_names_to_indices, &mut non_local_names);

        let suite = DefCompiled::transform_locals(suite, &local_names_to_indices);

        let suite = Statement::compile(suite)?;

        let mut args_slot = params.len();
        let mut kwargs_slot = params.len();
        for i in 0..params.len() {
            match params[i].node {
                Parameter::Normal(..) => {}
                Parameter::WithDefaultValue(..) => {}
                Parameter::Args(..) => {
                    args_slot = i;
                }
                Parameter::KWArgs(..) => {
                    kwargs_slot = i;
                }
            }
        }

        for name in local_names_to_indices.keys() {
            non_local_names.remove(name);
        }

        Ok(DefCompiled {
            name,
            params,
            args_slot,
            kwargs_slot,
            suite,
            local_names_to_indices,
            non_local_names,
        })
    }

    fn collect_locals(
        stmt: &AstStatement,
        local_names_to_indices: &mut HashMap<String, usize>,
        all_refs: &mut HashSet<String>,
    ) {
        match stmt.node {
            Statement::Assign(ref dest, _, ref expr) => {
                Expr::collect_locals_from_assign_expr(dest, local_names_to_indices);

                Expr::collect_refs(dest, all_refs);
                Expr::collect_refs(expr, all_refs);
            }
            Statement::For(ref dest, ref cond, ref body) => {
                Expr::collect_locals_from_assign_expr(dest, local_names_to_indices);

                Expr::collect_refs(dest, all_refs);
                Expr::collect_refs(cond, all_refs);
                DefCompiled::collect_locals(body, local_names_to_indices, all_refs);
            }
            Statement::Statements(ref stmts) => {
                for stmt in stmts {
                    DefCompiled::collect_locals(stmt, local_names_to_indices, all_refs);
                }
            }
            Statement::If(ref cond, ref then_block) => {
                Expr::collect_refs(cond, all_refs);
                DefCompiled::collect_locals(then_block, local_names_to_indices, all_refs);
            }
            Statement::IfElse(ref cond, ref then_block, ref else_block) => {
                Expr::collect_refs(cond, all_refs);
                DefCompiled::collect_locals(then_block, local_names_to_indices, all_refs);
                DefCompiled::collect_locals(else_block, local_names_to_indices, all_refs);
            }
            Statement::Return(Some(ref expr)) => {
                Expr::collect_refs(expr, all_refs);
            }
            Statement::Expression(ref expr) => {
                Expr::collect_refs(expr, all_refs);
            }
            Statement::Return(None) | Statement::Break | Statement::Continue | Statement::Pass => {}
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
                Statement::Def(..) | Statement::Load(..) | Statement::DefCompiled(..) => {
                    unreachable!()
                }
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
    bound: bool,
    signature: Vec<FunctionParameter>,
    function_type: FunctionType,
    captured_env: Option<HashMap<String, Value>>,
    map: Arc<Mutex<CodeMap>>,
    stmt: DefCompiled,
}

impl Def {
    pub fn new(
        module: String,
        signature: Vec<FunctionParameter>,
        stmt: DefCompiled,
        map: Arc<Mutex<CodeMap>>,
    ) -> Value {
        Value::new(Def {
            bound: false,
            function_type: FunctionType::Def(stmt.name.node.clone(), module),
            signature,
            stmt,
            captured_env: None,
            map,
        })
    }

    pub fn capture_env(&self, vars : &dyn Binder) -> Result<HashMap<String, Value>, ValueError> {
        let mut captured_env = HashMap::new();
        for n in &self.stmt.non_local_names {
            match vars.get(n)? {
                Some(v) => { captured_env.insert(n.clone(), v); },
                None => {
                    // TODO
                    /*
                        let v = vars
                            .get(n)
                            .ok_or_else(|| crate::values::error::RuntimeError {
                                code: "bad",
                                message: format!("couldn't find {}", n),
                                label: "".to_string(),
                            })?;
                        captured_env.insert((*n).clone(), v);
                    */
                }
            }
        }
        Ok(captured_env)
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
        Ok(FunctionInvoker::Def(DefInvoker::new(
            self,
            &self.stmt.local_names_to_indices,
            self.stmt.args_slot,
            self.stmt.kwargs_slot,
        )))
    }

    fn bind(&self, vars: &dyn Binder) -> Result<Option<Value>, ValueError> {
        if self.bound {
            return Ok(None);
        }

        // println!("binding {}", self.stmt.name.node);
        if self.stmt.non_local_names.is_empty() {
            // println!("nothing to bind");
            return Ok(None);
        }

        let captured_env = self.capture_env(vars)?;

        // println!("non-local names: {:?}", self.stmt.non_local_names);
        // println!("bound names: {:?}", captured_env.keys());

        Ok(Some(Value::new(Def {
            bound: true,
            function_type: self.function_type.clone(),
            signature: self.signature.clone(),
            stmt: self.stmt.clone(),
            captured_env: Some(captured_env),
            map: self.map.clone(),
        })))
    }
}

#[doc(hidden)]
pub struct IndexedParams<'a> {
    // signature: &'a [FunctionParameter],
    // current parameter index in function signature
    signature: &'a [FunctionParameter],
    local_names_to_indices: &'a HashMap<String, usize>,

    args_slot: usize,
    args_start: usize,
    args_len: usize,

    has_extra_positional: bool,
    extra_positional: RefCell<Vec<Value>>,
    star_args: Option<Value>,

    has_extra_named: bool,
    extra_named: RefCell<SmallMap<Value, Value>>,
    star_kwargs: Option<Value>,
}

impl<'a> IndexedParams<'a> {
    pub fn new(
        signature: &'a [FunctionParameter],
        local_names_to_indices: &'a HashMap<String, usize>,
        args_slot: usize,
        args_start: usize,
        positional: Vec<Value>,
        named: SmallMap<Value, Value>,
        args: Option<Value>,
        kwargs_arg: Option<Value>,
    ) -> IndexedParams<'a> {
        let args_len = args.as_ref().map(|v| v.length().unwrap()).unwrap_or(0) as usize;
        IndexedParams {
            signature,
            local_names_to_indices,

            args_slot,
            args_start,
            args_len,

            has_extra_positional: !positional.is_empty(),
            extra_positional: RefCell::new(positional),
            star_args: args,

            has_extra_named: !named.is_empty(),
            extra_named: RefCell::new(named),
            star_kwargs: kwargs_arg,
        }
    }

    pub fn fill_slot(
        &self,
        slot: usize,
        slot_name: &str,
        slots: &mut Vec<Option<Value>>,
    ) -> Option<Value> {
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
                let v = self
                    .get_normal(slot, name, slots)
                    .or_else(|| Some(default.clone()));
                slots[slot] = v.clone();
                v
            }
            Some(FunctionParameter::ArgsArray(ref name)) => {
                // A non-obvious property of a function that accepts *args: if there are any named args
                // passed to the function, then either *args will be empty, or there will be an error.

                // TODO: check for the error here.
                assert!(name == slot_name);
                match (self.has_extra_positional, &self.star_args) {
                    (false, None) => {
                        let v = Value::from(Vec::<Value>::new());
                        slots[slot] = Some(v.clone());
                        Some(v)
                    }
                    (false, Some(..)) => {
                        self.expand_args(slots);
                        slots[slot].clone()
                    }
                    (true, None) => {
                        let vec =
                            std::mem::replace(&mut *self.extra_positional.borrow_mut(), Vec::new());
                        let v = Value::from(vec);
                        slots[slot] = Some(v.clone());
                        Some(v)
                    }
                    (true, Some(star_args)) => {
                        let mut vec =
                            std::mem::replace(&mut *self.extra_positional.borrow_mut(), Vec::new());
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
                match (self.has_extra_named, &self.star_kwargs) {
                    (false, None) => {
                        let v = Dictionary::new();
                        slots[slot] = Some(v.clone());
                        Some(v)
                    }
                    (true, None) => {
                        let v = Value::new(Dictionary::from(std::mem::replace(
                            &mut *self.extra_named.borrow_mut(),
                            SmallMap::new(),
                        )));
                        slots[slot] = Some(v.clone());
                        Some(v)
                    }
                    _ => {
                        self.expand_kwargs(slots, slot);
                        slots[slot].clone()
                    }
                }
            }
            None => None,
        }
    }

    fn expand_kwargs(&self, slots: &mut Vec<Option<Value>>, slot: usize) {
        // println!("expanding kwargs");
        let mut named = SmallMap::new();
        if self.has_extra_named {
            std::mem::swap(&mut *self.extra_named.borrow_mut(), &mut named);
        }
        let kwargs = self.star_kwargs.as_ref().unwrap();
        for k in kwargs.iter().unwrap().into_iter() {
            let s = k.to_str();
            match self.local_names_to_indices.get(&s) {
                // we might have a match for a non-param local
                Some(found_slot) if *found_slot < slot => {
                    // println!("got slot {} for {}", slot, s);
                    if slots[*found_slot].is_none() {
                        slots[*found_slot] = Some(kwargs.at(k).unwrap());
                    }
                }
                _ => {
                    // println!("inserting {}", s);
                    named.insert(k.clone(), kwargs.at(k).unwrap());
                }
            }
        }

        slots[slot] = Some(Value::new(Dictionary::from(named)));
    }

    fn expand_args(&self, slots: &mut Vec<Option<Value>>) {
        let star_args = self.star_args.as_ref().expect("shouldn't be possible");
        let iter = star_args
            .iter()
            .expect(&format!("odd {}", self.star_args.as_ref().unwrap()));
        let mut args_iter = iter.into_iter();
        let mut idx = self.args_start;

        while idx < self.args_slot {
            match args_iter.next() {
                Some(v) => {
                    if slots[idx].is_none() {
                        slots[idx] = Some(v.clone());
                    }
                    idx += 1;
                }
                None => break,
            }
        }

        if self.args_slot < self.signature.len() {
            if let FunctionParameter::ArgsArray(..) = self.signature[self.args_slot] {
            } else {
                panic!("not a *args {}", self.signature[self.args_slot].name());
            }

            let vec: Vec<Value> = args_iter.map(|v| v.clone()).collect();
            if slots[self.args_slot].is_none() {
                slots[self.args_slot] = Some(Value::from(vec));
            } else {
                panic!("how did this happen to me?")
            }
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

    pub fn get_normal(
        &self,
        slot: usize,
        name: &str,
        slots: &mut Vec<Option<Value>>,
    ) -> Option<Value> {
        if self.has_extra_positional {
            panic!("weird, there shouldn't be extra positional args at this point");
        }

        // println!("maybe expanding args");
        if slot < self.args_start + self.args_len {
            if let Some(..) = self.star_args {
                // println!("really expanding args");
                self.expand_args(slots);
            }
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
    num_params: usize,
    idx: usize,

    args_slot: usize,
    extra_positional: Vec<Value>,
    star_args: Option<Value>,

    kwargs_slot: usize,
    extra_named: SmallMap<Value, Value>,
    star_kwargs: Option<Value>,

    captured_env: HashMap<String, Value>,

    slots: Vec<Option<Value>>,
}

impl<'a> DefInvoker<'a> {
    fn new(
        def: &'a Def,
        name_to_index: &'a HashMap<String, usize>,
        args_slot: usize,
        kwargs_slot: usize,
    ) -> Self {
        let slots_count = name_to_index.len();
        Self {
            def,
            name_to_index,
            num_params: def.stmt.params.len(),
            idx: 0,
            args_slot,
            extra_positional: Vec::new(),
            star_args: None,
            kwargs_slot,
            extra_named: SmallMap::new(),
            star_kwargs: None,
            captured_env: HashMap::new(),
            slots: vec![None; slots_count],
        }
    }

    pub fn invoke(mut self, context: &EvaluationContext) -> ValueResult {
        // println!("invoking {}", self.def.stmt.name.node);
        let extra_positional = std::mem::replace(&mut self.extra_positional, Vec::new());
        let extra_named = std::mem::replace(&mut self.extra_named, SmallMap::new());
        let lazy_params: IndexedParams<'a> = IndexedParams::new(
            &self.def.signature,
            self.name_to_index,
            self.args_slot,
            self.idx,
            extra_positional,
            extra_named,
            self.star_args.take(),
            self.star_kwargs.take(),
        );

        let locals = IndexedLocals::with_state(
            self.name_to_index,
            std::mem::replace(&mut self.slots, Vec::new()),
            lazy_params,
        );

        let module_env = context.module_env();

        let local_capture;
        let captured_env;

        if let Some(ref env) = self.def.captured_env {
            // println!("pre-bound");
            captured_env = env;
        } else {
            // println!("late-binding");
            struct LocalBinder<'a> {
                context: &'a LocalEnvironment,
            }

            impl<'a> Binder for LocalBinder<'a> {
                fn get(&self, name: &str) -> Result<Option<Value>, ValueError> {
                    match self.context.get(name) {
                        Ok(v) => Ok(Some(v)),
                        _ => Ok(None),
                    }
                }
            }
            local_capture = self.def.capture_env(&LocalBinder{context: module_env})?;
            captured_env = &local_capture;
        }


        let mut ctx = EvaluationContext {
            call_stack: context.call_stack().to_owned(),
            env: EvaluationContextEnvironment::Function(module_env, captured_env, locals),
            type_values: context.type_values(),
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
            Some(sl) if *sl < self.num_params => {
                self.slots[*sl] = Some(v);
            }
            _ => {
                self.extra_named.insert(Value::new(name.to_string()), v);
            }
        }
    }

    pub fn push_kwargs(&mut self, v: Value) {
        self.star_kwargs = Some(v);
    }
}
