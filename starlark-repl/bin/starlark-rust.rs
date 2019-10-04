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

//! A command line interpreter for Starlark, provide a REPL.

extern crate structopt;

#[macro_use]
extern crate starlark;

#[macro_use]
extern crate lazy_static;

use codemap::CodeMap;
use codemap_diagnostic::{ColorConfig, Diagnostic, Emitter};
use starlark::environment::Environment;
use starlark::environment::TypeValues;
use starlark::eval::interactive::{eval, eval_file, EvalError};
use starlark::eval::EvaluationContext;
use starlark::eval::FileLoader;
use starlark::stdlib::global_environment_with_extensions;
use starlark::syntax::ast::AstStatement;
use starlark::syntax::dialect::Dialect;
use starlark::syntax::parser::{parse, parse_file};
use starlark::values::Value;
use starlark_repl::{print_function, repl};
use std::io::prelude::*;
use std::process::exit;
use std::rc::Rc;
use std::sync::{Arc, Mutex};
use structopt::clap::AppSettings;
use structopt::StructOpt;

use starlark::values::error::*;
use starlark::values::function::*;
use starlark::values::none::*;
use starlark::values::*;

const EXIT_CODE_FAILURE: i32 = 2;

#[global_allocator]
static ALLOC: jemallocator::Jemalloc = jemallocator::Jemalloc;

#[derive(Debug, StructOpt)]
#[structopt(
    name = "starlark-repl",
    about = "Starlark in Rust interpreter",
    global_settings(&[AppSettings::ColoredHelp]),
)]
pub struct Opt {
    #[structopt(short = "a", long, help = "Parse and print AST instead of evaluating.")]
    ast: bool,

    #[structopt(
        short = "b",
        long,
        help = concat!(
            "Parse the build file format instead of full Starlark. See https://docs.rs/starlark/",
            env!("CARGO_PKG_VERSION"),
            "/starlark/eval/index.html#build_file",
        )
    )]
    build_file: bool,

    #[structopt(
        short = "c",
        help = "Starlark command to run after files have been parsed."
    )]
    command: Option<String>,

    #[structopt(short = "x", help = "no-bucky")]
    not_buck: bool,

    #[structopt(
        short = "r",
        long,
        conflicts_with = "command",
        help = "Run a REPL after files have been parsed."
    )]
    repl: bool,

    #[structopt(short = "t", long, help = "rule types file")]
    rules: Option<String>,

    #[structopt(long = "cells", help = "cells map")]
    cells: Option<String>,

    #[structopt(long = "config", help = "config")]
    config: Option<String>,

    #[structopt(name = "FILE", help = "Files to interpret")]
    files: Vec<String>,
}

use std;

type ValueMap = LinkedHashMap<::std::string::String, starlark::values::Value>;

fn some_func(
    __call_stack: &starlark::eval::call_stack::CallStack,
    __env: starlark::environment::TypeValues,
    mut args: ParameterParser,
    recorder: &std::rc::Rc<std::cell::RefCell<LinkedHashMap<String, ValueMap>>>,
) -> starlark::values::ValueResult {
    let map: LinkedHashMap<String, Value> = args.next_arg()?.into_kw_args_dict("kwargs")?;

    let name = map.get("name").unwrap();
    // println!("adding {}", name);

    recorder.borrow_mut().insert(name.to_string(), map);
    Ok::<Value, ValueError>(Value::from(NoneType::None))
}

fn provider_impl(
    __call_stack: &starlark::eval::call_stack::CallStack,
    __env: starlark::environment::TypeValues,
    mut args: starlark::values::function::ParameterParser,
) -> starlark::values::ValueResult {
    #[allow(unused_mut)]
    let mut kwargs: ::linked_hash_map::LinkedHashMap<
        ::std::string::String,
        starlark::values::Value,
    > = args.next_arg()?.into_kw_args_dict("kwargs")?;
    args.check_no_more_args()?;
    Ok(Value::new(starlark::stdlib::structs::StarlarkStruct {
        fields: kwargs,
    }))
}

starlark_module! {global_functions =>
    host_info() {
        /*
                    "is_linux", hostPlatform == Platform.LINUX,
            "is_macos", hostPlatform == Platform.MACOS,
            "is_windows", hostPlatform == Platform.WINDOWS,
            "is_freebsd", hostPlatform == Platform.FREEBSD,
            "is_unknown", hostPlatform == Platform.UNKNOWN);
    ImmutableMap<String, Object> arch =
        ImmutableMap.<String, Object>builder()
            .put("is_aarch64", hostArchitecture == Architecture.AARCH64)
            .put("is_arm", hostArchitecture == Architecture.ARM)
            .put("is_armeb", hostArchitecture == Architecture.ARMEB)
            .put("is_i386", hostArchitecture == Architecture.X86_32)
            .put("is_mips", hostArchitecture == Architecture.MIPS)
            .put("is_mips64", hostArchitecture == Architecture.MIPS64)
            .put("is_mipsel", hostArchitecture == Architecture.MIPSEL)
            .put("is_mipsel64", hostArchitecture == Architecture.MIPSEL64)
            .put("is_powerpc", hostArchitecture == Architecture.POWERPC)
            .put("is_ppc64", hostArchitecture == Architecture.PPC64)
            .put("is_unknown", hostArchitecture == Architecture.UNKNOWN)
            .put("is_x86_64", hostArchitecture == Architecture.X86_64)
            */
        let mut os : LinkedHashMap<String, Value> = LinkedHashMap::new();
        os.insert("is_linux".to_string(), Value::new(false));
        os.insert("is_macos".to_string(), Value::new(true));
        os.insert("is_windows".to_string(), Value::new(false));
        os.insert("is_freebsd".to_string(), Value::new(false));
        os.insert("is_unknown".to_string(), Value::new(false));
        let mut arch : LinkedHashMap<String, Value> = LinkedHashMap::new();
        arch.insert("is_aarch64".to_string(), Value::new(false));
        arch.insert("is_arm".to_string(), Value::new(false));
        arch.insert("is_armeb".to_string(), Value::new(false));
        arch.insert("is_i386".to_string(), Value::new(false));
        arch.insert("is_mips".to_string(), Value::new(false));
        arch.insert("is_mips64".to_string(), Value::new(false));
        arch.insert("is_mipsel".to_string(), Value::new(false));
        arch.insert("is_mipsel64".to_string(), Value::new(false));
        arch.insert("is_powerpc".to_string(), Value::new(false));
        arch.insert("is_ppc64".to_string(), Value::new(false));
        arch.insert("is_unknown".to_string(), Value::new(false));
        arch.insert("is_x86_64".to_string(), Value::new(true));
        let mut info : LinkedHashMap<String, Value> = LinkedHashMap::new();
        info.insert("os".to_string(), Value::new(starlark::stdlib::structs::StarlarkStruct{fields: os}));
        info.insert("arch".to_string(), Value::new(starlark::stdlib::structs::StarlarkStruct{fields: arch}));
        Ok(Value::new(starlark::stdlib::structs::StarlarkStruct{fields: info}))

    }

    provider(fields) {
        let mut signature = Vec::new();
        signature.push(starlark::values::function::FunctionParameter::KWArgsDict(
            "kwargs".to_owned(),
        ));
        let name = "uniquish".to_string();
        Ok(starlark::values::function::NativeFunction::new(
                        name.to_owned(),
                        provider_impl,
                        signature,
                    ))
    }
}

fn register_rule_def(
    env: starlark::environment::Environment,
    recorder: std::rc::Rc<std::cell::RefCell<LinkedHashMap<String, ValueMap>>>,
    name: &str,
) -> starlark::environment::Environment {
    let mut signature = Vec::new();
    signature.push(starlark::values::function::FunctionParameter::KWArgsDict(
        "kwargs".to_owned(),
    ));
    env.set(
        name,
        starlark::values::function::NativeFunction::new(
            name.to_owned(),
            move |c, t, p| some_func(c, t, p, &recorder),
            signature,
        ),
    )
    .unwrap();
    env
}

fn register_rule_exists(
    env: starlark::environment::Environment,
    recorder: std::rc::Rc<std::cell::RefCell<LinkedHashMap<String, ValueMap>>>,
) -> starlark::environment::Environment {
    let mut signature = Vec::new();
    signature.push(starlark::values::function::FunctionParameter::Normal(
        "rule_name".to_owned(),
    ));
    env.set(
        "rule_exists",
        starlark::values::function::NativeFunction::new(
            "rule_exists".to_owned(),
            move |c, t, mut p| {
                let k: String = p.next_arg()?.into_normal("")?;
                let exists = recorder.borrow().contains_key(&k);
                Ok(Value::new(exists))
            },
            signature,
        ),
    )
    .unwrap();
    env
}

use linked_hash_map::LinkedHashMap;

fn register_natives(env: starlark::environment::Environment) -> Environment {
    let mut map = LinkedHashMap::new();
    env.for_each_var(|k, v| {
        map.insert(k.clone().into(), v.clone());
    });

    env.set(
        "native",
        Value::new(starlark::stdlib::structs::StarlarkStruct { fields: map }),
    )
    .unwrap();
    env
}

use starlark::eval::EvalException;
use std::{collections::HashMap, path::Path, path::PathBuf};

mod buck {
    use super::*;

    pub struct SharedState {
        pub map: Arc<Mutex<HashMap<String, Environment>>>,
        pub parent_env: Environment,
        pub codemap: Arc<Mutex<CodeMap>>,
        pub cells: Rc<HashMap<String, PathBuf>>,
    }

    type ConfigMap = HashMap<String, HashMap<String, String>>;

    pub struct ParserInfo {
        package: PathBuf,
        config: Rc<ConfigMap>,
        shared: Rc<SharedState>,
    }

    impl ParserInfo {
        pub fn new(package: PathBuf, config: Rc<ConfigMap>, shared: Rc<SharedState>) -> Self {
            Self {
                package,
                config,
                shared,
            }
        }
    }

    struct ParserFileLoader {
        info: Rc<ParserInfo>,
    }

    use regex::Regex;

    impl FileLoader for ParserFileLoader {
        fn load(&self, path: &str) -> Result<Environment, EvalException> {
            lazy_static! {
                static ref RE: Regex =
                    Regex::new("(@(?P<cell>[^/]*))?(//(?P<package>[^:]*)?)?:(?P<filename>.*)")
                        .unwrap();
            }
            //println!("loading {}", path);

            let path = match RE.captures(path) {
                Option::None => panic!(),
                Option::Some(c) => {
                    let cell_path = c.name("cell").map_or(PathBuf::from_str(".").unwrap(), |m| {
                        self.info.shared.cells.get(m.as_str()).unwrap().clone()
                    });
                    let package_path = c.name("package").map_or(self.info.package.clone(), |p| {
                        PathBuf::from_str(p.as_str()).unwrap()
                    });
                    let filename = PathBuf::from_str(c.name("filename").unwrap().as_str()).unwrap();
                    cell_path.join(package_path).join(filename)
                }
            };

            let pathstr = path.to_str().unwrap();
            {
                let lock = self.info.shared.map.lock().unwrap();
                if lock.contains_key(pathstr) {
                    return Ok(lock.get(pathstr).unwrap().clone());
                }
            }

            // println!("resolved {:?}", path);

            let parser = Parser::new(Rc::new(ParserInfo::new(
                path.parent().unwrap().to_path_buf(),
                self.info.config.clone(),
                self.info.shared.clone(),
            )));

            let mut env = parser.create_env(path.to_str().unwrap());

            parser
                .super_eval_file(
                    &self.info.shared.codemap,
                    path.to_str().unwrap(),
                    Dialect::Bzl,
                    &mut env,
                    TypeValues::new(self.info.shared.parent_env.clone()),
                )
                .map_err(|e| EvalException::DiagnosedError(e))?;
            env.freeze();
            self.info
                .shared
                .map
                .lock()
                .unwrap()
                .insert(pathstr.to_string(), env.clone());
            Ok(env)
        }
    }

    pub struct Parser {
        info: Rc<ParserInfo>,
    }

    impl Parser {
        pub fn new(info: Rc<ParserInfo>) -> Self {
            Self { info: info }
        }
        pub fn new_file_loader(&self) -> impl FileLoader {
            ParserFileLoader {
                info: self.info.clone(),
            }
        }
        pub fn create_env(&self, path: &str) -> Environment {
            let env = self.info.shared.parent_env.child(path);
            let package = self.info.package.to_str().unwrap().to_string();
            let config = self.info.config.clone();

            let mut signature = Vec::new();
            signature.push(starlark::values::function::FunctionParameter::Normal(
                "$section".to_owned(),
            ));
            signature.push(starlark::values::function::FunctionParameter::Normal(
                "$key".to_owned(),
            ));
            signature.push(
                starlark::values::function::FunctionParameter::WithDefaultValue(
                    "$default".to_owned(),
                    Value::new(NoneType::None),
                ),
            );
            env.set(
                "read_config",
                starlark::values::function::NativeFunction::new(
                    "read_config".to_owned(),
                    move |c, t, mut p| {
                        let section: String = p.next_arg()?.into_normal("section")?;
                        let key: String = p.next_arg()?.into_normal("key")?;
                        let default: Value = p.next_arg()?.into_normal("default")?;
                        let val = config.get(&section).and_then(|s| s.get(&key));

                        match val {
                            Some(v) => Ok(Value::new(v.clone())),
                            None => Ok(default),
                        }
                    },
                    signature,
                ),
            )
            .unwrap();
            env.set(
                "package_name",
                starlark::values::function::NativeFunction::new(
                    "package_name".to_owned(),
                    move |c, t, p| Ok(Value::new(package.clone())),
                    Vec::new(),
                ),
            )
            .unwrap();

            env.set(
                "repository_name",
                starlark::values::function::NativeFunction::new(
                    "repository_name".to_owned(),
                    move |c, t, p| Ok(Value::new("".to_string())),
                    Vec::new(),
                ),
            )
            .unwrap();
            let env = register_natives(env);
            env
        }

        pub fn super_eval_file(
            &self,
            map: &Arc<Mutex<CodeMap>>,
            path: &str,
            build: Dialect,
            env: &mut Environment,
            type_values: TypeValues,
        ) -> Result<Value, Diagnostic> {
            let context = EvaluationContext::new(
                env.clone(),
                type_values,
                self.new_file_loader(),
                map.clone(),
            );
            let v = match starlark::eval::eval_stmt(&parse_file(map, path, build)?, &context) {
                Ok(v) => Ok(v),
                Err(p) => Err(p.into()),
            };
            // println!("{:?}", v);
            v
        }

        pub fn simple_eval_file(
            &self,
            map: &Arc<Mutex<CodeMap>>,
            path: &str,
            build: Dialect,
            env: &mut Environment,
            file_loader_env: Environment,
        ) -> Result<Value, Diagnostic> {
            self.super_eval_file(
                map,
                path,
                build,
                env,
                TypeValues::new(file_loader_env.clone()),
            )
        }

        pub fn eval_file(
            &self,
            path: &str,
            dialect: Dialect,
            env: &mut Environment,
            file_loader_env: Environment,
        ) -> Result<Option<Value>, EvalError> {
            self.transform_result(
                self.simple_eval_file(
                    &self.info.shared.codemap,
                    path,
                    dialect,
                    env,
                    file_loader_env,
                ),
                self.info.shared.codemap.clone(),
            )
        }

        fn transform_result(
            &self,
            result: Result<Value, Diagnostic>,
            codemap: Arc<Mutex<CodeMap>>,
        ) -> Result<Option<Value>, EvalError> {
            match result {
                Ok(ref v) if v.get_type() == "NoneType" => Ok(None),
                Ok(v) => Ok(Some(v)),
                Err(diagnostic) => Err(EvalError {
                    codemap,
                    diagnostic,
                }),
            }
        }
    }
}

use std::str::FromStr;

fn main() {
    let opt = Opt::from_args();

    let command = opt.command;
    let ast = opt.ast;
    let buck = !opt.not_buck;
    let recorder = std::rc::Rc::new(std::cell::RefCell::new(LinkedHashMap::new()));

    let mut cells = HashMap::new();

    let f = std::fs::File::open(opt.cells.unwrap()).unwrap();
    let file = std::io::BufReader::new(&f);
    for line in file.lines() {
        let line = line.unwrap();
        let sp: Vec<_> = line.split('=').collect();
        let left = sp[0].trim();
        let right = sp[1].trim();
        cells.insert(left.to_string(), PathBuf::from_str(right).unwrap());
    }

    /*
        bazel_skylib = ./third-party/skylark/bazel-skylib
        buck = .
        testlib = test/com/facebook/buck/testutil/integration/testlibs
    */

    let mut global = global_functions(print_function(global_environment_with_extensions()));

    let f = std::fs::File::open(opt.rules.unwrap()).unwrap();
    let file = std::io::BufReader::new(&f);
    for line in file.lines() {
        let line = line.unwrap();
        global = register_rule_def(global, recorder.clone(), &line);
    }

    let mut config = HashMap::new();
    let f = std::fs::File::open(opt.config.unwrap()).unwrap();
    let file = std::io::BufReader::new(&f);
    let mut section = "".to_string();
    for line in file.lines() {
        let line = line.unwrap();
        let line = line.trim();
        if line.starts_with('[') {
            section = line[1..line.len() - 1].to_string();
            if !config.contains_key(&section) {
                config.insert(section.clone(), HashMap::new());
            }
        } else {
            let sp: Vec<_> = line.split('=').collect();
            if sp.len() != 2 {
                println!("wtf: {}", line);
            } else {
                let key = sp[0];
                let val = sp[1];
                let s = config.get_mut(&section).unwrap();
                s.insert(key.to_string(), val.to_string());
            }
        }
    }

    let global = register_rule_exists(global, recorder.clone());
    global.freeze();

    let dialect = if opt.build_file {
        Dialect::Build
    } else {
        Dialect::Bzl
    };
    let free_args_empty = opt.files.is_empty();

    let config = Rc::new(config);
    for i in opt.files.into_iter() {
        if buck {
            let path: PathBuf = PathBuf::from_str(&i).unwrap();
            let shared = Rc::new(buck::SharedState {
                map: Arc::new(Mutex::new(HashMap::new())),
                parent_env: global.clone(),
                codemap: Arc::new(Mutex::new(CodeMap::new())),
                cells: Rc::new(cells.clone()),
            });

            let info = buck::ParserInfo::new(path.parent().unwrap().into(), config.clone(), shared);
            let parser = buck::Parser::new(Rc::new(info));
            let mut env = parser.create_env(path.to_str().unwrap());
            let res = parser.eval_file(&i, dialect, &mut env, global.clone());

            for (k, _) in &*recorder.borrow() {
                println!("{:?}", k);
            }

            maybe_print_or_exit(res);
        } else if ast {
            let codemap = Arc::new(Mutex::new(CodeMap::new()));
            maybe_print_ast_or_exit(parse_file(&codemap, &i, dialect), &codemap);
        } else {
            maybe_print_or_exit(eval_file(
                &i,
                dialect,
                &mut global.child(&i),
                global.clone(),
            ));
        }
    }
    if opt.repl || (free_args_empty && command.is_none()) {
        println!("Welcome to Starlark REPL, press Ctrl+D to exit.");
        repl(&global, dialect, ast);
    }
    if let Some(command) = command {
        let path = "[command flag]";
        if ast {
            let codemap = Arc::new(Mutex::new(CodeMap::new()));
            maybe_print_ast_or_exit(parse(&codemap, path, &command, dialect), &codemap);
        } else {
            maybe_print_or_exit(eval(
                "[command flag]",
                &command,
                dialect,
                &mut global.child("[command flag]"),
                global.clone(),
            ));
        }
    }
}

fn maybe_print_ast_or_exit(
    result: Result<AstStatement, Diagnostic>,
    codemap: &Arc<Mutex<CodeMap>>,
) {
    match result {
        Ok(ast) => {
            println!("{:#?}", ast);
        }
        Err(diagnostic) => {
            Emitter::stderr(ColorConfig::Auto, Some(&*codemap.lock().unwrap())).emit(&[diagnostic]);
            exit(EXIT_CODE_FAILURE);
        }
    }
}

fn maybe_print_or_exit(result: Result<Option<Value>, EvalError>) {
    match result {
        Ok(Some(value)) => println!("{}", value.to_repr()),
        Err(err) => {
            err.write_to_stderr();
            exit(EXIT_CODE_FAILURE);
        }
        Ok(None) => {}
    }
}
