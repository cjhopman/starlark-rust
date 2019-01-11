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

//! The syntax module that handle lexing and parsing

#[doc(hidden)]
pub mod errors;

#[cfg(test)]
#[macro_use]
mod testutil;

#[doc(hidden)]
pub mod ast;
pub mod dialect;
#[doc(hidden)]
pub mod lexer;

#[allow(clippy::all)]
mod grammar {
    include!(concat!(env!("OUT_DIR"), "/syntax/grammar.rs"));
}

// TODO(damienmg): there doesn't seem to have a way to reactivate default
// clippy warning / errors only for the tests...
#[cfg(test)]
mod grammar_tests {
    include!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/src/syntax/grammar.tests.rs"
    ));
}

#[doc(hidden)]
pub mod parser;
