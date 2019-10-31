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

//! The values module define a trait `TypedValue` that defines the attribute of
//! any value in Starlark and a few macro to help implementing this trait.
//! The `Value` struct defines the actual structure holding a TypedValue. It is mostly used to
//! enable mutable and Rc behavior over a TypedValue.
//! This modules also defines this traits for the basic immutable values: int, bool and NoneType.
//! Sub-modules implement other common types of all Starlark dialect.
//!
//! __Note__: we use _sequence_, _iterable_ and _indexable_ according to the
//! definition in the [Starlark specification](
//! https://github.com/google/skylark/blob/a0e5de7e63b47e716cca7226662a4c95d47bf873/doc/spec.md#sequence-types).
//! We also use the term _container_ for denoting any of those type that can hold several values.
//!
//!
//! # Defining a new type
//!
//! Defining a new Starlark type can be done by implenting the [`TypedValue`](crate::values::TypedValue)
//! trait. All method of that trait are operation needed by Starlark interpreter to understand the
//! type. Most of `TypedValue` methods are optional with default implementations returning error.
//!
//! For example the `NoneType` trait implementation is the following:
//!
//! ```rust
//! # use starlark::values::{TypedValue, Value, Immutable};
//! # use starlark::values::error::ValueError;
//! # use std::cmp::Ordering;
//! # use std::iter;
//!
//! /// Define the NoneType type
//! pub enum NoneType {
//!     None
//! }
//!
//! impl TypedValue for NoneType {
//!     type Holder = Immutable<Self>;
//!     const TYPE: &'static str = "NoneType";
//!
//!     fn compare(&self, _other: &NoneType) -> Result<Ordering, ValueError> {
//!         Ok(Ordering::Equal)
//!     }
//!     fn equals(&self, _other: &NoneType) -> Result<bool, ValueError> {
//!         Ok(true)
//!     }
//!     fn values_for_descendant_check_and_freeze<'a>(&'a self) -> Box<Iterator<Item=Value> + 'a> {
//!         Box::new(iter::empty())
//!     }
//!     fn to_repr(&self) -> String {
//!         "None".to_owned()
//!     }
//!     fn to_bool(&self) -> bool {
//!         false
//!     }
//!     // just took the result of hash(None) in macos python 2.7.10 interpreter.
//!     fn get_hash(&self) -> Result<u64, ValueError> {
//!         Ok(9_223_380_832_852_120_682)
//!     }
//! }
//! ```
//!
//! In addition to the `TypedValue` trait, it is recommended to implement the `From` trait
//! for all type that can convert to the added type but parameterized it with the `Into<Value>`
//! type. For example the unary tuple `From` trait is defined as followed:
//!
//! ```rust,ignore
//! impl<T: Into<Value>> From<(T,)> for Tuple {
//!     fn from(a: (T,)) -> Tuple {
//!         Tuple { content: vec![a.0.into()] }
//!     }
//! }
//! ```
use crate::environment::TypeValues;

use crate::environment::LocalEnvironment;
use crate::eval::call_stack;
use crate::eval::call_stack::CallStack;
use crate::values::error::ValueError;
use crate::values::function::FunctionInvoker;
use crate::values::iter::{FakeTypedIterable, RefIterable, TypedIterable};
use codemap_diagnostic::Level;
use std::any::Any;
use std::borrow::BorrowMut;
use std::borrow::Cow;
use std::cell::{RefCell, RefMut};
use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt;
use std::marker;
use std::rc::Rc;
use std::sync::Arc;

pub use crate::eval::EvalResult;
pub use mutability::*;

pub use crate::small_map::SmallMap;

impl SmallHash for Value {
    fn get_small_hash(&self) -> u64 {
        self.val_ref().get_hash().unwrap()
    }
}

impl SmallHash for FrozenValue {
    fn get_small_hash(&self) -> u64 {
        self.val_ref()
            .get_hash()
            .expect(&format!("couldn't hash {:?}", self))
    }
}

pub use crate::small_map::SmallHash;

/// ValueInner wraps the actual value or a memory pointer
/// to the actual value for complex type.

#[derive(Clone)]
enum FrozenInner {
    None(NoneType),
    Bool(bool),
    Int(i64),
    Object(Arc<dyn ImmutableValue>),
}

#[derive(Clone)]
enum LocalInner {
    Immutable(FrozenValue),
    Pseudo(Rc<dyn MutableValue>),
    Mutable(Rc<dyn Mutable>),
}

impl LocalInner {
    pub fn freeze(&self) -> Result<FrozenValue, ValueError> {
        match self {
            LocalInner::Immutable(v) => Ok(v.clone()),
            LocalInner::Mutable(v) => v.freeze(),
            LocalInner::Pseudo(v) => v.freeze(),
        }
    }

    pub fn freeze_for_iteration(&self) -> Result<(), ValueError> {
        match self {
            LocalInner::Mutable(v) => v.freeze_for_iteration(),
            _ => Ok(()),
        }
    }

    pub fn unfreeze_for_iteration(&self) -> Result<(), ValueError> {
        match self {
            LocalInner::Mutable(v) => v.unfreeze_for_iteration(),
            _ => Ok(()),
        }
    }

    pub fn shared(&self) -> Value {
        match self {
            LocalInner::Immutable(r) => r.shared(),
            _ => panic!(),
        }
    }
}

#[derive(Clone)]
pub struct FrozenValue(FrozenInner);

impl FrozenValue {
    pub fn shared(&self) -> Value {
        match &self.0 {
            FrozenInner::Object(o) => {
                if o.naturally_mutable() {
                    Value(LocalInner::Mutable(Rc::new(MutableCell::new_shared(o.clone()))))
                } else {
                    self.clone().into()
                }
            }
            _ => self.clone().into(),
        }
    }

    fn imm_ref(&self) -> &dyn TypedValue {
        match &self.0 {
            FrozenInner::None(v) => (v),
            FrozenInner::Bool(b) => (b),
            FrozenInner::Int(i) => (i),
            FrozenInner::Object(o) => (o.as_typed_value()),
        }
    }

    pub fn make_bool(v: bool) -> FrozenValue {
        FrozenValue(FrozenInner::Bool(v))
    }

    pub fn make_int(i: i64) -> FrozenValue {
        FrozenValue(FrozenInner::Int(i))
    }

    pub fn make_none() -> FrozenValue {
        FrozenValue(FrozenInner::None(NoneType::None))
    }

    pub fn make_immutable<T: ImmutableValue>(val: T) -> FrozenValue {
        FrozenValue(FrozenInner::Object(Arc::new(val)))
    }
}

impl ValueLike for FrozenValue {
    fn val_ref(&self) -> VRef<dyn TypedValue> {
        VRef::Ptr(self.imm_ref())
    }

    fn clone_value(&self) -> Value {
        self.clone().into()
    }
}

impl fmt::Display for FrozenValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        let v: Value = self.clone().into();
        write!(f, "{}", v.to_str())
    }
}

impl PartialEq for FrozenValue {
    fn eq(&self, other: &FrozenValue) -> bool {
        let v: Value = self.clone().into();
        let other: Value = other.clone().into();
        v.equals(&other) == Ok(true)
    }
}
impl Eq for FrozenValue {}

pub trait Binder {
    fn get(&mut self, name: &str) -> Result<Option<Value>, ValueError>;
}

pub struct ThrowingBinder {}

impl Binder for ThrowingBinder {
    fn get(&mut self, name: &str) -> Result<Option<Value>, ValueError> {
        panic!()
    }
}

/// A value in Starlark.
///
/// This is a wrapper around a [TypedValue] which is cheap to clone and safe to pass around.
#[derive(Clone)]
pub struct Value(LocalInner);

impl From<FrozenValue> for Value {
    fn from(frozen: FrozenValue) -> Self {
        Self(LocalInner::Immutable(frozen))
    }
}

pub type LocalValue = Value;

pub type ValueResult = Result<Value, ValueError>;

trait ValueUtils {
    fn new_value(self) -> Value;
}

impl Value {
    pub fn as_frozen(&self) -> FrozenValue {
        match &self.0 {
            LocalInner::Immutable(frozen) => frozen.clone(),
            _ => panic!("not frozen"),
        }
    }

    pub fn new<T: ImmutableValue>(t: T) -> Value {
        FrozenValue::make_immutable(t).into()
    }

    pub fn new_mutable<T: MutableValue>(t: T) -> Value {
        Value::make_mutable(t)
    }

    pub fn from_frozen(v: FrozenValue) -> Value {
        v.into()
    }

    pub fn make_pseudo<T: MutableValue>(val: T) -> Value {
        assert!(val.naturally_mutable());
        Value(LocalInner::Pseudo(Rc::new(val)))
    }

    pub fn make_mutable<T: MutableValue>(val: T) -> Value {
        assert!(val.naturally_mutable());
        let holder = MutableCell::new(val);
        Value(LocalInner::Mutable(Rc::new(holder)))
    }

    pub fn shared(&self) -> Value {
        self.0.shared()
    }

    fn val_mut(&mut self) -> Result<VRefMut<dyn MutableValue>, ValueError> {
        match &self.0 {
            LocalInner::Immutable(_inner) => Err(ValueError::CannotMutateImmutableValue),
            LocalInner::Mutable(inner) => inner.val_mut(),
            _ => panic!(),
        }
    }

    pub fn imm_ref(&self) -> &dyn TypedValue {
        match &self.0 {
            LocalInner::Immutable(inner) => inner.imm_ref(),
            LocalInner::Pseudo(inner) => inner.as_typed_value(),
            LocalInner::Mutable(inner) => inner.imm_ref(),
        }
    }

    /// Clone for inserting into the other container, using weak reference if we do a
    /// recursive insertion.
    pub fn clone_for_container<T: TypedValue>(&self, container: &T) -> Result<Value, ValueError> {
        if self.is_descendant(DataPtr::from(container)) {
            Err(ValueError::UnsupportedRecursiveDataStructure)
        } else {
            Ok(self.clone())
        }
    }

    pub fn clone_for_container_value(&self, other: &Value) -> Result<Value, ValueError> {
        if self.is_descendant_value(other) {
            Err(ValueError::UnsupportedRecursiveDataStructure)
        } else {
            Ok(self.clone())
        }
    }

    /// Determine if the value pointed by other is a descendant of self
    pub fn is_descendant_value(&self, other: &Value) -> bool {
        false
        // self.val_ref().is_descendant(other.data_ptr())
    }

    /// Function id used to detect recursion.
    pub fn function_id(&self) -> FunctionId {
        FunctionId(self.data_ptr())
    }
}

impl ValueLike for Value {
    fn val_ref(&self) -> VRef<dyn TypedValue> {
        match &self.0 {
            LocalInner::Immutable(inner) => inner.val_ref(),
            LocalInner::Pseudo(inner) => VRef::Ptr(inner.as_typed_value()),
            LocalInner::Mutable(inner) => inner.val_ref(),
        }
    }

    fn as_any_mut(&mut self) -> Result<Option<VRefMut<'_, dyn Any>>, ValueError> {
        match self.val_mut() {
            Result::Ok(vref) => {
                let dynany: VRefMut<'_, dyn Any> = VRefMut::map(vref, |v| v.as_dyn_any_mut());
                Ok(Some(dynany))
            }
            Result::Err(e) => Err(e),
        }
    }

    fn clone_value(&self) -> Value {
        self.clone()
    }
}

/// Pointer to data, used for cycle checks.
#[derive(Copy, Clone, Debug, Eq)]
pub struct DataPtr(*const ());

impl<T: TypedValue> From<*const T> for DataPtr {
    fn from(p: *const T) -> Self {
        DataPtr(p as *const ())
    }
}

impl<T: TypedValue> From<&'_ T> for DataPtr {
    fn from(p: &T) -> Self {
        DataPtr::from(p as *const T)
    }
}

impl From<Value> for DataPtr {
    fn from(v: Value) -> Self {
        v.data_ptr()
    }
}

impl PartialEq for DataPtr {
    fn eq(&self, other: &DataPtr) -> bool {
        self.0 == other.0
    }
}

/// Function identity to detect recursion.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FunctionId(pub DataPtr);

pub trait MutableValue: TypedValue {
    fn freeze(&self) -> Result<FrozenValue, ValueError>;

    fn as_dyn_any_mut(&mut self) -> &mut dyn Any;
}

pub trait ImmutableValue: TypedValue + Send + Sync {
    fn as_owned_value(&self) -> Box<dyn MutableValue> {
        assert!(!self.naturally_mutable());
        unimplemented!()
    }
}

impl<T: TypedValue> AsTypedValue for T {
    fn as_typed_value(&self) -> &dyn TypedValue {
        self
    }
}

macro_rules! unsupported {
    ($v:expr, $op:expr, $o:expr) => {
        ValueError::OperationNotSupported {
            op: $op.to_owned(),
            left: $v.get_type().to_owned(),
            // TODO
            right: None,
        }
    };
}

pub trait AsTypedValue {
    fn as_typed_value(&self) -> &dyn TypedValue;
}

/// A trait for a value with a type that all variable container
/// will implement.
pub trait TypedValue: 'static + AsTypedValue {
    /// Return a string describing the type of self, as returned by the type() function.
    fn get_type(&self) -> &'static str;

    fn as_dyn_any(&self) -> &dyn Any;

    fn naturally_mutable(&self) -> bool {
        false
    }

    /// Return a list of values to be used in freeze or descendant check operations.
    ///
    /// Objects which do not contain references to other Starlark objects typically
    /// implement it by returning an empty iterator:
    ///
    /// ```
    /// # use starlark::values::*;
    /// # use std::iter;
    /// # struct MyType;
    ///
    /// # impl TypedValue for MyType {
    /// #    type Holder = Immutable<MyType>;
    /// #    const TYPE: &'static str = "MyType";
    /// #
    /// fn values_for_descendant_check_and_freeze<'a>(&'a self) -> Box<Iterator<Item=Value> + 'a> {
    ///     Box::new(iter::empty())
    /// }
    /// #
    /// # }
    /// ```

    /// Return function id to detect recursion.
    ///
    /// If `None` is returned, object id is used.
    fn function_id(&self) -> Option<FunctionId> {
        None
    }

    fn to_str_slow(&self) -> String {
        let mut s = String::new();
        self.collect_str(&mut s);
        s
    }

    fn to_repr_slow(&self) -> String {
        let mut s = String::new();
        self.collect_repr(&mut s);
        s
    }

    /// Return a string describing of self, as returned by the str() function.
    fn collect_str(&self, collector: &mut String) {
        self.collect_repr(collector);
    }

    /// Return a string representation of self, as returned by the repr() function.
    fn collect_repr(&self, collector: &mut String) {
        collector.push('<');
        collector.push_str(self.get_type());
        collector.push('>');
    }

    fn to_json(&self) -> String {
        panic!("unsupported for type {}", self.get_type())
    }

    fn find_in<'a>(&'_ self, map: &'a SmallMap<String, Value>) -> Option<&'a Value> {
        panic!("unsupported as key for type {}", self.get_type())
    }

    /// Convert self to a Boolean truth value, as returned by the bool() function.
    fn to_bool(&self) -> bool {
        // Return `true` by default, because this is default when implementing
        // custom types in Python: https://docs.python.org/release/2.5.2/lib/truth.html
        true
    }

    /// Convert self to a integer value, as returned by the int() function if the type is numeric
    /// (not for string).
    fn to_int(&self) -> Result<i64, ValueError> {
        Err(unsupported!(self, "int()", None))
    }

    /// Return a hash code for self, as returned by the hash() function, or
    /// OperationNotSupported if there is no hash for this value (e.g. list).
    fn get_hash(&self) -> Result<u64, ValueError> {
        Err(ValueError::NotHashableValue)
    }

    /// Compare `self` with `other` for equality.
    ///
    /// `other` parameter is of type `Self` so it is safe to downcast it.
    ///
    /// Default implementation does pointer (id) comparison.
    ///
    /// Note: `==` in Starlark should work for arbitary objects,
    /// so implementation should avoid returning errors except for
    //  unrecoverable runtime errors.
    fn equals(&self, other: &Value) -> Result<bool, ValueError> {
        Err(unsupported!(self, "==", Some(other)))
    }

    /// Compare `self` with `other`.
    ///
    /// This method returns a result of type [`Ordering`].
    ///
    /// `other` parameter is of type `Self` so it is safe to downcast it.
    ///
    /// Default implementation returns error.
    ///
    /// __Note__: This does not use the [`PartialOrd`] trait as
    ///       the trait needs to know the actual type of the value we compare.
    fn compare(&self, other: &Value) -> Result<Ordering, ValueError> {
        Err(unsupported!(self, "compare", Some(other)))
    }

    /// Perform a call on the object, only meaningfull for function object.
    ///
    /// For instance, if this object is a callable (i.e. a function or a method) that adds 2
    /// integers then `self.call(vec![Value::new(1), Value::new(2)], HashMap::new(),
    /// None, None)` would return `Ok(Value::new(3))`.
    ///
    /// # Parameters
    ///
    /// * call_stack: the calling stack, to detect recursion
    /// * type_values: environment used to resolve type fields.
    /// * positional: the list of arguments passed positionally.
    /// * named: the list of argument that were named.
    /// * args: if provided, the `*args` argument.
    /// * kwargs: if provided, the `**kwargs` argument.
    fn new_invoker(&self) -> Result<FunctionInvoker, ValueError> {
        Err(unsupported!(self, "call()", None))
    }

    /// Perform an array or dictionary indirection.
    ///
    /// This returns the result of `a[index]` if `a` is indexable.
    fn at(&self, index: Value) -> ValueResult {
        Err(unsupported!(self, "[]", Some(index)))
    }

    /// Set the value at `index` with `new_value`.
    ///
    /// This method should error with `ValueError::CannotMutateImmutableValue` if the value was
    /// frozen (but with `ValueError::OperationNotSupported` if the operation is not supported
    /// on this value, even if the value is immutable, e.g. for numbers).
    fn set_at(&mut self, index: Value, _new_value: Value) -> Result<(), ValueError> {
        Err(unsupported!(self, "[]=", Some(index)))
    }

    /// Extract a slice of the underlying object if the object is indexable. The result will be
    /// object between `start` and `stop` (both of them are added length() if negative and then
    /// clamped between 0 and length()). `stride` indicates the direction.
    ///
    /// # Parameters
    ///
    /// * start: the start of the slice.
    /// * stop: the end of the slice.
    /// * stride: the direction of slice,
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use starlark::values::*;
    /// # use starlark::values::string;
    /// # assert!(
    /// // Remove the first element: "abc"[1:] == "bc".
    /// Value::from("abc").slice(Some(Value::from(1)), None, None).unwrap() == Value::from("bc")
    /// # );
    /// # assert!(
    /// // Remove the last element: "abc"[:-1] == "ab".
    /// Value::from("abc").slice(None, Some(Value::from(-1)), None).unwrap()
    ///    == Value::from("ab")
    /// # );
    /// # assert!(
    /// // Remove the first and the last element: "abc"[1:-1] == "b".
    /// Value::from("abc").slice(Some(Value::from(1)), Some(Value::from(-1)), None).unwrap()
    ///    == Value::from("b")
    /// # );
    /// # assert!(
    /// // Select one element out of 2, skipping the first: "banana"[1::2] == "aaa".
    /// Value::from("banana").slice(Some(Value::from(1)), None, Some(Value::from(2))).unwrap()
    ///    == Value::from("aaa")
    /// # );
    /// # assert!(
    /// // Select one element out of 2 in reverse order, starting at index 4:
    /// //   "banana"[4::-2] = "nnb"
    /// Value::from("banana").slice(Some(Value::from(4)), None, Some(Value::from(-2))).unwrap()
    ///    == Value::from("nnb")
    /// # );
    /// ```
    fn slice(
        &self,
        _start: Option<Value>,
        _stop: Option<Value>,
        _stride: Option<Value>,
    ) -> ValueResult {
        Err(unsupported!(self, "[::]", None))
    }

    /// Returns an iterable over the value of this container if this value hold an iterable
    /// container.
    fn iter(&self) -> Result<&dyn TypedIterable, ValueError> {
        Err(unsupported!(self, "(iter)", None))
    }

    /// Returns the length of the value, if this value is a sequence.
    fn length(&self) -> Result<i64, ValueError> {
        Err(unsupported!(self, "len()", None))
    }

    /// Get an attribute for the current value as would be returned by dotted expression (i.e.
    /// `a.attribute`).
    ///
    /// __Note__: this does not handle native methods which are handled through universe.
    fn get_attr(&self, attribute: &str) -> ValueResult {
        Err(unsupported!(self, ".{}", None))
    }

    /// Return true if an attribute of name `attribute` exists for the current value.
    ///
    /// __Note__: this does not handle native methods which are handled through universe.
    fn has_attr(&self, _attribute: &str) -> Result<bool, ValueError> {
        Err(unsupported!(self, "has_attr()", None))
    }

    /// Set the attribute named `attribute` of the current value to `new_value` (e.g.
    /// `a.attribute = new_value`).
    ///
    /// This method should error with `ValueError::CannotMutateImmutableValue` if the value was
    /// frozen or the attribute is immutable (but with `ValueError::OperationNotSupported`
    /// if the operation is not supported on this value, even if the self is immutable,
    /// e.g. for numbers).
    fn set_attr(&mut self, attribute: &str, _new_value: Value) -> Result<(), ValueError> {
        Err(unsupported!(self, ".{}=", None))
    }

    /// Return a vector of string listing all attribute of the current value, excluding native
    /// methods.
    fn dir_attr(&self) -> Result<Vec<String>, ValueError> {
        Err(unsupported!(self, "dir()", None))
    }

    /// Tell wether `other` is in the current value, if it is a container.
    ///
    /// Non container value should return an error `ValueError::OperationNotSupported`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use starlark::values::*;
    /// # use starlark::values::string;
    /// // "a" in "abc" == True
    /// assert!(Value::from("abc").is_in(&Value::from("a")).unwrap().to_bool());
    /// // "b" in "abc" == True
    /// assert!(Value::from("abc").is_in(&Value::from("b")).unwrap().to_bool());
    /// // "z" in "abc" == False
    /// assert!(!Value::from("abc").is_in(&Value::from("z")).unwrap().to_bool());
    /// ```
    fn is_in(&self, other: &Value) -> Result<bool, ValueError> {
        Err(unsupported!(other, "in", Some(self)))
    }

    /// Apply the `+` unary operator to the current value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[macro_use] extern crate starlark;
    /// # use starlark::values::*;
    /// # fn main() {
    /// assert_eq!(1, int_op!(1.plus()));  // 1.plus() = +1 = 1
    /// # }
    /// ```
    fn plus(&self) -> Result<Value, ValueError> {
        Err(unsupported!(self, "+", None))
    }

    /// Apply the `-` unary operator to the current value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[macro_use] extern crate starlark;
    /// # use starlark::values::*;
    /// # fn main() {
    /// assert_eq!(-1, int_op!(1.minus()));  // 1.minus() = -1
    /// # }
    /// ```
    fn minus(&self) -> Result<Value, ValueError> {
        Err(unsupported!(self, "-", None))
    }

    /// Add `other` to the current value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[macro_use] extern crate starlark;
    /// # use starlark::values::*;
    /// # fn main() {
    /// assert_eq!(3, int_op!(1.add(2)));  // 1.add(2) = 1 + 2 = 3
    /// # }
    /// ```
    fn add(&self, other: &Value) -> Result<Value, ValueError> {
        Err(unsupported!(self, "+", Some(other)))
    }

    fn add_assign(&mut self, other: &Value) -> Result<(), ValueError> {
        Err(unsupported!(self, "+=", Some(other)))
    }

    /// Substract `other` from the current value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[macro_use] extern crate starlark;
    /// # use starlark::values::*;
    /// # fn main() {
    /// assert_eq!(-1, int_op!(1.sub(2)));  // 1.sub(2) = 1 - 2 = -1
    /// # }
    /// ```
    fn sub(&self, other: &Value) -> Result<Value, ValueError> {
        Err(unsupported!(self, "-", Some(other)))
    }

    /// Multiply the current value with `other`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[macro_use] extern crate starlark;
    /// # use starlark::values::*;
    /// # fn main() {
    /// assert_eq!(6, int_op!(2.mul(3)));  // 2.mul(3) = 2 * 3 = 6
    /// # }
    /// ```
    fn mul(&self, other: Value) -> ValueResult {
        Err(unsupported!(self, "*", Some(other)))
    }

    /// Apply the percent operator between the current value and `other`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[macro_use] extern crate starlark;
    /// # use starlark::values::*;
    /// # use starlark::values::string;
    /// # fn main() {
    /// // Remainder of the floored division: 5.percent(3) = 5 % 3 = 2
    /// assert_eq!(2, int_op!(5.percent(3)));
    /// // String formatting: "a {} c" % 3 == "a 3 c"
    /// assert_eq!(Value::from("a 3 c"), Value::from("a %s c").percent(Value::from(3)).unwrap());
    /// # }
    /// ```
    fn percent(&self, other: Value) -> ValueResult {
        Err(unsupported!(self, "%", Some(other)))
    }

    /// Divide the current value with `other`.  division.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[macro_use] extern crate starlark;
    /// # use starlark::values::*;
    /// # fn main() {
    /// assert_eq!(3, int_op!(7.div(2)));  // 7.div(2) = 7 / 2 = 3
    /// # }
    /// ```
    fn div(&self, other: Value) -> ValueResult {
        Err(unsupported!(self, "/", Some(other)))
    }

    /// Floor division between the current value and `other`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[macro_use] extern crate starlark;
    /// # use starlark::values::*;
    /// # fn main() {
    /// assert_eq!(3, int_op!(7.floor_div(2)));  // 7.div(2) = 7 / 2 = 3
    /// # }
    /// ```
    fn floor_div(&self, other: Value) -> ValueResult {
        Err(unsupported!(self, "//", Some(other)))
    }

    /// Apply the operator pipe to the current value and `other`.
    ///
    /// This is usually the union on set.
    fn pipe(&self, other: Value) -> ValueResult {
        Err(unsupported!(self, "|", Some(other)))
    }
}

impl fmt::Debug for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Value[{}]({})", self.get_type(), self.to_repr())
    }
}

impl fmt::Debug for FrozenValue {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let val: Value = self.clone().into();
        write!(f, "FrozenValue[{}]({})", val.get_type(), val.to_repr())
    }
}

pub trait DowncastValue: ValueLike {
    /// Get a reference to underlying data or `None`
    /// if contained object has different type than requested.
    ///
    /// This function panics if the `Value` is borrowed mutably.
    fn downcast_ref<T: TypedValue>(&self) -> Option<RefOrRef<'_, T>> {
        let any = self.as_any_ref();
        if any.is::<T>() {
            Some(RefOrRef::map(any, |any| any.downcast_ref::<T>().unwrap()))
        } else {
            None
        }
    }
}

impl<T: ValueLike> DowncastValue for T {}

impl indexmap::Equivalent<Value> for FrozenValue {
    fn equivalent(&self, key: &Value) -> bool {
        self.equals(key).unwrap()
    }
}

impl indexmap::Equivalent<FrozenValue> for Value {
    fn equivalent(&self, key: &FrozenValue) -> bool {
        key.equals(self).unwrap()
    }
}

pub trait ValueLike:
    Eq + SmallHash + indexmap::Equivalent<Value> + indexmap::Equivalent<FrozenValue>
{
    fn clone_value(&self) -> Value;

    fn val_ref(&self) -> VRef<dyn TypedValue>;

    fn as_any_ref(&self) -> VRef<'_, dyn Any> {
        VRef::map(self.val_ref(), |e| e.as_dyn_any())
    }

    fn as_any_mut(&mut self) -> Result<Option<VRefMut<'_, dyn Any>>, ValueError> {
        unimplemented!()
    }

    fn data_ptr(&self) -> DataPtr {
        let ptr: *const dyn TypedValue = &*self.val_ref();
        DataPtr(ptr as *const ())
    }

    fn get_hash(&self) -> Result<u64, ValueError> {
        self.val_ref().get_hash()
    }

    fn collect_str(&self, s: &mut String) {
        self.val_ref().collect_str(s);
    }

    fn collect_repr(&self, s: &mut String) {
        self.val_ref().collect_repr(s);
    }
    fn to_json(&self) -> String {
        self.val_ref().to_json()
    }
    fn get_type(&self) -> &'static str {
        self.val_ref().get_type()
    }
    fn to_bool(&self) -> bool {
        self.val_ref().to_bool()
    }
    fn to_int(&self) -> Result<i64, ValueError> {
        self.val_ref().to_int()
    }
    fn at(&self, index: Value) -> ValueResult {
        self.val_ref().at(index)
    }

    fn equals(&self, other: &Value) -> Result<bool, ValueError> {
        match self.val_ref().equals(other) {
            Ok(v) => Ok(v),
            Err(e) => {
                let self_ptr = self.data_ptr();
                let other_ptr = other.data_ptr();
                Ok(self_ptr == other_ptr)
            }
        }
    }

    fn compare(&self, other: &Value) -> Result<Ordering, ValueError> {
        self.val_ref().compare(other)
    }

    fn slice(
        &self,
        start: Option<Value>,
        stop: Option<Value>,
        stride: Option<Value>,
    ) -> ValueResult {
        self.val_ref().slice(start, stop, stride)
    }

    fn length(&self) -> Result<i64, ValueError> {
        self.val_ref().length()
    }

    fn get_attr(&self, attribute: &str) -> ValueResult {
        self.val_ref().get_attr(attribute)
    }

    fn has_attr(&self, attribute: &str) -> Result<bool, ValueError> {
        self.val_ref().has_attr(attribute)
    }

    fn dir_attr(&self) -> Result<Vec<String>, ValueError> {
        self.val_ref().dir_attr()
    }

    fn is_in(&self, other: &Value) -> Result<bool, ValueError> {
        self.val_ref().is_in(other)
    }

    fn plus(&self) -> ValueResult {
        self.val_ref().plus()
    }

    fn minus(&self) -> ValueResult {
        self.val_ref().minus()
    }

    fn add(&self, other: Value) -> ValueResult {
        self.val_ref().add(&other)
    }

    fn sub(&self, other: Value) -> ValueResult {
        self.val_ref().sub(&other)
    }

    fn mul(&self, other: Value) -> ValueResult {
        self.val_ref().mul(other)
    }

    fn percent(&self, other: Value) -> ValueResult {
        self.val_ref().percent(other)
    }

    fn div(&self, other: Value) -> ValueResult {
        self.val_ref().div(other)
    }

    fn floor_div(&self, other: Value) -> ValueResult {
        self.val_ref().floor_div(other)
    }

    fn pipe(&self, other: Value) -> ValueResult {
        self.val_ref().pipe(other)
    }
}

impl Value {
    pub fn freeze(&self) -> Result<FrozenValue, ValueError> {
        self.0.freeze()
    }
    pub fn freeze_for_iteration(&mut self) -> Result<(), ValueError> {
        self.0.freeze_for_iteration()
    }
    pub fn unfreeze_for_iteration(&mut self) -> Result<(), ValueError> {
        self.0.unfreeze_for_iteration()
    }
    pub fn to_str(&self) -> String {
        let mut s = String::new();
        self.collect_str(&mut s);
        s
    }

    pub fn set_attr(&mut self, attribute: &str, new_value: Value) -> Result<(), ValueError> {
        self.val_mut()?.set_attr(attribute, new_value)
    }

    pub fn to_repr(&self) -> String {
        let mut s = String::new();
        self.collect_repr(&mut s);
        s
    }

    pub fn is_descendant(&self, other: DataPtr) -> bool {
        false
        // self.val_ref().is_descendant(other)
    }

    pub fn new_invoker(&self) -> Result<FunctionInvoker, ValueError> {
        self.imm_ref().new_invoker()
    }

    pub fn set_at(&mut self, index: Value, new_value: Value) -> Result<(), ValueError> {
        self.val_mut()?.set_at(index, new_value)
    }

    pub fn iter<'a>(&'a self) -> Result<RefIterable<'a>, ValueError> {
        Ok(RefIterable::new(VRef::map_err(self.val_ref(), |e| {
            e.iter().unwrap()
        })))
    }

    pub fn add_assign(&mut self, other: Value) -> Result<Option<Value>, ValueError> {
        match self.val_mut() {
            Ok(mut v) => {
                v.add_assign(&other)?;
                return Ok(None);
            }
            Err(..) => {}
        }

        Ok(Some(self.val_ref().add(&other)?))
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}", self.to_str())
    }
}

impl PartialEq for Value {
    fn eq(&self, other: &Value) -> bool {
        self.equals(other) == Ok(true)
    }
}
impl Eq for Value {}

impl Value {
    // To be calleds by convert_slice_indices only
    fn convert_index_aux(
        len: i64,
        v1: Option<Value>,
        default: i64,
        min: i64,
        max: i64,
    ) -> Result<i64, ValueError> {
        if let Some(v) = v1 {
            if v.get_type() == "NoneType" {
                Ok(default)
            } else {
                match v.to_int() {
                    Ok(x) => {
                        let i = if x < 0 { len + x } else { x };
                        if i < min {
                            Ok(min)
                        } else if i > max {
                            Ok(max)
                        } else {
                            Ok(i)
                        }
                    }
                    Err(..) => Err(ValueError::IncorrectParameterType),
                }
            }
        } else {
            Ok(default)
        }
    }

    /// Macro to parse the index for at/set_at methods.
    ///
    /// Return an `i64` from self corresponding to the index recenterd between 0 and len.
    /// Raise the correct errors if the value is not numeric or the index is out of bound.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use starlark::values::*;
    /// # assert!(
    /// Value::new(6).convert_index(7).unwrap() == 6
    /// # );
    /// # assert!(
    /// Value::new(-1).convert_index(7).unwrap() == 6
    /// # );
    /// ```
    ///
    /// The following examples would return an error
    /// ```rust
    /// # use starlark::values::*;
    /// # use starlark::values::error::*;
    /// # use starlark::values::string;
    /// # assert!(
    /// Value::from("a").convert_index(7) == Err(ValueError::IncorrectParameterType)
    /// # );
    /// # assert!(
    /// Value::new(8).convert_index(7) == Err(ValueError::IndexOutOfBound(8))   // 8 > 7 = len
    /// # );
    /// # assert!(
    /// Value::new(-8).convert_index(7) == Err(ValueError::IndexOutOfBound(-1)) // -8 + 7 = -1 < 0
    /// # );
    /// ```
    pub fn convert_index(&self, len: i64) -> Result<i64, ValueError> {
        match self.to_int() {
            Ok(x) => {
                let i = if x < 0 {
                    len.checked_add(x).ok_or(ValueError::IntegerOverflow)?
                } else {
                    x
                };
                if i < 0 || i >= len {
                    Err(ValueError::IndexOutOfBound(i))
                } else {
                    Ok(i)
                }
            }
            Err(..) => Err(ValueError::IncorrectParameterType),
        }
    }
}

impl Value {
    /// Parse indices for slicing.
    ///
    /// Takes the object length and 3 optional values and returns `(i64, i64, i64)`
    /// with those index correctly converted in range of length.
    /// Return the correct errors if the values are not numeric or the stride is 0.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use starlark::values::*;
    /// let six      = Some(Value::new(6));
    /// let minusone = Some(Value::new(-1));
    /// let ten      = Some(Value::new(10));
    ///
    /// # assert!(
    /// Value::convert_slice_indices(7, six, None, None).unwrap() == (6, 7, 1)
    /// # );
    /// # assert!(
    /// Value::convert_slice_indices(7, minusone.clone(), None, minusone.clone()).unwrap()
    ///        == (6, -1, -1)
    /// # );
    /// # assert!(
    /// Value::convert_slice_indices(7, minusone, ten, None).unwrap() == (6, 7, 1)
    /// # );
    /// ```
    pub fn convert_slice_indices(
        len: i64,
        start: Option<Value>,
        stop: Option<Value>,
        stride: Option<Value>,
    ) -> Result<(i64, i64, i64), ValueError> {
        let stride = stride.unwrap_or_else(|| Value::new(1));
        let stride = if stride.get_type() == "NoneType" {
            Ok(1)
        } else {
            stride.to_int()
        };
        match stride {
            Ok(0) => Err(ValueError::IndexOutOfBound(0)),
            Ok(stride) => {
                let def_start = if stride < 0 { len - 1 } else { 0 };
                let def_end = if stride < 0 { -1 } else { len };
                let clamp = if stride < 0 { -1 } else { 0 };
                let start = Value::convert_index_aux(len, start, def_start, clamp, len + clamp);
                let stop = Value::convert_index_aux(len, stop, def_end, clamp, len + clamp);
                match (start, stop) {
                    (Ok(s1), Ok(s2)) => Ok((s1, s2, stride)),
                    (Err(x), ..) => Err(x),
                    (Ok(..), Err(x)) => Err(x),
                }
            }
            _ => Err(ValueError::IncorrectParameterType),
        }
    }
}

pub fn to_frozen_for_defaults<T: Into<Value>>(t: T) -> FrozenValue {
    let mut v: Value = t.into();
    v.freeze().unwrap()
}

impl Value {
    /// Get a mutable reference to underlying data or `None`
    /// if contained object has different type than requested.
    ///
    /// This function panics if the `Value` is borrowed.
    ///
    /// Error is returned if the value is frozen or frozen for iteration.
    pub fn downcast_mut<T: TypedValue>(&mut self) -> Result<Option<RefMut<'_, T>>, ValueError> {
        let any = match self.as_any_mut()? {
            Some(any) => any,
            None => return Ok(None),
        };

        Ok(if any.is::<T>() {
            Some(RefMut::map(any, |any| any.downcast_mut::<T>().unwrap()))
        } else {
            None
        })
    }
}

// Submodules
pub mod boolean;
pub mod dict;
pub mod error;
pub mod function;
pub mod hashed_value;
pub mod int;
pub mod iter;
pub mod list;
pub mod mutability;
pub mod none;
pub mod range;
pub mod string;
pub mod tuple;

use crate::values::mutability::RefOrRef;
use crate::values::none::NoneType;

#[cfg(test)]
mod tests {
    use super::*;
    use std::iter;

    #[test]
    fn test_convert_index() {
        assert_eq!(Ok(6), Value::new(6).convert_index(7));
        assert_eq!(Ok(6), Value::new(-1).convert_index(7));
        assert_eq!(
            Ok((6, 7, 1)),
            Value::convert_slice_indices(7, Some(Value::new(6)), None, None)
        );
        assert_eq!(
            Ok((6, -1, -1)),
            Value::convert_slice_indices(7, Some(Value::new(-1)), None, Some(Value::new(-1)))
        );
        assert_eq!(
            Ok((6, 7, 1)),
            Value::convert_slice_indices(7, Some(Value::new(-1)), Some(Value::new(10)), None)
        );
        // Errors
        assert_eq!(
            Err(ValueError::IncorrectParameterType),
            Value::from("a").convert_index(7)
        );
        assert_eq!(
            Err(ValueError::IndexOutOfBound(8)),
            Value::new(8).convert_index(7)
        );
        assert_eq!(
            Err(ValueError::IndexOutOfBound(-1)),
            Value::new(-8).convert_index(7)
        );
    }

    #[test]
    fn can_implement_compare() {
        /*
        #[derive(Debug, PartialEq, Eq, Ord, PartialOrd)]
        struct WrappedNumber(u64);

        /// Define the NoneType type
        impl TypedValue for WrappedNumber {
            fn collect_repr(&self, s: &mut String) {
                s.push_str(&self.0.to_string());
            }
            fn get_type(&self) -> &'static str {
                "wrappednum"
            }
            fn to_bool(&self) -> bool {
                false
            }
            fn get_hash(&self) -> Result<u64, ValueError> {
                Ok(self.0)
            }
            fn compare(&self, other: &Value) -> Result<std::cmp::Ordering, ValueError> {
                Ok(std::cmp::Ord::cmp(self, other))
            }

            fn values_for_descendant_check_and_freeze<'a>(
                &'a self,
            ) -> Box<dyn Iterator<Item = Value> + 'a> {
                Box::new(iter::empty())
            }
        }

        let one = Value::new(WrappedNumber(1));
        let another_one = Value::new(WrappedNumber(1));
        let two = Value::new(WrappedNumber(2));

        use std::cmp::Ordering::*;

        assert_eq!(one.compare(&one), Ok(Equal));
        assert_eq!(one.compare(&another_one), Ok(Equal));
        assert_eq!(one.compare(&two), Ok(Less));
        assert_eq!(two.compare(&one), Ok(Greater));
        */
    }

    #[test]
    fn compare_between_different_types() {
        assert!(Value::new(1).compare(&Value::new(false)).is_err());
    }
}
