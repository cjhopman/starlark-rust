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

//! Mutability-related utilities.

use crate::values::ValueError;
use std::cell::{BorrowError, BorrowMutError, Cell, Ref, RefCell, RefMut};
use std::fmt;
use std::rc::Rc;
use std::ops::Deref;

/// A helper enum for defining the level of mutability of an iterable.
#[derive(PartialEq, Eq, Hash, Debug, Copy, Clone)]
pub enum MutabilityState {
    Shared,
    Mutable,
    Frozen,
    FrozenForIteration(bool),
}

impl MutabilityState {
    /// Tests the mutability value and return the appropriate error
    ///
    /// This method is to be called simply `mutability.test()?` to return
    /// an error if the current container is no longer mutable.
    pub fn test(self) -> Result<(), ValueError> {
        match self {
            MutabilityState::Shared => Ok(()),
            MutabilityState::Mutable => Ok(()),
            MutabilityState::Frozen => Err(ValueError::CannotMutateFrozenValue),
            MutabilityState::FrozenForIteration(_) => Err(ValueError::MutationDuringIteration),
        }
    }
}

/// `std::cell::Ref<T>` or `&T`
pub enum RefOrRef<'a, T: ?Sized + 'a> {
    Ptr(&'a T),
    Borrowed(Ref<'a, T>),
}

impl<'a, T: ?Sized + 'a> Deref for RefOrRef<'a, T> {
    type Target = T;

    fn deref(&self) -> &T {
        match self {
            RefOrRef::Ptr(p) => p,
            RefOrRef::Borrowed(p) => p.deref(),
        }
    }
}

impl<'a, T: ?Sized + 'a> RefOrRef<'a, T> {
    pub fn map<U: ?Sized, F>(orig: RefOrRef<'a, T>, f: F) -> RefOrRef<'a, U>
    where
        F: FnOnce(&T) -> &U,
    {
        match orig {
            RefOrRef::Ptr(p) => RefOrRef::Ptr(f(p)),
            RefOrRef::Borrowed(p) => RefOrRef::Borrowed(Ref::map(p, f)),
        }
    }
}

/// Container for data which is either `RefCell` or immutable data.
pub trait ContentCell {
    type Content;

    const MUTABLE : bool;

    fn new(value: Self::Content) -> Self;
    fn borrow(&self) -> RefOrRef<'_, Self::Content>;
    fn try_borrow(&self) -> Result<RefOrRef<Self::Content>, BorrowError>;
    fn borrow_mut(&self) -> RefMut<'_, Self::Content>;
    fn try_borrow_mut(&self) -> Result<RefMut<'_, Self::Content>, ()>;
    fn shared(&self) -> Self;
    fn as_ptr(&self) -> *const Self::Content;

    fn test_mut(&self) -> Result<(), ValueError>;

    fn freeze(&self);
    fn freeze_for_iteration(&self);
    fn unfreeze_for_iteration(&self);
}

/// Container for immutable data
#[derive(Debug, Clone)]
pub struct ImmutableCell<T>(T);

pub trait CloneForCell {
    fn clone_for_cell(&self) -> Self;
}

#[derive(Debug, Clone)]
pub struct MutableCell<T : CloneForCell> {
    state: Cell<MutabilityState>,
    val : Rc<RefCell<T>>,
}

impl<T: CloneForCell> MutableCell<T> {
    pub fn ensure_owned(&self) {
        if let MutabilityState::Shared = self.state.get() {
            // println!("making owned");
            self.state.set(MutabilityState::Mutable);
            let mut bw = self.val.borrow_mut();
            let cl = bw.clone_for_cell();
            *bw = cl;
        }
    }
}

impl<T: CloneForCell> ContentCell for MutableCell<T> {
    type Content = T;

    const MUTABLE: bool = true;

    fn new(value: T) -> Self {
        Self {
            state: Cell::new(MutabilityState::Mutable),
            val: Rc::new(RefCell::new(value)),
        }
    }

    fn test_mut(&self) -> Result<(), ValueError> {
        self.state.get().test()
    }

    fn borrow(&self) -> RefOrRef<T> {
        RefOrRef::Borrowed(RefCell::borrow(&self.val))
    }

    fn try_borrow(&self) -> Result<RefOrRef<T>, BorrowError> {
        RefCell::try_borrow(&self.val).map(RefOrRef::Borrowed)
    }

    fn borrow_mut(&self) -> RefMut<Self::Content> {
        self.ensure_owned();
        RefCell::borrow_mut(&self.val)
    }

    fn try_borrow_mut(&self) -> Result<RefMut<Self::Content>, ()> {
        self.ensure_owned();
        RefCell::try_borrow_mut(&self.val).map_err(|e| ())
    }

    fn as_ptr(&self) -> *const T {
        RefCell::as_ptr(&self.val)
    }

    fn shared(&self) -> Self {
        match self.state.get() {
            MutabilityState::FrozenForIteration(_) => panic!("attempt to freeze during iteration"),
            MutabilityState::Frozen => {}
            MutabilityState::Mutable => self.state.set(MutabilityState::Shared),
            MutabilityState::Shared => {},
        }

        Self{
            state : Cell::new(MutabilityState::Shared),
            val: self.val.clone(),
        }
    }

    fn freeze(&self) {
        match self.state.get() {
            MutabilityState::FrozenForIteration(_) => panic!("attempt to freeze during iteration"),
            MutabilityState::Frozen => {}
            MutabilityState::Mutable => self.state.set(MutabilityState::Frozen),
            MutabilityState::Shared => self.state.set(MutabilityState::Frozen),
        }
    }

    /// Freezes the current value for iterating over.
    fn freeze_for_iteration(&self) {
        match self.state.get() {
            MutabilityState::Frozen => {}
            MutabilityState::FrozenForIteration(_) => panic!("already frozen"),
            MutabilityState::Mutable => self.state.set(MutabilityState::FrozenForIteration(false)),
            MutabilityState::Shared => self.state.set(MutabilityState::FrozenForIteration(true)),
        }
    }

    /// Unfreezes the current value for iterating over.
    fn unfreeze_for_iteration(&self) {
        match self.state.get() {
            MutabilityState::Frozen => {}
            MutabilityState::FrozenForIteration(false) => self.state.set(MutabilityState::Mutable),
            MutabilityState::FrozenForIteration(true) => self.state.set(MutabilityState::Shared),
            MutabilityState::Mutable => panic!("not frozen"),
            MutabilityState::Shared => panic!("not frozen"),
        }
    }
}

impl<T> ContentCell for ImmutableCell<T> {
    type Content = T;

    const MUTABLE : bool = false;

    fn new(value: T) -> Self {
        ImmutableCell(value)
    }

    fn borrow(&self) -> RefOrRef<T> {
        RefOrRef::Ptr(&self.0)
    }

    fn try_borrow(&self) -> Result<RefOrRef<T>, BorrowError> {
        Ok(RefOrRef::Ptr(&self.0))
    }

    fn borrow_mut(&self) -> RefMut<Self::Content> {
        panic!("immutable value cannot be mutably borrowed")
    }

    fn try_borrow_mut(&self) -> Result<RefMut<Self::Content>, ()> {
        Err(())
    }

    fn as_ptr(&self) -> *const T {
        &self.0 as *const T
    }

    fn shared(&self) -> Self {
        unimplemented!("shared not impled for immutables")
    }

    fn test_mut(&self) -> Result<(), ValueError> {
        Err(ValueError::CannotMutateImmutableValue)
    }

    fn freeze(&self) {
    }

    fn freeze_for_iteration(&self) {
    }

    fn unfreeze_for_iteration(&self) {
    }
}