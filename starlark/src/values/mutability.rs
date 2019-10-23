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
use std::ops::Deref;
use std::rc::Rc;

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

pub type VRef<'a, T> = RefOrRef<'a, T>;

pub type VRefMut<'a, T> = RefMut<'a, T>;

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

    /*
        pub fn map_result<U: ?Sized, E : std::fmt::Debug, F>(orig: RefOrRef<'a, T>, f: F) -> Result<RefOrRef<'a, U>, E>
        where
            F: FnOnce(&T) -> Result<&U, E>,
        {
            match orig {
                RefOrRef::Ptr(p) => Ok(RefOrRef::Ptr(f(p)?)),
                RefOrRef::Borrowed(p) => {
                    let r: Ref<Result<&U, E>> = Ref::map(p, f);
                    match *r {
                        Err(e) => Err(e),
                        Ok(..) => Ok(RefOrRef::Borrowed(Ref::map(r, |e| e.unwrap()))),
                    }
                }
            }
        }
    */
}

/// Container for data which is either `RefCell` or immutable data.
pub trait ContentCell {
    type Content;

    const MUTABLE: bool;

    fn new(value: Self::Content) -> Self;
    fn borrow(&self) -> RefOrRef<'_, Self::Content>;
    fn try_borrow(&self) -> Result<RefOrRef<Self::Content>, BorrowError>;
    fn borrow_mut(&self) -> RefMut<'_, Self::Content>;
    fn try_borrow_mut(&self) -> Result<RefMut<'_, Self::Content>, ()>;
    fn shared(&self) -> Self;
    fn as_ptr(&self) -> *const Self::Content;

    fn test_mut(&self) -> Result<(), ValueError>;

    fn freeze_for_iteration(&self);
    fn unfreeze_for_iteration(&self);
}

/// Container for immutable data
#[derive(Debug, Clone)]
pub struct ImmutableCell<T>(T);

pub trait CloneForCell {
    fn clone_for_cell(&self) -> Self;
}

#[derive(Debug)]
pub enum Sharable<T> {
    Uninit,
    Owned(T),
    Shared(Rc<T>),
}

impl<T> Sharable<T> {
    pub fn to_ref(&self) -> &T {
        match self {
            Sharable::Uninit => panic!(),
            Sharable::Owned(ref t) => t,
            Sharable::Shared(ref rc) => &*rc,
        }
    }

    pub fn to_ref_mut(&mut self) -> &mut T {
        match self {
            Sharable::Uninit => panic!(),
            Sharable::Owned(ref mut t) => t,
            Sharable::Shared(_) => panic!(),
        }
    }

    pub fn shared(&mut self) -> Sharable<T> {
        match self {
            Sharable::Uninit => panic!(),
            Sharable::Shared(ref rc) => Sharable::Shared(rc.clone()),
            Sharable::Owned(_) => {
                let mut taken = Sharable::Uninit;
                std::mem::swap(self, &mut taken);
                match taken {
                    Sharable::Owned(t) => {
                        let rc = Rc::new(t);
                        let mut sharable = Sharable::Shared(rc.clone());
                        std::mem::swap(self, &mut sharable);
                        Sharable::Shared(rc.clone())
                    }
                    _ => unreachable!(),
                }
            }
        }
    }
}

#[derive(Debug)]
pub struct MutableCell<T: CloneForCell> {
    state: Cell<MutabilityState>,
    val: RefCell<Sharable<T>>,
}

impl<T: CloneForCell> MutableCell<T> {
    pub fn ensure_owned(&self) {
        match self.state.get() {
            MutabilityState::Shared => {
                self.state.set(MutabilityState::Mutable);
                // println!("making owned");
                let mut bw = self.val.borrow_mut();
                let cl = match *bw {
                    Sharable::Shared(ref rc) => rc.clone_for_cell(),
                    _ => panic!(),
                };
                *bw = Sharable::Owned(cl);
            }
            MutabilityState::Mutable => match *self.val.borrow() {
                Sharable::Owned(..) => {}
                _ => panic!(),
            },
            MutabilityState::Frozen => panic!(),
            MutabilityState::FrozenForIteration(_) => panic!(),
        }
    }
}

impl<T: CloneForCell> ContentCell for MutableCell<T> {
    type Content = T;

    const MUTABLE: bool = true;

    fn new(value: T) -> Self {
        Self {
            state: Cell::new(MutabilityState::Mutable),
            val: RefCell::new(Sharable::Owned(value)),
        }
    }

    fn test_mut(&self) -> Result<(), ValueError> {
        self.state.get().test()
    }

    fn borrow(&self) -> RefOrRef<T> {
        RefOrRef::Borrowed(Ref::map(RefCell::borrow(&self.val), Sharable::to_ref))
    }

    fn try_borrow(&self) -> Result<RefOrRef<T>, BorrowError> {
        RefCell::try_borrow(&self.val).map(|b| RefOrRef::Borrowed(Ref::map(b, Sharable::to_ref)))
    }

    fn borrow_mut(&self) -> RefMut<Self::Content> {
        self.ensure_owned();
        RefMut::map(RefCell::borrow_mut(&self.val), Sharable::to_ref_mut)
    }

    fn try_borrow_mut(&self) -> Result<RefMut<Self::Content>, ()> {
        match self.state.get() {
            MutabilityState::Shared | MutabilityState::Mutable => {
                self.ensure_owned();
                RefCell::try_borrow_mut(&self.val)
                    .map(|b| RefMut::map(b, Sharable::to_ref_mut))
                    .map_err(|e| ())
            }
            MutabilityState::Frozen => Err(()),
            MutabilityState::FrozenForIteration(_) => Err(()),
        }
    }

    fn as_ptr(&self) -> *const T {
        let ptr = RefCell::as_ptr(&self.val);

        unsafe {
            match *ptr {
                Sharable::Uninit => panic!(),
                Sharable::Owned(ref p) => &*p,
                Sharable::Shared(ref rc) => &**rc,
            }
        }
    }

    fn shared(&self) -> Self {
        match self.state.get() {
            MutabilityState::FrozenForIteration(_) => panic!("attempt to freeze during iteration"),
            MutabilityState::Frozen => {}
            MutabilityState::Mutable => {
                self.state.set(MutabilityState::Shared);
            }
            MutabilityState::Shared => {}
        }

        let shared = self.val.borrow_mut().shared();

        Self {
            state: Cell::new(MutabilityState::Shared),
            val: RefCell::new(shared),
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

    const MUTABLE: bool = false;

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

    fn freeze_for_iteration(&self) {}

    fn unfreeze_for_iteration(&self) {}
}
