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

use crate::values::*;
use std::fmt;
use std::ops::Deref;
use std::rc::Rc;
use std::{
    cell::{BorrowError, BorrowMutError, Cell, Ref, RefCell, RefMut},
    sync::Arc,
};

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
}

pub trait Mutable {
    fn val_ref(&self) -> VRef<dyn TypedValue>;
    fn imm_ref(&self) -> &dyn TypedValue;
    fn val_mut(&self) -> Result<VRefMut<dyn MutableValue>, ValueError>;
    fn freeze(&self) -> Result<FrozenValue, ValueError>;
    fn freeze_for_iteration(&self) -> Result<(), ValueError>;
    fn unfreeze_for_iteration(&self) -> Result<(), ValueError>;
}

pub trait MutableInner: Sized {
    fn val_ref(&self) -> &dyn TypedValue;
    fn val_mut(&mut self) -> &mut dyn MutableValue;
}

pub struct OwnedInner(Box<dyn MutableValue>);

impl MutableInner for OwnedInner {
    fn val_ref(&self) -> &dyn TypedValue {
        self.0.as_typed_value()
    }
    fn val_mut(&mut self) -> &mut dyn MutableValue {
        &mut *self.0
    }
}

pub trait MutableLink {
    type ImmutableType: ImmutableValue;
    type MutableType: MutableValue;
}

pub struct SharedInner(Arc<dyn ImmutableValue>);

impl SharedInner {
    fn to_mutable(&self) -> OwnedInner {
        OwnedInner(self.0.as_owned_value())
    }
}

impl MutableInner for SharedInner {
    fn val_ref(&self) -> &dyn TypedValue {
        self.0.as_typed_value()
    }
    fn val_mut(&mut self) -> &mut dyn MutableValue {
        panic!("no! this can't happen")
    }
}

pub enum MutabilityState {
    Mutable(OwnedInner),
    Shared(SharedInner),
}

impl MutabilityState {
    fn to_mutable(&self) -> OwnedInner {
        match self {
            MutabilityState::Mutable(..) => panic!("badab"),
            MutabilityState::Shared(v) => v.to_mutable(),
        }
    }

    fn val_ref(&self) -> &dyn TypedValue {
        match self {
            MutabilityState::Mutable(v) => v.val_ref(),
            MutabilityState::Shared(v) => v.val_ref(),
        }
    }

    fn val_mut(&mut self) -> &mut dyn MutableValue {
        match self {
            MutabilityState::Mutable(v) => v.val_mut(),
            MutabilityState::Shared(v) => v.val_mut(),
        }
    }
}

pub struct FrozenState {
    frozen: bool,
    inner: MutabilityState,
}

impl FrozenState {
    fn new(inner: MutabilityState) -> Self {
        Self{frozen: false, inner}
    }

    fn val_ref(&self) -> &dyn TypedValue {
        self.inner.val_ref()
    }

    fn val_mut(&mut self) -> &mut dyn MutableValue {
        self.inner.val_mut()
    }
}

pub struct MutableCell {
    state: RefCell<FrozenState>,
}

impl MutableCell {
    pub fn new<T: MutableValue>(t: T) -> Self {
        Self {
            state: RefCell::new(FrozenState::new(MutabilityState::Mutable(OwnedInner(
                Box::new(t),
            )))),
        }
    }

    pub fn new_shared(t: Arc<dyn ImmutableValue>) -> Self {
        Self {
            state: RefCell::new(FrozenState::new(MutabilityState::Shared(SharedInner(t)))),
        }
    }

    fn ensure_mut(&self) -> Result<(), ValueError> {
        let mut state = self.state.borrow_mut();
        if state.frozen {
            return Err(ValueError::MutationDuringIteration);
        }

        match state.inner {
            MutabilityState::Mutable(_) => { return Ok(()); },
            MutabilityState::Shared(..) => (),
        }

        state.inner = MutabilityState::Mutable(state.inner.to_mutable());

        Ok(())
    }
}

impl Mutable for MutableCell {
    fn imm_ref(&self) -> &dyn TypedValue {
        panic!("can't get immutable ref to mutable cell")
    }

    fn val_ref(&self) -> VRef<dyn TypedValue> {
        VRef::Borrowed(Ref::map(self.state.borrow(), |e| e.val_ref()))
    }

    fn val_mut(&self) -> Result<VRefMut<dyn MutableValue>, ValueError> {
        self.ensure_mut()?;
        Ok(VRefMut::map(self.state.borrow_mut(), |e| e.val_mut()))
    }

    fn freeze(&self) -> Result<FrozenValue, ValueError> {
        self.val_mut()?.freeze()
    }

    fn freeze_for_iteration(&self) -> Result<(), ValueError> {
        self.state.borrow_mut().frozen = true;
        Ok(())
    }

    fn unfreeze_for_iteration(&self) -> Result<(), ValueError> {
        self.state.borrow_mut().frozen = false;
        Ok(())
    }
}
