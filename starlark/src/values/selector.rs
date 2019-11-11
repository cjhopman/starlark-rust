use crate::values::error::{RuntimeError, ValueError};
use crate::values::iter::TypedIterable;
use crate::values::*;
use std::{cmp::Ordering, ops::Deref};

pub enum SelectorGen<ValueType: ValueLike> {
    Inner(ValueType),
    Added(ValueType, ValueType),
}

pub type Selector = SelectorGen<Value>;
pub type FrozenSelector = SelectorGen<FrozenValue>;

impl Selector {
    pub fn new(d: Value) -> Self {
        Selector::Inner(d)
    }

    pub fn added(left: Value, right: Value) -> ValueResult {
        Ok(Value::make_mutable(Selector::Added(left, right)))
    }
}
pub trait SelectorLike {
}

impl <T: ValueLike> SelectorLike for SelectorGen<T> {
}

pub trait ValueAsSelector {
    fn as_selector(&self) -> Option<VRef<dyn SelectorLike>>;
}

impl<T: ValueLike> ValueAsSelector for T {
    fn as_selector(&self) -> Option<VRef<dyn SelectorLike>> {
        self.downcast_ref::<FrozenSelector>()
            .map(|o| VRef::map(o, |e| e as &dyn SelectorLike))
            .or_else(|| {
                self.downcast_ref::<Selector>()
                    .map(|o| VRef::map(o, |e| e as &dyn SelectorLike))
            })
    }
}
pub trait SelectorBase {
    type Item: ValueLike;

}

impl SelectorBase for Selector {
    type Item = Value;
}

impl MutableValue for Selector {
    fn freeze(&self) -> Result<FrozenValue, ValueError> {
        match self {
            Selector::Inner(ref v) => {
                Ok(FrozenValue::make_immutable(FrozenSelector::Inner(v.freeze()?)))
            },
            Selector::Added(ref l, ref r) => {
                Ok(FrozenValue::make_immutable(FrozenSelector::Added(l.freeze()?, r.freeze()?)))
            }
        }
    }
    fn as_dyn_any_mut(&mut self) -> &mut dyn Any { self }
}

impl ImmutableValue for FrozenSelector {
    fn as_owned_value(&self) -> Box<dyn MutableValue> {
        unimplemented!()
    }    
}

impl SelectorBase for FrozenSelector {
    type Item = FrozenValue;
}


impl<T : ValueLike + 'static> TypedValue for SelectorGen<T> where SelectorGen<T> : SelectorBase<Item=T> {
    fn naturally_mutable(&self) -> bool {
        true
    }

    fn collect_repr(&self, s: &mut String) {
        
        match self {
            SelectorGen::Inner(v) => {
                s.push_str("select[");
                v.collect_repr(s);
                s.push(']');
            },
            SelectorGen::Added(l, r) => {
                l.collect_repr(s);
                s.push_str(" + ");
                r.collect_repr(s);
            }
        }
    }

    fn to_json(&self) -> String {
        unimplemented!()
    }

    fn get_type(&self) -> &'static str {
        "selector"
    }

    fn to_bool(&self) -> bool {
        true
    }

    fn add(&self, other: &Value) -> Result<Value, ValueError> {
        let this = match self {
            Self::Inner(ref v) => Value::make_mutable(Selector::new(v.clone_value())),
            Self::Added(ref l, ref r) => Selector::added(l.clone_value(), r.clone_value())?,
        };

        Selector::added(this, other.clone())
    }

    fn as_dyn_any(&self) -> &dyn Any {
        self
    }
}


