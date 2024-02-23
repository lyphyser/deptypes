use crate::{guard::Guard, term::{Term, Value, ValueEq}, transmutable::coerce};
use core::marker::PhantomData;

pub struct Var<'a, T> {_marker: (PhantomData<Guard<'a>>, PhantomData<fn() -> T>,)}
pub type Erasure<'a, T> = Var<'a, <T as Term>::Type>;

impl<'a, T> Term for Var<'a, T> {
    type Type = T;
}

#[allow(non_snake_case)]
pub fn Var<'a, T>(_guard: Guard<'a>, v: T) -> Value<Var<'a, T>> {
    unsafe {Value::definition(v, &Var {_marker: (PhantomData, PhantomData)})}
}

impl<'a, T> Var<'a, T> {    
    pub fn erase<A: Term<Type = T>>(_guard: Guard<'a>) -> ValueEq<A, Var<'a, T>> {
        unsafe {ValueEq::axiom()}
    }

    pub fn alias<A: Term<Type = T>>(guard: Guard<'a>, x: Value<A>) -> (Value<Self>, ValueEq<A, Var<'a, T>>) {
        let eq = Var::erase::<A>(guard);
        let x = coerce(x, eq);
        (x, eq)
    }
}
