use crate::{guard::Guard, term::{Term, ValueEq, Value}};
use core::marker::PhantomData;

pub struct Var<'a, T> {_marker: (PhantomData<Guard<'a>>, PhantomData<fn() -> T>,)}

impl<'a, T> Term for Var<'a, T> {
    type Type = T;
}

#[allow(non_snake_case)]
pub fn Var<'a, T>(_guard: Guard<'a>, v: T) -> Value<Var<'a, T>> {
    unsafe {Value::new_unchecked(v)}
}

impl<'a, T> Var<'a, T> {    
    pub fn erase<A: Term<Type = T>>(_guard: Guard<'a>) -> ValueEq<A, Var<'a, T>> {
        unsafe {ValueEq::axiom()}
    }

    pub fn alias<A: Term<Type = T>>(guard: Guard<'a>, x: Value<A>) -> (Value<Self>, ValueEq<A, Var<'a, T>>) {
        let eq = Var::erase::<A>(guard);
        (Value::equiv(eq).coerce(x), eq)
    }
}
