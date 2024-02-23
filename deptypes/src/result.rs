use core::marker::PhantomData;
use core::mem::ManuallyDrop;
use crate::bool::choose;
use crate::guard::Guard;
use crate::term::Value;
use crate::var::Var;
use crate::transmutable::{coerce, Equiv};
use crate::term::ValueEq;
use crate::{bool::{False, True}, term::Term};

#[repr(C)]
pub union DResult<B: Term<Type = bool>, T, F> {
    phantom: PhantomData<Value<B>>,
    t: ManuallyDrop<T>,
    f: ManuallyDrop<F>,
}

impl<B: Term<Type = bool>, T, F> Drop for DResult<B, T, F> {
    #[inline(always)]
    fn drop(&mut self) {
        link_error!("DResult types are linear types that cannot be allowed to be dropped, instead use into() or into_result() so that the proper destructor is run");
    }
}

impl<T, F> DResult<True, T, F> {
    pub fn into(mut self) -> T {
        let r = unsafe {ManuallyDrop::take(&mut self.t)};
        core::mem::forget(self);
        r
    }

    pub fn new(t: T) -> Self {
        DResult {t: ManuallyDrop::new(t)}
    }
}

impl<T, F> DResult<False, T, F> {
    pub fn into(mut self) -> F {
        let r = unsafe {ManuallyDrop::take(&mut self.f)};
        core::mem::forget(self);
        r
    }

    pub fn new(f: F) -> Self {
        DResult {f: ManuallyDrop::new(f)}
    }
}

impl<B: Term<Type = bool>, T, F> DResult<B, T, F> {
    pub fn equiv<B1: Term<Type = bool>>(_: ValueEq<B, B1>) -> Equiv<DResult<B, T, F>, DResult<B1, T, F>> {
        unsafe {Equiv::axiom()}
    }
}

impl<'a, T, F> DResult<Var<'a, bool>, T, F> {
    pub fn from(guard: Guard<'a>, x: Result<T, F>) -> (Self, Result<ValueEq<Var<'a, bool>, True>, ValueEq<Var<'a, bool>, False>>) {
        match x {
            Ok(t) => {
                let eq = Var::erase(guard);
                let r = DResult::<True, _, _>::new(t);
                let r = coerce(r, DResult::equiv(eq));
                (r, Ok(-eq))
            }
            Err(f) => {
                let eq = Var::erase(guard);
                let r = DResult::<False, _, _>::new(f);
                let r = coerce(r, DResult::equiv(eq));
                (r, Err(-eq))
            }
        }
    }
}

impl<B: Term<Type = bool>, T, F> DResult<B, T, F> {
    pub fn into_result(r: DResult<B, T, F>, b: Value<B>) -> Result<T, F> {
        match choose(b) {
            Ok(eq) => {
                let r = coerce(r, DResult::equiv(eq));
                Ok(r.into())
            },
            Err(eq) => {
                let r = coerce(r, DResult::equiv(eq));
                Err(r.into())
            }
        }
    }
}
