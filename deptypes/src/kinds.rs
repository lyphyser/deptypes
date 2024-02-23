use crate::{term::{Term, ValueEq}, transmutable::Equiv};

/// SAFETY: Self::Type<'a> must be transmutable between lifetimes
pub unsafe trait L2S {
    type Type<'a>: Sized;

    fn equiv<'a, 'b>() -> Equiv<Self::Type<'a>, Self::Type<'b>> {
        unsafe {Equiv::axiom()}
    }    
}

pub type L2S_<'a, S> = <S as L2S>::Type<'a>;

/// SAFETY: Self::Type must be transmutable between ValueEq-equivalent terms.  This means it should be #[repr(C)] or #[repr(transparent)] or ZST.
pub unsafe trait Term2S<T> {
    type Type<U: Term<Type = T>>: Sized;

    fn equiv<A: Term<Type = T>, B: Term<Type = T>>(_eq: ValueEq<A, B>) -> Equiv<Self::Type<A>, Self::Type<B>> {
        unsafe {Equiv::axiom()}
    }
}

pub type Term2S_<S, U> = <S as Term2S<<U as Term>::Type>>::Type<U>;
