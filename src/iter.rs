use crate::guard::Guard;
use core::marker::PhantomData;

use crate::term::{Term, Value, ValueEq};
use crate::var::Var;
use crate::uint::{Succ, Zero};

// TODO: does this trait really need to be unsafe?
pub unsafe trait DIterator {
    type Item;
    type Length: Term;
    type Generic<'a>: DIterator<Length = Var<'a, <Self::Length as Term>::Type>, Item = Self::Item>;

    fn next<'a>(
        self,
        guard: Guard<'a>,
    ) -> Result<
        (
            Self::Generic<'a>,
            Self::Item,
            ValueEq<Self::Length, Succ<Var<'a, <Self::Length as Term>::Type>>>,
        ),
        ValueEq<Self::Length, Zero<<Self::Length as Term>::Type>>,
    >;
}

#[repr(transparent)]
pub struct DIter<I: Iterator, L: Term>(I, PhantomData<Value<L>>);

unsafe impl<I: Iterator, L: Term> DIterator for DIter<I, L> {
    type Length = L;
    type Item = I::Item;
    type Generic<'a> = DIter<I, Var<'a, L::Type>>;

    fn next<'a>(
        mut self,
        _guard: Guard<'a>,
    ) -> Result<
        (
            Self::Generic<'a>,
            Self::Item,
            ValueEq<L, Succ<Var<'a, L::Type>>>,
        ),
        ValueEq<L, Zero<L::Type>>,
    > {
        match Iterator::next(&mut self.0) {
            Some(v) => Ok((DIter(self.0, PhantomData), v, unsafe {
                ValueEq::axiom()
            })),
            None => Err(unsafe { ValueEq::axiom() }),
        }
    }
}

impl<'a, I: Iterator> DIter<I, Var<'a, u64>> {
    pub fn from(_guard: Guard<'a>, iter: I) -> Self {
        DIter(iter, PhantomData)
    }
}

impl<I: Iterator, L: Term> DIter<I, L> {
    pub unsafe fn new_unchecked(iter: I) -> Self {
        DIter(iter, PhantomData)
    }
}

impl<'a, I: ExactSizeIterator> DIter<I, Var<'a, usize>> {
    pub fn new_exact(guard: Guard<'a>, iter: I) -> (Self, Value<Var<'a, usize>>) {
        let len = iter.len();
        (DIter(iter, PhantomData), Var(guard, len))
    }
}
