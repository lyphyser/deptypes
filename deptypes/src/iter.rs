use generativity::make_guard;

use crate::guard::Guard;
use crate::kinds::Term2S;
use crate::int::sub::s_a_minus_s_0_eq_a;
use crate::int::uint::{uint_as_succ, UInt};
use crate::loops::repeat_to_zero;
use crate::ops::Sub;
use crate::pair::DPair;
use crate::transmutable::{coerce, Equiv};
use crate::type_eq::refl;
use crate::unreachable::Unreachable;
use core::marker::PhantomData;
use core::mem::ManuallyDrop;

use crate::term::{Term, Value, ValueEq};
use crate::var::Var;
use crate::int::{Pred, Succ, Zero};

/// SAFETY: You must either implement equiv yourself, or Iter<L> must be transmutable to/from Iter<L2> where L and L2 are value-eq. This means it should be #[repr(C)] or #[repr(transparent)] or ZST
pub unsafe trait DLIterFamily {
    type LengthType: UInt;
    type Iter<L: Term<Type = Self::LengthType>>: DLIter<LengthType = Self::LengthType, Family = Self, Length = L>;
    type Item;

    fn next<L: Term<Type = Self::LengthType>>(
        iter: Self::Iter<Succ<L>>,
        value: Value<L>
    ) -> (Self::Iter<L>, Self::Item);

    fn finish(iter: Self::Iter<Zero<Self::LengthType>>);

    fn equiv<L1: Term<Type = Self::LengthType>, L2: Term<Type = Self::LengthType>>(_: ValueEq<L1, L2>) -> Equiv<Self::Iter<L1>, Self::Iter<L2>> {
        unsafe {Equiv::axiom()}
    }
}

#[allow(non_camel_case_types)]
struct DLIterFamily_Iter<F: DLIterFamily>(PhantomData<F>);

/// SAFETY: guaranteed by the safety requirements on DIterNoLenFamily
unsafe impl<F: DLIterFamily> Term2S<F::LengthType> for DLIterFamily_Iter<F> {
    type Type<L: Term<Type = F::LengthType>> = F::Iter<L>;
}

/// SAFETY: must be transmutable to/from Generic<L2> where L2 is a value-equivalent term
pub trait DLIter {
    type LengthType: UInt;
    type Family: DLIterFamily<LengthType = Self::LengthType, Iter<Self::Length> = Self>;
    type Length: Term<Type = Self::LengthType>;

    fn next(self, value: Value<Self::Length>) -> Result<
        (<Self::Family as DLIterFamily>::Iter<Pred<Self::Length>>, <Self::Family as DLIterFamily>::Item),
        ValueEq<Self::Length, Zero::<<Self::Length as Term>::Type>>
    > where Self: Sized
    {
        make_guard!(g);
        match uint_as_succ(g, value) {
            Ok((pred, eq)) => {
                let iter = coerce(self, Self::Family::equiv(eq));
                let (iter, x) = <Self::Family as DLIterFamily>::next(iter, pred);
                let iter = coerce(iter, Self::Family::equiv(-s_a_minus_s_0_eq_a() - Sub::eq(eq, refl())));
                Ok((iter, x))
            },
            Err(is_zero) => {
                let iter = coerce(self, Self::Family::equiv(is_zero));
                Self::Family::finish(iter);
                Err(is_zero)
            }
        }
    }

    fn drop(self, len: Value<Self::Length>)
        where Self: Sized {
        let iter = repeat_to_zero::<DLIterFamily_Iter<Self::Family>, _, _>(len, self, |pred_len, iter| {
            let (iter, _) = <Self::Family as DLIterFamily>::next(iter, pred_len.clone());
            iter
        });
        Self::Family::finish(iter);
    }
}

#[repr(C)]
pub struct DIter<I: DLIter>(ManuallyDrop<I>, Value<I::Length>);

impl<I: DLIter> Drop for DIter<I> {
    fn drop(&mut self) {
        unsafe {ManuallyDrop::take(&mut self.0)}.drop(self.1.clone())
    }
}

impl<I: DLIter> DIter<I> {
    pub fn into_inner(mut self) -> (I, Value<I::Length>) {
        let len = self.1.clone();
        let iter = unsafe {ManuallyDrop::take(&mut self.0)};
        core::mem::forget(self);
        (iter, len)
    }
    
    pub fn next(self) -> Result<
        (DIter<<I::Family as DLIterFamily>::Iter<Pred<I::Length>>>, <I::Family as DLIterFamily>::Item),
        ValueEq<I::Length, Zero::<<I::Length as Term>::Type>>
    > where Self: Sized
    {
        let (iter, len) = self.into_inner();
        match iter.next(len.clone()) {
            Ok((iter, x)) => Ok((DIter(ManuallyDrop::new(iter), Pred(len)), x)),
            Err(eq) => Err(eq)
        }
    }
}

#[repr(transparent)]
struct DIterPair<T, F>(Option<DPair<T, DLIterFamily_Iter<F>>>)
        where F: DLIterFamily<LengthType = T>;

impl_newtype! {
    impl [T, F] [T2, F2] DIterPair(Option<DPair<T, DLIterFamily_Iter<F>>>)
        where [F: DLIterFamily<LengthType = T>] [F2: DLIterFamily<LengthType = T2>]
}

impl<T, F: DLIterFamily<LengthType = T>> Iterator for DIterPair<T, F>
    where T: UInt {
    type Item = F::Item;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(pair) = self.0.take() {
            make_guard!(g);
            let (len, iter) = pair.into_inner(g);
            let res = iter.next(len.clone());
            match res {
                Ok((iter, x)) => {
                    self.0 = Some(DPair::new(Pred(len), iter));
                    Some(x)
                },
                Err(_eq) => None
            }
        } else {
            None
        }
    }
}

#[repr(C)]
pub struct DIterBridge<I: Iterator, L: Term, U: Unreachable>(I, U, PhantomData<Value<L>>);

pub struct DIterBridgeFamily<I, LT, U: Unreachable>(PhantomData<(I, LT, U)>);

unsafe impl<I: Iterator, LT: UInt, U: Unreachable> DLIterFamily for DIterBridgeFamily<I, LT, U> {
    type LengthType = LT;
    type Item = I::Item;
    type Iter<L: Term<Type = Self::LengthType>> = DIterBridge<I, L, U>;

    fn next<L: Term<Type = Self::LengthType>>(
            mut iter: Self::Iter<Succ<L>>,
            _value: Value<L>
        ) -> (Self::Iter<L>, Self::Item) {
        match Iterator::next(&mut iter.0) {
            Some(v) => (DIterBridge(iter.0, iter.1, PhantomData), v),
            None => {
                iter.1.unreachable();
            }
        }
    }

    fn finish(_iter: Self::Iter<Zero<Self::LengthType>>) {
    }
}

impl<I: Iterator, L: Term, U: Unreachable> DLIter for DIterBridge<I, L, U>
    where L::Type: UInt {
    type LengthType = L::Type;
    type Length = L;
    type Family = DIterBridgeFamily<I, <Self::Length as Term>::Type, U>;

    fn drop(self, _len: Value<L>) {
    }
}

impl<I: Iterator, LT: UInt, U: Unreachable> DIterBridge<I, Zero<LT>, U> {
    pub fn new_empty(iter: I) -> Self {
        // SAFETY: next() can never be called because the length is zero
        DIterBridge(iter, unsafe {U::new()}, PhantomData)
    }
}

impl<I: Iterator, L: Term, U: Unreachable> DIterBridge<I, L, U> {
    pub fn new_assert(iter: I, unreachable: U) -> Self {
        DIterBridge(iter, unreachable, PhantomData)
    }
}

impl<'a, I: ExactSizeIterator, U: Unreachable> DIterBridge<I, Var<'a, usize>, U> {
    pub fn new_exact(guard: Guard<'a>, iter: I, unreachable: U) -> (Self, Value<Var<'a, usize>>) {
        let len = iter.len();
        (DIterBridge(iter, unreachable, PhantomData), Var(guard, len))
    }
}

#[cfg(feature = "trusted_len")]
impl<'a, I: ExactSizeIterator + core::iter::TrustedLen> DIterBridge<I, Var<'a, usize>, UnreachableUnchecked> {
    pub fn new_trusted(guard: Guard<'a>, iter: I) -> (Self, Value<Var<'a, usize>>) {
        use core::unreachable::UnreachableUnchecked;
        unsafe {Self::new_exact(guard, iter, unsafe {UnreachableUnchecked::new()})}
    }
}
