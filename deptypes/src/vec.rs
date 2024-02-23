use crate::guard::Guard;
use crate::kinds::Term2S;
use crate::int::uint::UInt;
use crate::int::{One, Succ, Zero};
use crate::loops::repeat_to_zero;
use crate::int::sub::{a_minus_0_eq_a, a_plus_b_minus_b_eq_a, s_a_minus_s_0_eq_a, s_sub_a_s_b_eq_a_minus_b};
use crate::unreachable::UnreachableUnchecked;
use core::marker::PhantomData;
use core::mem::ManuallyDrop;
use core::ops::Deref;
use core::ops::DerefMut;
use crate::term::ValueEq;
use crate::transmutable::{coerce, Equiv, Transm};

use crate::term::{Term, Value};
use crate::var::Var;
use crate::fin::Fin;
use crate::slice::DSlice;
use crate::iter::{DIterBridge, DLIter, DLIterFamily};
use crate::ops::{Add, Sub};

use alloc::vec::Vec;

#[repr(C)]
pub struct DLVec<T, N: Term>(*mut T, usize, PhantomData<Value<N>>);

impl<T, N: Term> Drop for DLVec<T, N> {
    #[inline(always)]
    fn drop(&mut self) {
        link_error!("DLVec types are linear types that cannot be allowed to be dropped, instead use with_len() so that the proper destructor is run");
    }
}

impl<T, L: Term> DLVec<T, L>
    where usize: From<L::Type>, L::Type: UInt {
    pub fn with_len(self, len: Value<L>) -> DVec<T, L> {
        DVec(ManuallyDrop::new(self), len)
    }
}

impl<T, L: Term> Deref for DLVec<T, L> {
    type Target = DSlice<T, L>;

    fn deref(&self) -> &Self::Target {
        unsafe {DSlice::new_ref_unchecked(core::slice::from_raw_parts(self.0, 0))}
    }
}

impl<T, L: Term> DerefMut for DLVec<T, L> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe {DSlice::new_mut_unchecked(core::slice::from_raw_parts_mut(self.0, 0))}
    }
}

#[repr(C)]
pub struct DVec<T, L: Term>(ManuallyDrop<DLVec<T, L>>, Value<L>)
    where usize: From<L::Type>, L::Type: UInt;

impl<T, LT> DVec<T, Zero<LT>>
    where usize: From<LT>, LT: UInt {
    pub fn new() -> Self {
        unsafe {DVec::new_unchecked(Vec::new(), Zero())}
    }

    pub fn with_capacity(cap: usize) -> Self {
        unsafe {DVec::new_unchecked(Vec::with_capacity(cap), Zero())}
    }
}

impl<T, LT> Default for DVec<T, Zero<LT>>
    where usize: From<LT>, LT: UInt {
    fn default() -> Self {
        unsafe {DVec::new_unchecked(Vec::new(), Zero())}
    }
}

impl<T, L: Term> Drop for DVec<T, L>
    where usize: From<L::Type>, L::Type: UInt {
    fn drop(&mut self) {
        unsafe {Vec::from_raw_parts(self.0.0, usize::from(self.1.clone().into_inner()), self.0.1)};
    }
}

impl<T, L: Term> DVec<T, L>
    where usize: From<L::Type>, L::Type: UInt {
    pub fn equiv<L1: Term>(_: ValueEq<L, L1>) -> Equiv<DVec<T, L>, DVec<T, L1>>
        where usize: From<L1::Type>, L1::Type: UInt {
        unsafe {Equiv::axiom()}
    }

    pub fn transm<T1, L1: Term>(_: Transm<T, T1>, _: ValueEq<L, L1>) -> Transm<DVec<T, L>, DVec<T1, L1>>
        where usize: From<L1::Type>, L1::Type: UInt {
        unsafe {Transm::axiom()}
    }
}

impl<T, L: Term> DVec<T, L>
    where usize: From<L::Type>, L::Type: UInt {
    pub unsafe fn new_unchecked(mut vec: Vec<T>, len: Value<L>) -> DVec<T, L> {
        let (ptr, cap) = (vec.as_mut_ptr(), vec.capacity());
        core::mem::forget(vec);
        DVec(ManuallyDrop::new(DLVec(ptr, cap, PhantomData)), len)
    }
    
    pub fn into_vec(self) -> Vec<T> {
        let r = unsafe {Vec::from_raw_parts(self.0.0, usize::from(self.1.clone().into_inner()), self.0.1)};
        core::mem::forget(self);
        r
    }

    pub fn len(&self) -> Value<L> {
        self.1.clone()
    }

    pub fn push(self, x: T) -> DVec<T, Succ<L>> {
        let len = self.len();
        let mut v = self.into_vec();
        v.push(x);
        unsafe {DVec::new_unchecked(v, Succ(len))}
    }

    // TODO: provide our own dependent iterator
    pub fn into_iter(self) -> DIterBridge<alloc::vec::IntoIter<T>, L, UnreachableUnchecked> {
        DIterBridge::new_assert(self.into_vec().into_iter(), unsafe {UnreachableUnchecked::new()})
    }

    pub fn clear(self) -> DVec<T, Zero<L::Type>> {
        let mut v = self.into_vec();
        v.clear();
        unsafe {DVec::new_unchecked(v, Zero())}
    }

    pub fn add_iter<I, IL: Term<Type = L::Type>>(
        self,
        iter: I,
        len: Value<IL>
    ) -> DVec<T, Add<L, IL>>
        where I: DLIter<Length = IL>, I::Family: DLIterFamily<Item = T, LengthType = L::Type> {
        let vec = coerce(self, DVec::equiv(-a_plus_b_minus_b_eq_a()));
        
        #[repr(C)]
        struct State<F: DLIterFamily + ?Sized, RL: Term<Type = F::LengthType>, A: Term<Type = F::LengthType>>(DVec<F::Item, Sub<RL, A>>, <F as DLIterFamily>::Iter<A>)
            where usize: From<F::LengthType>;

        struct StateFamily<F: ?Sized, RL>(PhantomData<(*mut F, RL)>);

        unsafe impl<F: DLIterFamily, RL: Term<Type = F::LengthType>> Term2S<F::LengthType> for StateFamily<F, RL>
            where usize: From<F::LengthType> {
            type Type<A: Term<Type = F::LengthType>> = State<F, RL, A>;
        }
        
        let State(vec, iter) = repeat_to_zero::<StateFamily<I::Family, _>, _, _>(len, State(vec, iter), |pred_len, State(vec, iter)| {
            let (iter, x) = <I::Family as DLIterFamily>::next(iter, pred_len.clone());
            let vec = vec.push(x);
            let vec = coerce(vec, DVec::equiv(s_sub_a_s_b_eq_a_minus_b()));
            State(vec, iter)
        });
        let vec = coerce(vec, DVec::equiv(a_minus_0_eq_a()));
        I::Family::finish(iter);
        vec
    }
    
    pub fn add<BL: Term<Type = L::Type>>(
        self,
        bv: DVec<T, BL>,
    ) -> DVec<T, Add<L, BL>> {
        let len = bv.len();
        self.add_iter(bv.into_iter(), len)
    }
    
}

impl<T, L: Term> DVec<T, Succ<L>>
    where usize: From<L::Type>, L::Type: UInt + From<usize> {
    pub fn swap_remove<'a>(self, idx: Fin<L>) -> (DVec<T, L>, T) {
        let len = self.len();
        let mut v = self.into_vec();
        let x = v.swap_remove(usize::from(idx.into_inner()));
        let len = Sub(len, One());
        let len = coerce(len, s_a_minus_s_0_eq_a());
        (unsafe {DVec::new_unchecked(v, len)}, x)
    }
}

impl<T, L: Term> From<DVec<T, L>> for DLVec<T, L>
    where usize: From<L::Type>, L::Type: UInt {
    fn from(x: DVec<T, L>) -> Self {
        let r = DLVec(x.0.0, x.0.1, x.0.2);
        core::mem::forget(x);
        r
    }
}

impl<T, L: Term> Deref for DVec<T, L>
    where usize: From<L::Type>, L::Type: UInt {
    type Target = DLVec<T, L>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T, L: Term> DerefMut for DVec<T, L>
    where usize: From<L::Type>, L::Type: UInt {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<'a, T, LT> DVec<T, Var<'a, LT>>
    where usize: From<LT>, LT: UInt + TryFrom<usize> {
    pub fn try_from(guard: Guard<'a>, vec: Vec<T>) -> Result<Self, LT::Error> {
        let len = vec.len();
        let len = len.try_into()?;
        Ok(unsafe {DVec::new_unchecked(vec, Var(guard, len))})
    }
}

impl<'a, T> DVec<T, Var<'a, usize>> {
    pub fn from(guard: Guard<'a>, vec: Vec<T>) -> Self {
        let len = vec.len();
        unsafe {DVec::new_unchecked(vec, Var(guard, len.into()))}
    }
}

#[test]
pub fn test_fin_range() {
    extern crate std;
    use alloc::vec;
    use std::println;
    use generativity::make_guard;

    make_guard!(al);
    let a = DVec::from(al.into(), vec![3, 66, 80, 99]);
    println!("hello len={}", a.len());
    for i in Fin::range(a.len()) {
        println!("{}: {}", i, a[i]);
    }
    make_guard!(bl);
    let b = DVec::from(bl.into(), vec![434, 73, 13]);
    let c = a.add(b);
    println!("c len={}", c.len());
    for i in Fin::range(c.len()) {
        println!("{}: {}", i, c[i]);
    }
}
