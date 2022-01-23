use crate::guard::{Guard, make_guard};
use crate::uint::add::{a_plus_0_eq_a, sa_eq_s_a_and_sb_eq_s_b_implies_sa_plus_b_eq_a_plus_sb};
use core::marker::PhantomData;
use core::mem::ManuallyDrop;
use core::ops::Deref;
use core::ops::DerefMut;
use crate::term::ValueEq;
use crate::transmutable::{Transm, Equiv};

use crate::term::{Term, Value};
use crate::var::Var;
use crate::fin::Fin;
use crate::slice::DSlice;
use crate::iter::{DIter, DIterator};
use crate::ops::Add;
use crate::uint::{Succ, Zero};

use alloc::vec::Vec;

#[repr(C)]
pub struct DVecNoLen<T, N: Term<Type = usize>>(*mut T, usize, PhantomData<Value<N>>);

impl<T, N: Term<Type = usize>> Drop for DVecNoLen<T, N> {
    #[inline(always)]
    fn drop(&mut self) {
        link_error!("DVecNoLen types are linear types that cannot be allowed to be dropped, instead use with_len() so that the proper destructor is run");
    }
}

impl<T, L: Term<Type = usize>> DVecNoLen<T, L> {
    pub fn with_len(self, len: Value<L>) -> DVec<T, L> {
        DVec(ManuallyDrop::new(self), len)
    }
}

impl<T, L: Term<Type = usize>> Deref for DVecNoLen<T, L> {
    type Target = DSlice<T, L>;

    fn deref(&self) -> &Self::Target {
        unsafe {DSlice::new_ref_unchecked(core::slice::from_raw_parts(self.0, 0))}
    }
}

impl<T, L: Term<Type = usize>> DerefMut for DVecNoLen<T, L> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe {DSlice::new_mut_unchecked(core::slice::from_raw_parts_mut(self.0, 0))}
    }
}

#[repr(C)]
pub struct DVec<T, L: Term<Type = usize>>(ManuallyDrop<DVecNoLen<T, L>>, Value<L>);

impl<T> Default for DVec<T, Zero<usize>> {
    fn default() -> Self {
        unsafe {DVec::new_unchecked(Vec::new())}
    }
}

impl<T, L: Term<Type = usize>> Drop for DVec<T, L> {
    fn drop(&mut self) {
        unsafe {Vec::from_raw_parts(self.0.0, self.1.into_inner(), self.0.1)};
    }
}

impl<T, L: Term<Type = usize>> DVec<T, L> {
    pub fn equiv<L1: Term<Type = usize>>(_: ValueEq<L, L1>) -> Equiv<DVec<T, L>, DVec<T, L1>> {
        unsafe {Equiv::axiom()}
    }

    pub fn transm<T1, L1: Term<Type = usize>>(_: Transm<T, T1>, _: ValueEq<L, L1>) -> Transm<DVec<T, L>, DVec<T1, L1>> {
        unsafe {Transm::axiom()}
    }
}

impl<T, L: Term<Type = usize>> DVec<T, L> {
    pub unsafe fn new_unchecked(mut vec: Vec<T>) -> DVec<T, L> {
        let (ptr, len, cap) = (vec.as_mut_ptr(), vec.len(), vec.capacity());
        core::mem::forget(vec);
        DVec(ManuallyDrop::new(DVecNoLen(ptr, cap, PhantomData)), Value::new_unchecked(len))
    }

    pub fn into_vec(self) -> Vec<T> {
        let r = unsafe {Vec::from_raw_parts(self.0.0, self.1.into_inner(), self.0.1)};
        core::mem::forget(self);
        r
    }

    pub fn len(&self) -> Value<L> {
        self.1
    }

    pub fn push(self, x: T) -> DVec<T, Succ<L>> {
        let mut v = self.into_vec();
        v.push(x);
        unsafe {DVec::new_unchecked(v)}
    }

    pub fn into_iter(self) -> DIter<alloc::vec::IntoIter<T>, L> {
        unsafe { DIter::new_unchecked(self.into_vec().into_iter()) }
    }

    pub fn clear(self) -> DVec<T, Zero<usize>> {
        let mut v = self.into_vec();
        v.clear();
        unsafe {DVec::new_unchecked(v)}
    }

    pub fn swap_remove<'a>(self, idx: Fin<L>) -> (DVec<T, Var<'a, usize>>, T, ValueEq<Succ<Var<'a, usize>>, L>) {
        let mut v = self.into_vec();
        let x = v.swap_remove(*idx);
        (unsafe {DVec::new_unchecked(v)}, x, unsafe {ValueEq::axiom()})
    }
}

impl<T, L: Term<Type = usize>> From<DVec<T, L>> for DVecNoLen<T, L> {
    fn from(x: DVec<T, L>) -> Self {
        let r = DVecNoLen(x.0.0, x.0.1, x.0.2);
        core::mem::forget(x);
        r
    }
}

impl<T, L: Term<Type = usize>> Deref for DVec<T, L> {
    type Target = DVecNoLen<T, L>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T, L: Term<Type = usize>> DerefMut for DVec<T, L> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<'a, T> DVec<T, Var<'a, usize>> {
    pub fn from(_guard: Guard<'a>, vec: Vec<T>) -> Self {
        unsafe {DVec::new_unchecked(vec)}
    }
}

impl<T> DVec<T, Zero<usize>> {
    pub fn new() -> Self {
        unsafe {DVec::new_unchecked(Vec::new())}
    }
}

// DVec<T, A + 1>, B::Generic
pub fn add_iter<T, A: Term<Type = usize>, B: Term<Type = usize>>(
    a: DVec<T, A>,
    b: impl DIterator<Length = B, Item = T>,
) -> DVec<T, Add<A, B>> {
    make_guard!(g);
    let m = b.next(g.into());
    match m {
        Ok((bp, x, b_eq_s_bp)) => {
            let an = a.push(x);
            make_guard!(an_guard);
            let an_eq_s_a = Var::erase(an_guard.into());
            let an_erased = DVec::equiv(an_eq_s_a).coerce(an);
            let r = add_iter(an_erased, bp);

            DVec::equiv(sa_eq_s_a_and_sb_eq_s_b_implies_sa_plus_b_eq_a_plus_sb(-an_eq_s_a, b_eq_s_bp)).coerce(r)
        }
        Err(e) => {
            DVec::equiv(Add::eq(ValueEq::refl(), e)
                .trans(a_plus_0_eq_a::<_, A>())
                .invert()).coerce(a)
        },
    }
}

pub fn add<T, A: Term<Type = usize>, B: Term<Type = usize>>(
    av: DVec<T, A>,
    bv: DVec<T, B>,
) -> DVec<T, Add<A, B>> {
    add_iter(av, bv.into_iter())
}

#[test]
pub fn test_fin_range() {
    extern crate std;
    use alloc::vec;
    use std::println;

    make_guard!(al);
    let a = DVec::from(al.into(), vec![3, 66, 80, 99]);
    println!("hello len={}", a.len());
    for i in Fin::range(a.len()) {
        println!("{}: {}", i, a[i]);
    }
    make_guard!(bl);
    let b = DVec::from(bl.into(), vec![434, 73, 13]);
    let c = add(a, b);
    println!("c len={}", c.len());
    for i in Fin::range(c.len()) {
        println!("{}: {}", i, c[i]);
    }
}