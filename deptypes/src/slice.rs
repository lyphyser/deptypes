use core::ops::IndexMut;
use core::ptr::NonNull;
use core::{marker::PhantomData, ops::Index};
use crate::guard::Guard;

use crate::int::{Succ, Zero};
use crate::iter::{DLIter, DLIterFamily};
//use crate::iter::DIterNoLen;
use crate::term::{Term, Value};
use crate::var::Var;
use crate::int::{ConstUsize, uint::UInt};
use crate::fin::Fin;

pub struct DSlice<T, L: Term>(PhantomData<(Value<L>, [T])>, [T; 0]);

impl<'a, T, L: Term> Index<Fin<L>> for DSlice<T, L>
    where usize: From<L::Type>, L::Type: UInt {
    type Output = T;

    fn index(&self, index: Fin<L>) -> &Self::Output
    where usize: From<L::Type>, L::Type: UInt {
        unsafe {core::mem::transmute((self as *const _ as *const T).add(usize::from(Fin::into_inner(index))))}
    }
}

impl<'a, T, L: Term> IndexMut<Fin<L>> for DSlice<T, L>
    where usize: From<L::Type>, L::Type: UInt {
    fn index_mut(&mut self, index: Fin<L>) -> &mut Self::Output
        where usize: From<L::Type>, L::Type: UInt {
        unsafe {core::mem::transmute((self as *mut _ as *mut T).add(usize::from(Fin::into_inner(index))))}
    }
}

macro_rules! impl_slice_iter {
    ($S:ident $F:ident $as_ref:ident $($m:tt)*) => {
        #[repr(C)]
        pub struct $S<'a, T, L: Term>
        {
            ptr: NonNull<T>,
            _marker: PhantomData<(&'a T, Value<L>)>
        }

        pub struct $F<'a, T, LT>(PhantomData<fn(LT) -> &'a T>);

        unsafe impl<'a, T, LT: UInt> DLIterFamily for $F<'a, T, LT> {
            type LengthType = LT;
            type Iter<L: Term<Type = Self::LengthType>> = $S<'a, T, L>;
            type Item = &'a $($m)* T;

            fn next<L: Term<Type = Self::LengthType>>(
                iter: Self::Iter<Succ<L>>,
                _value: Value<L>
            ) -> (Self::Iter<L>, Self::Item) {
                let mut ptr = iter.ptr;
                let ptr = &mut ptr;
                let r = unsafe {ptr.$as_ref()};
                let iter = $S {ptr: unsafe {NonNull::new_unchecked(ptr.as_ptr().offset(1))}, _marker: PhantomData};
                (iter, r)
            }

            fn finish(_iter: Self::Iter<Zero<Self::LengthType>>) {
            }    
        }

        impl<'a, T, L: Term> DLIter for $S<'a, T, L>
            where L::Type: UInt {
            type LengthType = L::Type;
            type Length = L;
            type Family = $F<'a, T, L::Type>;

            fn drop(self, _len: Value<L>) {
            }
        }
    }
}

impl_slice_iter! {DSliceIter DSliceIterFamily as_ref}
impl_slice_iter! {DSliceIterMut DSliceIterMutFamily as_mut mut}

impl<T, L: Term> DSlice<T, L> {
    pub unsafe fn new_ref_unchecked(x: &[T]) -> &Self {
        core::mem::transmute(x.as_ptr())
    }

    pub unsafe fn new_mut_unchecked(x: &mut [T]) -> &mut Self {
        core::mem::transmute(x.as_mut_ptr())
    }

    pub fn iter(&self) -> DSliceIter<'_, T, L> {
        DSliceIter {ptr: unsafe {NonNull::new_unchecked(&self.1[0] as *const T as *mut T)}, _marker: PhantomData}
    }

    pub fn iter_mut(&mut self) -> DSliceIterMut<'_, T, L> {
        DSliceIterMut {ptr: unsafe {NonNull::new_unchecked(&self.1[0] as *const T as *mut T)}, _marker: PhantomData}
    }
}

impl<'a, T> DSlice<T, Var<'a, usize>>
{
    pub fn new_ref<'x>(guard: Guard<'a>, x: &'x [T]) -> (&'x DSlice<T, Var<'a, usize>>, Value<Var<'a, usize>>) {
        let len = x.len();
        (unsafe {DSlice::new_ref_unchecked(x)}, Var(guard, len))
    }

    pub fn new_mut<'x>(guard: Guard<'a>, x: &'x mut [T]) -> (&'x mut DSlice<T, Var<'a, usize>>, Value<Var<'a, usize>>) {
        let len = x.len();
        (unsafe {DSlice::new_mut_unchecked(x)}, Var(guard, len))
    }
}

impl<'a, T, const N: usize> From<&'a [T; N]> for &'a DSlice<T, ConstUsize<N>> {
    fn from(x: &'a [T; N]) -> Self {
        unsafe {core::mem::transmute(x)}
    }
}

impl<'a, T, const N: usize> From<&'a mut [T; N]> for &'a mut DSlice<T, ConstUsize<N>> {
    fn from(x: &'a mut [T; N]) -> Self {
        unsafe {core::mem::transmute(x)}
    }
}
