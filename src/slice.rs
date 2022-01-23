use core::ops::IndexMut;
use core::{marker::PhantomData, ops::Index};
use crate::guard::Guard;

use crate::term::{Term, Value};
use crate::var::Var;
use crate::uint::ConstUsize;
use crate::fin::Fin;

pub struct DSlice<T, L: Term<Type = usize>>(PhantomData<(Value<L>, [T])>, [T; 0]);

impl<'a, T, L: Term<Type = usize>> Index<Fin<L>> for DSlice<T, L> {
    type Output = T;

    fn index(&self, index: Fin<L>) -> &Self::Output {
        unsafe {core::mem::transmute((self as *const _ as *const T).add(Fin::into_inner(index)))}
    }
}

impl<'a, T, L: Term<Type = usize>> IndexMut<Fin<L>> for DSlice<T, L> {
    fn index_mut(&mut self, index: Fin<L>) -> &mut Self::Output {
        unsafe {core::mem::transmute((self as *mut _ as *mut T).add(Fin::into_inner(index)))}
    }
}

impl<T, L: Term<Type = usize>> DSlice<T, L> {
    pub unsafe fn new_ref_unchecked(x: &[T]) -> &Self {
        core::mem::transmute(x.as_ptr())
    }

    pub unsafe fn new_mut_unchecked(x: &mut [T]) -> &mut Self {
        core::mem::transmute(x.as_mut_ptr())
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
