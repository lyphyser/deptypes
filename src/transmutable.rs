use crate::type_eq::{TypeEqR, TypeLeR};

pub struct Transmutability;
pub type Transm<X, Y> = TypeLeR<Transmutability, X, Y>;
pub type Equiv<X, Y> = TypeEqR<Transmutability, X, Y>;

pub fn array_equiv<A, B, const N: usize>(_: Equiv<A, B>) -> Equiv<[A; N], [B; N]> {
    unsafe {Equiv::axiom()}
}

pub fn array_transm<A, B, const N: usize>(_: Transm<A, B>) -> Transm<[A; N], [B; N]> {
    unsafe {Transm::axiom()}
}

#[cfg(feature = "std")]
pub fn box_equiv<A, B>(_: Equiv<A, B>) -> Equiv<alloc::boxed::Box<A>, alloc::boxed::Box<B>> {
    unsafe {Equiv::axiom()}
}

#[cfg(feature = "std")]
pub fn box_transm<A, B>(_: Transm<A, B>) -> Transm<alloc::boxed::Box<A>, alloc::boxed::Box<B>> {
    unsafe {Transm::axiom()}
}

#[cfg(feature = "std")]
pub fn vec_equiv<A, B>(_: Equiv<A, B>) -> Equiv<alloc::vec::Vec<A>, alloc::vec::Vec<B>> {
    unsafe {Equiv::axiom()}
}

#[cfg(feature = "std")]
pub fn vec_transm<A, B>(_: Transm<A, B>) -> Transm<alloc::vec::Vec<A>, alloc::vec::Vec<B>> {
    unsafe {Transm::axiom()}
}

pub fn ref_equiv<'x, A, B>(_: Equiv<A, B>) ->  Equiv<&'x A, &'x B> {
    unsafe {Equiv::axiom()}
}

pub fn ref_transm<'x, A, B>(_: Transm<A, B>) -> Transm<&'x A, &'x B> {
    unsafe {Transm::axiom()}
}

pub fn mut_equiv<'x, A, B>(_: Equiv<A, B>) -> Equiv<&'x mut A, &'x mut B> {
    unsafe {Equiv::axiom()}
}

pub fn mut_transm<'x, A, B>(_: Transm<A, B>) -> Transm<&'x mut A, &'x mut B> {
    unsafe {Transm::axiom()}
}

impl<T, U> Equiv<T, U> {
    /// Coerce a value of type `T` to a value of type `U`
    #[inline(always)]
    pub fn coerce(self, t: T) -> U
    {
        let u = unsafe {core::mem::transmute_copy(&t)};
        core::mem::forget(t);
        u
    }
}

impl<T, U> Transm<T, U> {
    /// Coerce a value of type `T` to a value of type `U`
    #[inline(always)]
    pub fn coerce(self, t: T) -> U
    {
        let u = unsafe {core::mem::transmute_copy(&t)};
        core::mem::forget(t);
        u
    }
}
