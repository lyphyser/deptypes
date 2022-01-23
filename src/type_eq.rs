// Heavily modified version of type_equalities

// # Notice from the original version of type_equalities
// Copyright (c) 2021 t WorldSEnder
// Licensed under the Apache License, Version 2.0
// <LICENSE-APACHE or http://www.apache.org/licenses/LICENSE-2.0> or the MIT
// license <LICENSE-MIT or http://opensource.org/licenses/MIT>,
// at your option. All files in the project carrying such
// notice may not be copied, modified, or distributed except
// according to those Values.

use core::marker::PhantomData;

use crate::{uninhabited::{Inhabited, Uninhabited, type_has_elements_or_uninhabited}, total::TotalFn};

/// Evidence of the transitive relation R(T, U) as a zero-sized type.
///
/// [invariant]: https://doc.rust-lang.org/nomicon/subtyping.html#variance
pub struct TypeLtR<R, T: ?Sized, U: ?Sized>(PhantomData<(*const R, *const core::cell::Cell<T>, *const core::cell::Cell<U>)>);

impl<R, T: ?Sized, U: ?Sized> Clone for TypeLtR<R, T, U> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<R, T: ?Sized, U: ?Sized> Copy for TypeLtR<R, T, U> {}

impl<R, T: ?Sized, U: ?Sized> core::fmt::Debug for TypeLtR<R, T, U> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("TypeLt<")?;
        f.write_str(core::any::type_name::<T>())?;
        f.write_str(" < ")?;
        f.write_str(core::any::type_name::<U>())?;
        f.write_str(">")?;
        Ok(())
    }
}

impl<R, T: ?Sized, U: ?Sized> TypeLtR<R, T, U> {
    /// Assert that `T < U`. You must ensure that any invariant required by relation R for safety holds.
    pub const unsafe fn axiom() -> Self {
        TypeLtR(PhantomData)
    }    

    /// Apply transitivity. `T < U & U < V  ==>  T < V`
    #[inline(always)]
    pub const fn trans<V: ?Sized>(self, _rhs: TypeLtR<R, U, V>) -> TypeLtR<R, T, V> {
        TypeLtR(PhantomData)
    }

    pub const fn le(self) -> TypeLeR<R, T, U> {
        unsafe {TypeLeR::axiom()}
    }
}

impl<R, T: ?Sized, U: ?Sized, V: ?Sized> core::ops::Add<TypeLtR<R, U, V>> for TypeLtR<R, T, U> {
    type Output = TypeLtR<R, T, V>;
    fn add(self, b: TypeLtR<R, U, V>) -> Self::Output {
        self.trans(b)
    }
}

pub type TypeNotLtR<R, T, U> = Uninhabited<TypeLtR<R, T, U>>;

impl<R, T: ?Sized, U: ?Sized> Uninhabited<TypeLtR<R, T, U>> {
    /// T !< U and T !< M implies M !< U
    #[inline(always)]
    pub fn triangle<M: ?Sized>(self, t_lt_m: TypeLtR<R, T, M>) -> TypeNotLtR<R, M, U> {
        self.rev_map(unsafe {TotalFn::new(|x|
            t_lt_m.trans(x)
        )})
    }
}

pub fn type_lt_or_not<R, X, Y>() -> Inhabited<Result<
    TypeLtR<R, X, Y>,
    TypeNotLtR<R, X, Y>
>> {
    type_has_elements_or_uninhabited()
}

/// Evidence of the preorder relation R(T, U) as a zero-sized type.
///
/// [invariant]: https://doc.rust-lang.org/nomicon/subtyping.html#variance
pub struct TypeLeR<R, T: ?Sized, U: ?Sized>(PhantomData<(*const R, *const core::cell::Cell<T>, *const core::cell::Cell<U>)>);

impl<R, T: ?Sized, U: ?Sized> Clone for TypeLeR<R, T, U> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<R, T: ?Sized, U: ?Sized> Copy for TypeLeR<R, T, U> {}

impl<R, T: ?Sized, U: ?Sized> core::fmt::Debug for TypeLeR<R, T, U> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("TypeLe<")?;
        f.write_str(core::any::type_name::<T>())?;
        f.write_str(" <= ")?;
        f.write_str(core::any::type_name::<U>())?;
        f.write_str(">")?;
        Ok(())
    }
}

impl<R, T: ?Sized> TypeLeR<R, T, T> {
    /// Construct evidence of the reflexive equality `T <= T`.
    pub const fn refl() -> Self {
        TypeLeR(PhantomData)
    }
}

impl<R, T: ?Sized> Default for TypeLeR<R, T, T> {
    fn default() -> Self {
        TypeLeR::refl()
    }
}

impl<R, T: ?Sized, U: ?Sized> TypeLeR<R, T, U> {
    /// Assert that `T <= U`. You must ensure that any invariant required by relation R for safety holds.
    pub const unsafe fn axiom() -> Self {
        TypeLeR(PhantomData)
    }    

    /// Apply transitivity. `T <= U & U <= V  ==>  T <= V`
    #[inline(always)]
    pub const fn trans<V: ?Sized>(self, _rhs: TypeLeR<R, U, V>) -> TypeLeR<R, T, V> {
        TypeLeR(PhantomData)
    }

    pub const fn eq(self, _rhs: TypeLeR<R, U, T>) -> TypeEqR<R, U, T> {
        unsafe {TypeEqR::axiom()}
    }
}

impl<R, T: ?Sized, U: ?Sized, V: ?Sized> core::ops::Add<TypeLeR<R, U, V>> for TypeLeR<R, T, U> {
    type Output = TypeLeR<R, T, V>;
    fn add(self, b: TypeLeR<R, U, V>) -> Self::Output {
        self.trans(b)
    }
}

pub type TypeNotLeR<R, T, U> = Uninhabited<TypeLeR<R, T, U>>;

impl<R, T: ?Sized, U: ?Sized> Uninhabited<TypeLeR<R, T, U>> {
    /// T !<= U and T !<= M implies M !<= U
    #[inline(always)]
    pub fn triangle<M: ?Sized>(self, t_le_m: TypeLeR<R, T, M>) -> TypeNotLeR<R, M, U> {
        self.rev_map(unsafe {TotalFn::new(|x|
            t_le_m.trans(x)
        )})
    }
}

pub fn type_le_or_not<R, X, Y>() -> Inhabited<Result<
    TypeLeR<R, X, Y>,
    TypeNotLeR<R, X, Y>
>> {
    type_has_elements_or_uninhabited()
}

/// Evidence of the equivalence relation R(T, U) as a zero-sized type.
///
/// [invariant]: https://doc.rust-lang.org/nomicon/subtyping.html#variance
pub struct TypeEqR<R, T: ?Sized, U: ?Sized>(PhantomData<(*const R, *const core::cell::Cell<T>, *const core::cell::Cell<U>)>);

impl<R, T: ?Sized, U: ?Sized> Clone for TypeEqR<R, T, U> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<R, T: ?Sized, U: ?Sized> Copy for TypeEqR<R, T, U> {}

impl<R, T: ?Sized, U: ?Sized> core::fmt::Debug for TypeEqR<R, T, U> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("TypeEq<")?;
        f.write_str(core::any::type_name::<T>())?;
        f.write_str(" == ")?;
        f.write_str(core::any::type_name::<U>())?;
        f.write_str(">")?;
        Ok(())
    }
}

impl<R, T: ?Sized> TypeEqR<R, T, T> {
    /// Construct evidence of the reflexive equality `T == T`.
    pub const fn refl() -> Self {
        TypeEqR(PhantomData)
    }
}

impl<R, T: ?Sized> Default for TypeEqR<R, T, T> {
    fn default() -> Self {
        TypeEqR::refl()
    }
}

impl<R, T: ?Sized, U: ?Sized> TypeEqR<R, T, U> {
    /// Assert that `T == U`. You must ensure that any invariant required by relation R for safety holds.
    pub const unsafe fn axiom() -> Self {
        TypeEqR(PhantomData)
    }

    /// Get the inverse equality. `T == U  ==>  U == T`
    #[inline(always)]
    pub const fn invert(self) -> TypeEqR<R, U, T> {
        TypeEqR(PhantomData)
    }

    /// Apply transitivity. `T == U & U == V  ==>  T == V`
    #[inline(always)]
    pub const fn trans<V: ?Sized>(self, _rhs: TypeEqR<R, U, V>) -> TypeEqR<R, T, V> {
        TypeEqR(PhantomData)
    }

    pub const fn le(self) -> TypeLeR<R, U, T> {
        unsafe {TypeLeR::axiom()}
    }
}

impl<R, T: ?Sized, U: ?Sized> core::ops::Neg for TypeEqR<R, T, U> {
    type Output = TypeEqR<R, U, T>;
    fn neg(self) -> Self::Output {
        self.invert()
    }
}

impl<R, T: ?Sized, U: ?Sized, V: ?Sized> core::ops::Add<TypeEqR<R, U, V>> for TypeEqR<R, T, U> {
    type Output = TypeEqR<R, T, V>;
    fn add(self, b: TypeEqR<R, U, V>) -> Self::Output {
        self.trans(b)
    }
}

impl<R, T: ?Sized, U: ?Sized, V: ?Sized> core::ops::Sub<TypeEqR<R, V, U>> for TypeEqR<R, T, U> {
    type Output = TypeEqR<R, T, V>;
    fn sub(self, b: TypeEqR<R, V, U>) -> Self::Output {
        self.trans(b.invert())
    }
}

/*/
pub struct TypeNeR<R, T: ?Sized, U: ?Sized>(PhantomData<(*const core::cell::Cell<R, T>, *const core::cell::Cell<R, U>)>);

impl<R, T: ?Sized, U: ?Sized> Clone for TypeNeR<R, T, U> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<R, T: ?Sized, U: ?Sized> Copy for TypeNeR<R, T, U> {}

impl<R, T: ?Sized, U: ?Sized> core::fmt::Debug for TypeNeR<R, T, U> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("TypeNe<")?;
        f.write_str(core::any::type_name::<R, T>())?;
        f.write_str(" != ")?;
        f.write_str(core::any::type_name::<R, U>())?;
        f.write_str(">")?;
        Ok(())
    }
}
*/

pub type TypeNeR<R, T, U> = Uninhabited<TypeEqR<R, T, U>>;

impl<R, T: ?Sized, U: ?Sized> Uninhabited<TypeEqR<R, T, U>> {
    /// Get the inverse equality. `T == U  ==>  U == T`
    #[inline(always)]
    pub const fn invert(self) -> TypeNeR<R, U, T> {
        unsafe {TypeNeR::axiom()}
    }

    /// Apply transitivity. `T != U & U == V  ==>  T != V`
    #[inline(always)]
    pub const fn trans<V: ?Sized>(self, _rhs: TypeEqR<R, U, V>) -> TypeNeR<R, T, V> {
        unsafe {TypeNeR::axiom()}
    }

    #[inline(always)]
    pub const fn trans_left<V: ?Sized>(self, rhs: TypeEqR<R, V, T>) -> TypeNeR<R, V, U> {
        self.invert().trans(rhs.invert()).invert()
    }
}

impl<R, T: ?Sized, U: ?Sized> core::ops::Neg for TypeNeR<R, T, U> {
    type Output = TypeNeR<R, U, T>;
    fn neg(self) -> Self::Output {
        self.invert()
    }
}

impl<R, T: ?Sized, U: ?Sized, V: ?Sized> core::ops::Add<TypeEqR<R, U, V>> for TypeNeR<R, T, U> {
    type Output = TypeNeR<R, T, V>;
    fn add(self, b: TypeEqR<R, U, V>) -> Self::Output {
        self.trans(b)
    }
}

impl<R, T: ?Sized, U: ?Sized, V: ?Sized> core::ops::Sub<TypeEqR<R, V, U>> for TypeNeR<R, T, U> {
    type Output = TypeNeR<R, T, V>;
    fn sub(self, b: TypeEqR<R, V, U>) -> Self::Output {
        self.trans(b.invert())
    }
}

impl<R, T: ?Sized, U: ?Sized, V: ?Sized> core::ops::Add<TypeNeR<R, U, V>> for TypeEqR<R, T, U> {
    type Output = TypeNeR<R, T, V>;
    fn add(self, b: TypeNeR<R, U, V>) -> Self::Output {
        b.trans_left(self)
    }
}

impl<R, T: ?Sized, U: ?Sized, V: ?Sized> core::ops::Sub<TypeNeR<R, V, U>> for TypeEqR<R, T, U> {
    type Output = TypeNeR<R, T, V>;
    fn sub(self, b: TypeNeR<R, V, U>) -> Self::Output {
        b.invert().trans_left(self)
    }
}

pub fn type_eq_or_ne<R, X, Y>() -> Inhabited<Result<
    TypeEqR<R, X, Y>,
    TypeNeR<R, X, Y>
>> {
    type_has_elements_or_uninhabited()
}
