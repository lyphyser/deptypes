use derive_where::derive_where;

use core::{cmp::Ordering, marker::PhantomData};

/// Asserts that the equality of a relation is reflexive
pub trait EqReflexive<T: ?Sized> {}

macro_rules! impl_type_r {
    ($(#[$m:meta])* struct $S:ident = $s:expr, $T:ident;) => {
        $(#[$m])*
        /// [invariant]: https://doc.rust-lang.org/nomicon/subtyping.html#variance
        pub struct $S<R, T: ?Sized, U: ?Sized>(PhantomData<(*const R, *const core::cell::Cell<T>, *const core::cell::Cell<U>)>);

        impl_zst!(impl [R, T, U] [R2, T2, U2] $S where [T: ?Sized, U: ?Sized] [T2: ?Sized, U2: ?Sized]);

        impl<R, T: ?Sized, U: ?Sized> core::fmt::Debug for $S<R, T, U> {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                f.write_str(core::any::type_name::<R>())?;
                f.write_str("<")?;
                f.write_str(core::any::type_name::<T>())?;
                f.write_str($s)?;
                f.write_str(core::any::type_name::<U>())?;
                f.write_str(">")?;
                Ok(())
            }
        }

        impl<R, T: ?Sized, U: ?Sized> $S<R, T, U> {
            /// Define the relation as a general property of relations
            const fn property() -> Self {
                $S(PhantomData)
            }

            /// Define the relation as a relation-specific defintion. Must hold a value of the relation type (which must not be publically constructible)
            pub const fn definition(_: &R) -> Self {
                $S(PhantomData)
            }

            /// Assert the relation. You must ensure that any invariant required by relation R for safety holds.
            pub const unsafe fn axiom() -> Self {
                $S(PhantomData)
            }

            /// Apply transitivity
            #[inline(always)]
            pub const fn trans<V: ?Sized>(self, _rhs: $T<R, U, V>) -> $S<R, T, V> {
                $S::property()
            }
        }

        impl<R, T: ?Sized, U: ?Sized, V: ?Sized> core::ops::Add<$T<R, U, V>> for $S<R, T, U> {
            type Output = $S<R, T, V>;
            fn add(self, b: $T<R, U, V>) -> Self::Output {
                self.trans(b)
            }
        }
    }
}

// Note that in PartialEq, we only have that a < b && b <= c => a < c or a,c incomparable
// Here instead we "extend" the PartialEq relation to have it imply a <= c
impl_type_r!(
    /// Evidence of the transitive relation R<(T, U) as a zero-sized type.
    struct TypeLtR = " < ", TypeLeR;
);

pub type TypeGtR<R, T, U> = TypeLtR<R, U, T>;

impl<R, T: ?Sized, U: ?Sized> TypeLtR<R, T, U> {
    pub const fn le(self) -> TypeLeR<R, T, U> {
        TypeLeR::property()
    }

    pub const fn ne(self) -> TypeNeR<R, T, U> {
        TypeNeR::property()
    }
}

impl<R, T: ?Sized, U: ?Sized>  From<TypeLtR<R, T, U>> for TypeLeR<R, T, U> {
    fn from(value: TypeLtR<R, T, U>) -> Self {
        value.le()
    }
}

impl<R, T: ?Sized, U: ?Sized>  From<TypeLtR<R, T, U>> for TypeNeR<R, T, U> {
    fn from(value: TypeLtR<R, T, U>) -> Self {
        value.ne()
    }
}

impl_type_r!(
    /// Evidence of the transitive relation R<=(T, U) as a zero-sized type.
    struct TypeLeR = " <= ", TypeLeR;
);

pub type TypeGeR<R, T, U> = TypeLeR<R, U, T>;

impl<R, T: ?Sized> TypeLeR<R, T, T>
    where R: EqReflexive<T> {
    /// Construct evidence of the reflexive equality `T <= T`.
    pub const fn refl() -> Self {
        TypeEqR::refl().le()
    }
}

impl<R, T: ?Sized> Default for TypeLeR<R, T, T>
    where R: EqReflexive<T> {
    fn default() -> Self {
        TypeLeR::refl()
    }
}

impl<R, T: ?Sized, U: ?Sized> TypeLeR<R, T, U> {
    pub const fn eq(self, _rhs: TypeLeR<R, U, T>) -> TypeEqR<R, T, U> {
        TypeEqR::property()
    }

    pub const fn lt(self, _ne: TypeNeR<R, T, U>) -> TypeLtR<R, U, T> {
        TypeLtR::property()
    }
}

impl_type_r!(
    /// Evidence of the symmetric and transitive relation R(T, U) as a zero-sized type.
    struct TypeEqR = " == ", TypeEqR;
);

impl<R, T: ?Sized> TypeEqR<R, T, T>
    where R: EqReflexive<T> {
    /// Construct evidence of the reflexive equality `T == T`.
    pub const fn refl() -> Self {
        TypeEqR::property()
    }
}

pub const fn refl<R, T: ?Sized>() -> TypeEqR<R, T, T>
    where R: EqReflexive<T> {
    TypeEqR::refl()
}

impl<R, T: ?Sized> Default for TypeEqR<R, T, T>
    where R: EqReflexive<T> {
    fn default() -> Self {
        TypeEqR::refl()
    }
}

impl<R, T: ?Sized, U: ?Sized> TypeEqR<R, T, U> {
    /// Get the inverse equality. `T == U  ==>  U == T`
    #[inline(always)]
    pub const fn invert(self) -> TypeEqR<R, U, T> {
        TypeEqR::property()
    }

    pub const fn le(self) -> TypeLeR<R, T, U> {
        TypeLeR::property()
    }
}

impl<R, T: ?Sized, U: ?Sized>  From<TypeEqR<R, T, U>> for TypeLeR<R, T, U> {
    fn from(value: TypeEqR<R, T, U>) -> Self {
        value.le()
    }
}

impl<R, T: ?Sized, U: ?Sized> core::ops::Neg for TypeEqR<R, T, U> {
    type Output = TypeEqR<R, U, T>;
    fn neg(self) -> Self::Output {
        self.invert()
    }
}

impl<R, T: ?Sized, U: ?Sized, V: ?Sized> core::ops::Sub<TypeEqR<R, V, U>> for TypeEqR<R, T, U> {
    type Output = TypeEqR<R, T, V>;
    fn sub(self, b: TypeEqR<R, V, U>) -> Self::Output {
        self.trans(b.invert())
    }
}

impl_type_r!(
    /// Evidence of absence of the symmetric and transitive relation R(T, U) as a zero-sized type.
    struct TypeNeR = " != ", TypeEqR;
);

impl<R, T: ?Sized, U: ?Sized> TypeNeR<R, T, U> {
    /// Get the inverse equality. `T != U  ==>  U != T`
    #[inline(always)]
    pub const fn invert(self) -> TypeNeR<R, U, T> {
        TypeNeR::property()
    }

    /// Apply T != U && T == V => V != U
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

#[derive_where(Copy, Clone, Debug, PartialEq, PartialOrd, Ord, Eq, Hash)]
#[repr(i8)]
pub enum TypeOrdering<R, T, U> {
    Lt(TypeLtR<R, T, U>) = -1,
    Eq(TypeEqR<R, T, U>) = 0,
    Gt(TypeGtR<R, T, U>) = 1,
}

impl<R, T, U> TypeOrdering<R, T, U> {
    pub fn definition(ordering: Ordering, r: &R) -> Self {
        match ordering {
            Ordering::Less => TypeOrdering::Lt(TypeLtR::definition(r)),
            Ordering::Equal => TypeOrdering::Eq(TypeEqR::definition(r)),
            Ordering::Greater => TypeOrdering::Gt(TypeGtR::definition(r)),
        }
    }
}

/// The relation that indicates that two types are the same type
/// Only constructible via `TypeEq::refl()`
///
/// Note that evidence that types are not the same cannot be provided in general since it would depend on lifetime equality
pub struct TypeIdentity {_marker: ()}
impl_zst! {impl TypeIdentity}

impl<T> EqReflexive<T> for TypeIdentity {}

pub type TypeEq<T, U> = TypeEqR<TypeIdentity, T, U>;
