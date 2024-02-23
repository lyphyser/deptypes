use core::cmp::Ordering;
use core::marker::PhantomData;
use crate::type_eq::{EqReflexive, TypeEqR, TypeGeR, TypeGtR, TypeLeR, TypeLtR, TypeNeR, TypeOrdering};
use crate::transmutable::{Equiv, Transm};

pub trait Term
{
    type Type;
}

pub struct ValueCmp {_marker: ()}
impl_zst! {impl ValueCmp}

impl<T: Term> EqReflexive<T> for ValueCmp where T::Type: Eq {}
const VALUE_CMP: ValueCmp = ValueCmp {_marker: ()};

pub type ValueOrdering<X, Y> = TypeOrdering<ValueCmp, X, Y>;

pub type ValueEq<X, Y> = TypeEqR<ValueCmp, X, Y>;
pub type ValueNe<X, Y> = TypeNeR<ValueCmp, X, Y>;
pub type ValueLe<X, Y> = TypeLeR<ValueCmp, X, Y>;
pub type ValueLt<X, Y> = TypeLtR<ValueCmp, X, Y>;
pub type ValueGe<X, Y> = TypeGeR<ValueCmp, X, Y>;
pub type ValueGt<X, Y> = TypeGtR<ValueCmp, X, Y>;

/// Value of term A
/// the A::Type value is guaranteed to always be the same for a given type A and instantiation of its lifetimes (this must be respected when unsafely calling new_unchecked or unsafely implementing Eval)
#[repr(transparent)]
pub struct Value<A: Term>(A::Type);

impl_newtype! {
    impl [A] [B] Value(<A as Term>::Type) where [A: Term] [B: Term]
}

impl<A: Term> core::fmt::Debug for Value<A>
    where A::Type: core::fmt::Debug
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        f.write_str("Value<")?;
        f.write_str(core::any::type_name::<A>())?;
        f.write_str(">(")?;
        core::fmt::Debug::fmt(&self.0, f)?;
        f.write_str(")")
    }
}


impl<A: Term> Value<A> {
    pub const unsafe fn definition(value: A::Type, _: &A) -> Self {
        Value(value)
    }

    pub fn equiv_with<B: Term>(_: ValueEq<A, B>, _: Equiv<A::Type, B::Type>) -> Equiv<Value<A>, Value<B>> {
        unsafe {Equiv::axiom()}
    }

    pub fn transm_with<B: Term>(_: ValueEq<A, B>, _: Transm<A::Type, B::Type>) -> Transm<Value<A>, Value<B>> {
        unsafe {Transm::axiom()}
    }

    pub fn equiv<B: Term<Type = A::Type>>(eq: ValueEq<A, B>) -> Equiv<Value<A>, Value<B>> {
        Self::equiv_with(eq, Equiv::refl())
    }
}

impl<A: Term, B: Term<Type = A::Type>> From<ValueEq<A, B>> for Equiv<Value<A>, Value<B>> {
    fn from(eq: ValueEq<A, B>) -> Self {
        Value::equiv(eq)
    }
}

impl<A: Term, B: Term<Type = A::Type>> From<ValueEq<A, B>> for Transm<Value<A>, Value<B>> {
    fn from(eq: ValueEq<A, B>) -> Self {
        Equiv::from(eq).into()
    }
}

/// Return evidence of x == y or x != y
pub fn value_eq<X: Term, Y: Term>(x: Value<X>, y: Value<Y>) -> Result<
    ValueEq<X, Y>,
    ValueNe<X, Y>
> where X::Type: PartialEq<Y::Type>, X::Type: Eq, Y::Type: Eq {
    if x.into_inner() == y.into_inner() {
        Ok(ValueEq::definition(&VALUE_CMP))
    } else {
        Err(ValueNe::definition(&VALUE_CMP))
    }
}

/// Return evidence of x <= y
pub fn value_le<X: Term, Y: Term>(x: Value<X>, y: Value<Y>) -> Option<ValueLe<X, Y>>
    where X::Type: PartialOrd<Y::Type>, X::Type: Ord, Y::Type: Ord {
    if x.into_inner() <= y.into_inner() {
        Some(ValueLe::definition(&VALUE_CMP))
    } else {
        None
    }
}

/// Return evidence of x < y
pub fn value_lt<X: Term, Y: Term>(x: Value<X>, y: Value<Y>) -> Option<ValueLt<X, Y>>
    where X::Type: PartialOrd<Y::Type>, X::Type: Ord, Y::Type: Ord {
    if x.into_inner() < y.into_inner() {
        Some(ValueLt::definition(&VALUE_CMP))
    } else {
        None
    }
}

/// Return evidence of x < y or x > y
pub fn value_partial_cmp<X: Term, Y: Term>(x: Value<X>, y: Value<Y>) -> Result<ValueOrdering<X, Y>, ValueNe<X, Y>>
 where X::Type: PartialOrd<Y::Type>, X::Type: Ord, Y::Type: Ord {
    match x.into_inner().partial_cmp(&y.into_inner()) {
        Some(ord) => Ok(ValueOrdering::definition(ord, &VALUE_CMP)),
        None => Err(ValueNe::definition(&VALUE_CMP))
    }
}

/// Return evidence of x <= y or x > y
pub fn value_le_or_gt<X: Term, Y: Term<Type = X::Type>>(x: Value<X>, y: Value<Y>) -> Result<
    ValueLe<X, Y>,
    ValueGt<X, Y>
> where X::Type: Ord {
    if x.into_inner() <= y.into_inner() {
        Ok(ValueLe::definition(&VALUE_CMP))
    } else {
        Err(ValueGt::definition(&VALUE_CMP))
    }
}

/// Return evidence of x < y or x >= y
pub fn value_lt_or_ge<X: Term, Y: Term<Type = X::Type>>(x: Value<X>, y: Value<Y>) -> Result<
    ValueLt<X, Y>,
    ValueGe<X, Y>
> where X::Type: Ord {
    if x.into_inner() < y.into_inner() {
        Ok(ValueLt::definition(&VALUE_CMP))
    } else {
        Err(ValueGe::definition(&VALUE_CMP))
    }
}

pub fn value_cmp<X: Term, Y: Term<Type = X::Type>>(x: Value<X>, y: Value<Y>) -> ValueOrdering<X, Y>
 where X::Type: Ord {
    let ord = x.into_inner().cmp(&y.into_inner());
    ValueOrdering::definition(ord, &VALUE_CMP)
}

pub trait TotalCmp {
    fn total_cmp(&self, other: &Self) -> Ordering;
    fn total_lt(&self, other: &Self) -> bool;
    fn total_le(&self, other: &Self) -> bool;
    fn total_eq(&self, other: &Self) -> bool;
}

macro_rules! impl_total_cmp {
    ($($T:ty)*) => {
        $(
            impl TotalCmp for $T {
                fn total_cmp(&self, other: &Self) -> Ordering {self.total_cmp(other)}
                fn total_lt(&self, other: &Self) -> bool {self.total_cmp(other) == Ordering::Less}
                fn total_le(&self, other: &Self) -> bool {self.total_cmp(other) != Ordering::Greater}
                fn total_eq(&self, other: &Self) -> bool {self.to_bits() == other.to_bits()}
            }
        )*
    }
}

impl_total_cmp! {f32 f64}

/// Return evidence of x == y or x != y. Uses total_cmp()
pub fn total_eq<X: Term, Y: Term<Type = X::Type>>(x: Value<X>, y: Value<Y>) -> Result<
    ValueEq<X, Y>,
    ValueNe<X, Y>
> where X::Type: TotalCmp {
    if x.total_eq(&y) {
        Ok(ValueEq::definition(&VALUE_CMP))
    } else {
        Err(ValueNe::definition(&VALUE_CMP))
    }
}

/// Return evidence of x <= y or x > y
pub fn total_le<X: Term, Y: Term<Type = X::Type>>(x: Value<X>, y: Value<Y>) -> Result<
    ValueLe<X, Y>,
    ValueGt<X, Y>
> where X::Type: TotalCmp {
    if x.total_le(&y) {
        Ok(ValueLe::definition(&VALUE_CMP))
    } else {
        Err(ValueGt::definition(&VALUE_CMP))
    }
}

/// Return evidence of x < y or x >= y
pub fn total_lt<X: Term, Y: Term<Type = X::Type>>(x: Value<X>, y: Value<Y>) -> Result<
    ValueLt<X, Y>,
    ValueGe<X, Y>
> where X::Type: TotalCmp {
    if x.total_lt(&y) {
        Ok(ValueLt::definition(&VALUE_CMP))
    } else {
        Err(ValueGe::definition(&VALUE_CMP))
    }
}

pub fn total_cmp<X: Term, Y: Term<Type = X::Type>>(x: Value<X>, y: Value<Y>) -> ValueOrdering<X, Y>
 where X::Type: TotalCmp {
    let ord = x.into_inner().total_cmp(&y.into_inner());
    ValueOrdering::definition(ord, &VALUE_CMP)
}


/// Define a term, consisting of:
/// - A non-instantiable struct type `$name` implementing the Term trait
/// - A constructor function with the same name that creates a Value<`$name`>
/// - A `$name::eq` function that construct a ValueEq from ValueEqs for each term parameter
/// 
/// SAFETY: must ensure that, for any given input terms, and for equal values, the values returned are all equal
/// 
/// # Example
/// 
/// fn-like syntax:
/// ```rust
/// deptypes::term! {
///     pub fn Add(a, b) -> unsafe <a::Type as core::ops::Add<b::Type>>::Output
///         where a::Type: core::ops::Add<b::Type> {
///         core::ops::Add::add(a, b)
///     }
/// }
/// ```
/// 
/// Code generated by the macro
/// ```rust
/// use core::marker::PhantomData;
/// use deptypes::term::{Term, Value, ValueEq};
/// 
/// #[allow(non_camel_case_types)]
/// pub struct Add<a: Term, b: Term> {_marker: (PhantomData<fn() -> Value<a>>, PhantomData<fn() -> Value<b>>)}
/// 
/// #[allow(non_camel_case_types)]
/// impl<a: Term, b: Term> Term for Add<a, b>
///     where a::Type: core::ops::Add<b::Type> {
///     type Type = <a::Type as core::ops::Add<b::Type>>::Output;
/// }
/// 
/// #[allow(non_snake_case)]
/// #[allow(non_camel_case_types)]
/// pub fn Add<a: Term, b: Term>(a: Value<a>, b: Value<b>) -> Value<Add<a, b>>
///     where a::Type: core::ops::Add<b::Type> {
///     let (a, b) = (a.into_inner(), b.into_inner());
///     let ret = {core::ops::Add::add(a, b)};
///     unsafe {Value::definition(ret, &Add {_marker: (PhantomData, PhantomData)})}
/// }
/// 
/// #[allow(non_camel_case_types)]
/// impl<a0: Term, b0: Term> Add<a0, b0> {
///     pub fn eq<a1: Term, b1: Term>(_: ValueEq<a0, a1>, _: ValueEq<b0, b1>)
///      -> ValueEq<Self, Add<a1, b1>> {
///         unsafe { ValueEq::axiom() }
///     }
/// }
/// ```
#[macro_export]
macro_rules! term {
    // fn-like Values
    ($(#[$fn_attrs:meta])* $fn_vis:vis fn $fn:ident $($rest:tt)*) => {
        $crate::generics_parse_raw! {
            $crate::term_impl {
                @fn_parse_fn_body
                [$([$fn_attrs])*]
                [$fn_vis]
                $fn
                []
            }
            $($rest)*
        }
    };

    ($(#[$fn_attrs:meta])* $fn_vis:vis const fn $fn:ident $($rest:tt)*) => {
        $crate::generics_parse_raw! {
            $crate::term_impl {
                @fn_parse_fn_body
                [$([$fn_attrs])*]
                [$fn_vis]
                $fn
                [const]
            }
            $($rest)*
        }
    };
}

/// Used by term!
#[doc(hidden)]
#[macro_export]
macro_rules! term_impl {
    // Submacros for fn-like Values
    (@fn_parse_fn_body
        [$([$fn_attrs:meta])*]
        [$fn_vis:vis]
        $fn:ident
        [$($fn_keywords:tt)*]
        [$fn_gen:tt $fn_arg:tt $fn_where:tt $($fn_extra:tt)*]
        ($($param:tt)*) -> unsafe $type:ty {
            $($body:expr);*
        }
    ) => {
        $crate::internal::generics_parse_raw! {
            $crate::term_impl {
                @fn_params
                [
                    [
                        [
                            [[$(#[$fn_attrs])*] [$fn_vis] $fn]
                            [$(#[$fn_attrs])* #[allow(non_snake_case)]] [$fn_vis $($fn_keywords)*]
                        ]
                        $type {$($body);*}
                    ]
                    [$fn_gen $fn_arg $fn_where]
                ]
            }
            <$($param)*>
        }
    };

    (@fn_params
        $ctx:tt
        [
            [$([$($param_gen:tt)*])?]
            [$([$([$($param_arg:tt)*])*])?]
            $param_where:tt
            $($extra:tt)*
        ]
    ) => {
        $crate::term_impl! {
            @fn_parse_params
            [
                $ctx
                [$($($($param_arg)*),*)?]
            ]
            [] []
            [$($($param_gen)*)?]
            [$($([$($param_arg)*])*)?]
            $param_where
        }
    };

    (@fn_parse_params
        $ctx:tt
        [$($add_gen:tt)*]
        [$($add_arg:tt)*]
        [[$name:ident] $($param_gen:tt)*]
        [[$name_arg:ident] $($param_arg:tt)*]
        $param_where:tt
    ) => {
        $crate::term_impl! {
            @fn_parse_params
            $ctx
            [$($add_gen)* [$name : $crate::term::Term]]
            [$($add_arg)* [$name_arg]]
            [$($param_gen)*]
            [$($param_arg)*]
            $param_where
        }
    };

    (@fn_parse_params
        $ctx:tt
        [$($add_gen:tt)*]
        [$($add_arg:tt)*]
        [[$name:ident : $type:ty] $($param_gen:tt)*]
        [[$name_arg:ident] $($param_arg:tt)*]
        $param_where:tt
    ) => {
        $crate::term_impl! {
            @fn_parse_params
            $ctx
            [$($add_gen)* [$name: $crate::term::Term<Type = $type>]]
            [$($add_arg)* [$name_arg]]
            [$($param_gen)*]
            [$($param_arg)*]
            $param_where
        }
    };

    (@fn_parse_params
        [
            [
                $ctx:tt
                [[] [] $fn_where:tt]
            ]
            $fn_args:tt
        ]
        []
        []
        [] [] []
    ) => {
        $crate::term_impl! {
            @fn_output
            $ctx
            []
            [
                []
                []
                $fn_where
            ]
        }
    };

    (@fn_parse_params
        [
            [
                $ctx:tt
                [[$([$($fn_gen:tt)*])?] [$([$($fn_arg:tt)*])?] $fn_where:tt]
            ]
            $fn_args:tt
        ]
        [$($add_gen:tt)*]
        [$($add_arg:tt)*]
        [] [] []
    ) => {
        $crate::term_impl! {
            @fn_output
            $ctx
            $fn_args
            [
                [[$($($fn_gen)*)? $($add_gen)*]]
                [[$($($fn_arg)*)? $($add_arg)*]]
                $fn_where
            ]
        }
    };

    (@fn_output
        $ctx:tt
        $fn_args:tt
        [[$([$([$($struct_gen:tt)*])*])?] [$([$([$($struct_arg:tt)*])*])?] $fn_where:tt]
    ) => {
        $crate::term_impl! {
            @parse_generics
            [
                [
                    [
                        $ctx
                        [#[allow(non_camel_case_types)]]
                        [
                            [$(<$($($struct_gen)*),*>)?]
                            [$(<$($($struct_arg)*),*>)?]
                            []
                        ]
                    ]
                    $fn_args
                ]
                [
                    [$(<$($($struct_gen)*),*>)?]
                    [$(<$($($struct_arg)*),*>)?]
                    $fn_where
                ]
            ]
            [$($([$($struct_gen)*])*)?]
            [] [] [] []
            [] [] [] []
        }
    };

    (@parse_generics
        $ctx:tt
        [[const $name:ident $($tokens:tt)*] $($gen_rest:tt)*]
        [$($lifetimes_c:tt)*] [$($types_c:tt)*] [$($Values_c:tt)*] [$($consts_c:tt)*]
        [$($lifetimes:lifetime)*] [$($types:ident)*] [$($Values:ident)*] [$($consts:ident)*]
    ) => {
        $crate::term_impl! {@parse_generics $ctx
            [$($gen_rest)*]
            [$($lifetimes_c)*]
            [$($types_c)*]
            [$($Values_c)*]
            [$($consts_c)*  [$($tokens)*]]
            [$($lifetimes)*]
            [$($types)*]
            [$($Values)*]
            [$($consts)* $name]
        }
    };
    
    (@parse_generics
        $ctx:tt
        [[$lifetime:lifetime $($tokens:tt)*] $($gen_rest:tt)*]
        [$($lifetimes_c:tt)*] [$($types_c:tt)*] [$($Values_c:tt)*] [$($consts_c:tt)*]
        [$($lifetimes:lifetime)*] [$($types:ident)*] [$($Values:ident)*] [$($consts:ident)*]
    ) => {
        $crate::term_impl! {@parse_generics $ctx
            [$($gen_rest)*]
            [$($lifetimes_c)* [$($tokens)*]]
            [$($types_c)*]
            [$($Values_c)*]
            [$($consts_c)*]
            [$($lifetimes)* $lifetime]
            [$($types)*]
            [$($Values)*]
            [$($consts)*]
        }
    };

    // TODO: this unfortunately matches <any crate>::term::Term, but I don't think there's a better
    (@parse_generics
        $ctx:tt
        [[$name:ident : $krate:tt :: term :: Term $($tokens:tt)*] $($gen_rest:tt)*]
        [$($lifetimes_c:tt)*] [$($types_c:tt)*] [$($Values_c:tt)*] [$($consts_c:tt)*]
        [$($lifetimes:lifetime)*] [$($types:ident)*] [$($Values:ident)*] [$($consts:ident)*]
    ) => {
        $crate::term_impl! {@parse_generics $ctx
            [$($gen_rest)*]
            [$($lifetimes_c)*]
            [$($types_c)*]
            [$($Values_c)* [: $krate ::term::Term $($tokens)*]]
            [$($consts_c)*]
            [$($lifetimes)*]
            [$($types)*]
            [$($Values)* $name]
            [$($consts)*]
        }
    };

    (@parse_generics
        $ctx:tt
        [[$name:ident : Term $($tokens:tt)*] $($gen_rest:tt)*]
        [$($lifetimes_c:tt)*] [$($types_c:tt)*] [$($Values_c:tt)*] [$($consts_c:tt)*]
        [$($lifetimes:lifetime)*] [$($types:ident)*] [$($Values:ident)*] [$($consts:ident)*]
    ) => {
        $crate::term_impl! {@parse_generics $ctx
            [$($gen_rest)*]
            [$($lifetimes_c)*]
            [$($types_c)*]
            [$($Values_c)* [: Term $($tokens)*]]
            [$($consts_c)*]
            [$($lifetimes)*]
            [$($types)*]
            [$($Values)* $name]
            [$($consts)*]
        }
    };

    (@parse_generics
        $ctx:tt
        [[$type:tt $($tokens:tt)*] $($gen_rest:tt)*]
        [$($lifetimes_c:tt)*] [$($types_c:tt)*] [$($Values_c:tt)*] [$($consts_c:tt)*]
        [$($lifetimes:lifetime)*] [$($types:ident)*] [$($Values:ident)*] [$($consts:ident)*]
    ) => {
        $crate::term_impl! {@parse_generics $ctx
            [$($gen_rest)*]
            [$($lifetimes_c)*]
            [$($types_c)* [$($tokens)*]]
            [$($Values_c)*]
            [$($consts_c)*]
            [$($lifetimes)*]
            [$($types)* $type]
            [$($Values)*]
            [$($consts)*]
        }
    };

    (@parse_generics
        [[$ctx:tt [$($fn_arg:tt),*]] $concat:tt]
        []
        [$($lifetimes_c:tt)*] [$($types_c:tt)*] [$($Values_c:tt)*] [$($consts_c:tt)*]
        [$($lifetimes:lifetime)*] [$($types:ident)*] [$($Values:ident)*] [$($consts:ident)*]
    ) => {
        $crate::term_impl! {@output [[$ctx [$($fn_arg),*]] $concat]
            [$($lifetimes_c)*]
            [$($types_c)*]
            [$($Values_c)*]
            [$($consts_c)*]
            [$($lifetimes)*]
            [$($types)*]
            [$($Values)*]
            [$($consts)*]
            [$([$fn_arg: $crate::term::Value<$Values>])*]
        }
    };

    (@output
        [
            [
                [
                    [
                        [
                            [
                                [$($struct_attrs:tt)*] [$($struct_keywords:tt)*] $struct:ident
                            ]
                            [$($fn_attrs:tt)*] [$($fn_keywords:tt)*]
                        ]
                        $type:ty {$($body:expr);*}
                    ]
                    [$($struct_gen_attrs:tt)*]
                    [[$($struct_gen:tt)*] [$($struct_arg:tt)*] [$($struct_where:tt)*]]
                ]
                [$($fn_arg:ident),*]
            ]
            [[$($concat_gen:tt)*] [$($concat_arg:tt)*] [$($concat_where:tt)*]]
        ]
        [$([$($lifetimes_c:tt)*])*] [$([$($types_c:tt)*])*] [$([$($Values_c:tt)*])*] [$([$($consts_c:tt)*])*]
        [$($lifetimes:lifetime)*] [$($types:ident)*] [$($Values:ident)*] [$($consts:ident)*]
        [$([$($fn_param:tt)*])*]
    ) => {
        $($struct_attrs)* $($struct_gen_attrs)* $($struct_keywords)* struct $struct $($struct_gen)* $($struct_where)* {_marker: ($($crate::internal::PhantomData<fn() -> $crate::term::Value<$Values>>,)* $($crate::internal::PhantomData<fn() -> $types>,)*)}

        $($struct_gen_attrs)* impl $($struct_gen)* $crate::term::Term for $struct $($struct_arg)*
            $($concat_where)* {
            type Type = $type;
        }

        $($fn_attrs)* $($struct_gen_attrs)* $($fn_keywords)* fn $struct $($struct_gen)* ($($($fn_param)*),*) -> $crate::term::Value<$struct $($struct_arg)*>
            $($concat_where)* {
            let ($($fn_arg,)*) = ($($fn_arg.into_inner(),)*);
            let ret = {$($body);*};
            unsafe {$crate::term::Value::definition(ret, &$struct {_marker: 
                ($($crate::internal::PhantomData::<fn() -> $crate::term::Value<$Values>>,)* $($crate::internal::PhantomData<fn() -> $types>,)*)
            })}
        }

        $crate::paste! {
            $($struct_gen_attrs)* impl<$($lifetimes $($lifetimes_c)*,)* $($types $($types_c)*,)* $([<$Values 0>] $($Values_c)*,)* $(const $consts $($consts_c)*,)*> $struct<$($lifetimes,)* $($types,)* $([<$Values 0>],)* $($consts,)*> {
                pub fn eq<$([<$Values 1>] $($Values_c)*,)*> ($(_: $crate::term::ValueEq<[<$Values 0>], [<$Values 1>]>),*) -> $crate::term::ValueEq<Self, $struct<$($lifetimes,)* $($types,)* $([<$Values 1>],)* $($consts,)*>> {
                    unsafe {$crate::term::ValueEq::axiom()}
                }
            }
        }
    };
}


/// An erased term, used by DPair to erase values
pub struct Erased<T> {_marker: PhantomData<fn() -> T>}

impl<T> Term for Erased<T> {
    type Type = T;
}

impl<T> Erased<T> {
    /// SAFETY: must not be returned and must only be used in a way that doesn't create extra ValueEqs between non-Erased values
    pub unsafe fn erase<U: Term<Type = T>>() -> ValueEq<U, Erased<T>> {
        ValueEq::axiom()
    }
}

pub struct Def<N> {_marker: PhantomData<fn() -> N>}

impl<N> Term for Def<N> {
    type Type = N;
}

#[allow(non_snake_case)]
pub fn Def<N>() -> Value<Def<N>>
    where N: core::default::Default {
    unsafe {Value::definition(N::default(), &Def {_marker: PhantomData})}
}

impl<N> Def<N> {
    pub fn eq() -> ValueEq<Self, Self>
        where N: Eq {
        ValueEq::refl()
    }
}