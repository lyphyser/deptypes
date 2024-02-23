use crate::type_eq::{EqReflexive, TypeEqR, TypeLeR};
pub struct Transmutability {_marker: ()}
impl_zst! {impl Transmutability}

const TRANSMUTABILITY: Transmutability = Transmutability {_marker: ()};
impl<T> EqReflexive<T> for Transmutability {}

pub type Transm<X, Y> = TypeLeR<Transmutability, X, Y>;
pub type Equiv<X, Y> = TypeEqR<Transmutability, X, Y>;

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

pub fn coerce<T, U, P>(x: T, transm: P) -> U
    where Transm<T, U>: From<P> {
    Transm::from(transm).coerce(x)
}

/// This is needed because Vec is not repr(C)
#[cfg(feature = "std")]
pub fn coerce_vec<T, U, P>(vec: alloc::vec::Vec<T>, transm: P) -> alloc::vec::Vec<U>
    where Transm<T, U>: From<P> {
    let _ = Transm::<T, U>::from(transm);

    let ptr = vec.as_ptr();
    let length = vec.len();
    let capacity = vec.capacity();

    let ptr = ptr as *mut U;

    core::mem::forget(vec);
    // SAFETY: the vector type is transmutable
    unsafe {alloc::vec::Vec::from_raw_parts(ptr, length, capacity)}
}

unsafe fn equiv_definition<T, U, A, B, P>(x: P) -> Equiv<T, U>
    where Equiv<A, B>: From<P>{
    let _ = Equiv::from(x);
    Equiv::definition(&TRANSMUTABILITY)
}

unsafe fn transm_definition<T, U, A, B, P>(x: P) -> Transm<T, U>
    where Transm<A, B>: From<P> {
    let _ = Transm::from(x);
    Transm::definition(&TRANSMUTABILITY)
}

#[macro_export]
macro_rules! impl_transm {
    (@replace [tts $with:tt] [$($p:tt)*] []) => {
        $($p)*
    };
    (@replace [brackets $with:tt] [$($p:tt)*] []) => {
        [$($p)*]
    };
    (@replace [parens $with:tt] [$($p:tt)*] []) => {
        ($($p)*)
    };
    (@replace [curly $with:tt] [$($p:tt)*] []) => {
        {$($p)*}
    };
    (@replace [$mode:tt $with:tt] [$($p:tt)*] [T $($s:tt)*]) => {
        impl_transm! {@replace [$mode $with] [$($p)* $with] [$($s)*]}
    };
    (@replace [$mode:tt $with:tt] [$($p:tt)*] [[$($t:tt)*] $($s:tt)*]) => {
        impl_transm! {@replace [$mode $with] [$($p)* impl_transm!(@replace [brackets $with] [] [$($t)*])] [$($s)*]}
    };
    (@replace [$mode:tt $with:tt] [$($p:tt)*] [($($t:tt)*) $($s:tt)*]) => {
        impl_transm! {@replace [$mode $with] [$($p)* impl_transm!(@replace [parens $with] [] [$($t)*])] [$($s)*]}
    };
    (@replace [$mode:tt $with:tt] [$($p:tt)*] [{$($t:tt)*} $($s:tt)*]) => {
        impl_transm! {@replace [$mode $with] [$($p)* impl_transm!(@replace [curly $with] [] [$($t)*])] [$($s)*]}
    };
    (@replace [$mode:tt $with:tt] [$($p:tt)*] [$t:tt $($s:tt)*]) => {
        impl_transm! {@replace [$mode $with] [$($p)* $t] [$($s)*]}
    };

    (@transm [$(#[$m:meta])* $v:vis unsafe fn $name:ident $([$($T:tt)*])? <T> -> $($R:tt)*]) => {
        $crate::paste! {
            $(#[$m])* $v fn [<$name _transm>]<$($($T)*,)? A, B, P>(transm: P)
                -> Transm<impl_transm!(@replace [tts A] [] [$($R)*]), impl_transm!(@replace [tts B] [] [$($R)*])>
                where Transm<A, B>: From<P> {
                unsafe {transm_definition(transm)}
            }
        }
    };

    (@equiv [$(#[$m:meta])* $v:vis unsafe fn $name:ident $([$($T:tt)*])? <T> -> $($R:tt)*]) => {
        $crate::paste! {
            $(#[$m])* $v fn [<$name _equiv>]<$($($T)*,)? A, B, P>(equiv: P)
                -> Equiv<impl_transm!(@replace [tts A] [] [$($R)*]), impl_transm!(@replace [tts B] [] [$($R)*])>
                where Equiv<A, B>: From<P> {
                unsafe {equiv_definition(equiv)}
            }
        }
    };

    (@item [$($m:tt)*] $T:tt) => {
        $(
            impl_transm! {@$m $T}
        )*
    };

    (@item $(R:tt)*) => {
        ::core::compile_error!("Incorrect impl_transm! syntax");
    };

    (@parse $m:tt [] []) => {};

    (@parse $m:tt [$($p:tt)*] []) => {
        ::core::compile_error!("impl_transm! body must end with semicolon (if non-empty)");
    };

    (@parse $m:tt [$($p:tt)*] [; $($s:tt)*]) => {
        impl_transm! {@item $m [$($p)*]}
        impl_transm! {@parse $m [] [$($s)*]}
    };

    (@parse $m:tt [$($p:tt)*] [$t:tt $($s:tt)*]) => {
        impl_transm! {@parse $m [$($p)* $t] [$($s)*]}
    };

    (@ $(R:tt)*) => {
        ::core::compile_error!("implementation error in impl_transm!");
    };

    ($($R:tt)*) => {
        impl_transm! {@parse [transm equiv] [] [$($R)*]}
    };
}

#[macro_export]
macro_rules! impl_equiv {
    ($($R:tt)*) => {
        $crate::impl_transm! {@parse [equiv] [] [$($R)*]}
    };
}

impl_transm! {
    pub unsafe fn id <T> -> T;
    pub unsafe fn array [const N: usize] <T> -> [T; N];
    #[cfg(feature = "std")] pub unsafe fn box <T> -> alloc::boxed::Box<T>;
    //[cfg(feature = "std")] pub unsafe fn vec <T> -> alloc::vec::Vec<T>; // this is not correct because Vec is not repr(C)
    pub unsafe fn ref ['x] <T> -> &'x T;
}

impl_equiv! {
    pub unsafe fn mut ['x] <T> -> &'x mut T;
}