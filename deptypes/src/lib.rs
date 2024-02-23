#![no_std]

#![cfg_attr(feature = "never", feature(never_type))]
#![cfg_attr(feature = "trusted_len", feature(trusted_len))]

#[cfg(feature = "std")]
extern crate alloc;

pub use num_traits;

#[macro_use]
pub mod linkerror;

#[macro_use]
pub mod newtype;

#[macro_use]
pub mod zst;

pub use generativity as guard;
pub use generativity::make_guard as make_guard;

#[macro_use]
pub mod type_eq;

#[macro_use]
pub mod transmutable;

#[macro_use]
pub mod term;
pub mod var;
pub mod ops;
pub mod int;
pub mod bool;
pub mod slice;
pub mod fin;
pub mod unreachable;
pub mod iter;
pub mod pair;
pub mod result;
pub mod loops;
pub mod kinds;

#[cfg(feature = "std")]
pub mod vec;

/// For usage by macro-generated code
#[doc(hidden)]
pub use generics2::parse as generics_parse;

/// For usage by macro-generated code
#[doc(hidden)]
pub use generics2::parse_raw as generics_parse_raw;

/// For usage by macro-generated code
#[doc(hidden)]
pub use generics2::concat as generics_concat;

/// For usage by macro-generated code
#[doc(hidden)]
pub mod internal {
    pub use core::marker::PhantomData;
    pub use core::mem::transmute;
    pub use core::mem::transmute_copy;
    pub use core::default::Default;
    pub use generics2::parse_raw as generics_parse_raw;
}

/// For usage by macro-generated code
#[doc(hidden)]
pub use paste::paste;

#[cfg(doctest)]
#[doc = include_str!("../README.md")]
extern {}
