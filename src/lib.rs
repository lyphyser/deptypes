#![no_std]
#![recursion_limit = "256"]

#![cfg_attr(feature = "gat", feature(generic_associated_types))]
#![cfg_attr(feature = "never", feature(never_type))]

#[cfg(feature = "std")]
extern crate alloc;

pub use num_traits;

#[macro_use]
pub mod linkerror;

#[macro_use]
pub mod newtype;

pub use generativity as guard;
pub use generativity::make_guard as make_guard;

pub mod total;

#[macro_use]
pub mod type_eq;
pub mod transmutable;

pub mod uninhabited;

#[macro_use]
pub mod term;
pub mod var;
pub mod ops;
pub mod uint;
pub mod bool;
#[cfg(feature = "gat")]
pub mod induction;
pub mod slice;
pub mod fin;
#[cfg(feature = "gat")]
pub mod iter;
pub mod pair;
pub mod result;

#[cfg(feature = "std")]
#[cfg(feature = "gat")]
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
