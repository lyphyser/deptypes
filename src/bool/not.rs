use crate::term::{Term, ValueEq, ValueNe};
use crate::ops::{Not};

use super::{False, True, true_ne_false};

pub fn not_true_is_false() -> ValueEq<Not<True>, False> {
    unsafe {ValueEq::axiom()}
}

pub fn not_false_is_true() -> ValueEq<Not<False>, True> {
    unsafe {ValueEq::axiom()}
}

pub fn not_is_ne<T: Term<Type = bool>>() -> ValueNe<Not<T>, T> {
    // TODO: could prove this
    unsafe {ValueNe::axiom()}
}

pub fn not_not_is_value<T: Term<Type = bool>>() -> ValueEq<Not<Not<T>>, T> {
    // TODO: could prove this
    unsafe {ValueEq::axiom()}
}

pub fn true_implies_ne_not_true<T: Term<Type = bool>>(eq: ValueEq<T, True>) -> ValueNe<Not<T>, True> {
    Not::eq(eq) + not_true_is_false() - true_ne_false()
}

pub fn not_true_implies_ne_true<T: Term<Type = bool>>(eq: ValueEq<Not<T>, True>) -> ValueNe<T, True> {
    -not_not_is_value() + Not::eq(eq) + not_true_is_false() - true_ne_false()
}
