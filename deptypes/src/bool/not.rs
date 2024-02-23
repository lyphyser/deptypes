use crate::term::{Term, ValueEq, ValueNe};
use crate::ops::Not;

use super::{ne_false_implies_true, ne_ne_implies_eq, ne_true_implies_false, False, True};

/// Axiom (definition of not in bool): !a != a
pub fn not_a_ne_a<T: Term<Type = bool>>() -> ValueNe<Not<T>, T> {
    unsafe {ValueNe::axiom()}
}

/// Theorem: a != b => a == !b
pub fn ne_implies_eq_not<A: Term<Type = bool>, B: Term<Type = bool>>(ne: ValueNe<A, B>) -> ValueEq<A, Not<B>> {
    ne_ne_implies_eq(ne, not_a_ne_a())
}

/// Theorem: !!a == a
pub fn not_not_a_eq_a<T: Term<Type = bool>>() -> ValueEq<Not<Not<T>>, T> {
    // !!a != !a && a != !a => !!a == a
    ne_ne_implies_eq(not_a_ne_a(), -not_a_ne_a())
}

/// Theorem !true == false
pub fn not_true_is_false() -> ValueEq<Not<True>, False> {
    ne_true_implies_false(not_a_ne_a())
}

/// Theorem !false == true
pub fn not_false_is_true() -> ValueEq<Not<False>, True> {
    ne_false_implies_true(not_a_ne_a())
}

/// Theorem a == b => !a != b
pub fn a_eq_b_implies_not_a_ne_b<A: Term<Type = bool>, B: Term<Type = bool>>(eq: ValueEq<A, B>) -> ValueNe<Not<A>, B> {
    // !a != a == b
    not_a_ne_a() + eq
}

/// Theorem !a == b => a != b
pub fn not_a_eq_b_implies_a_ne_b<A: Term<Type = bool>, B: Term<Type = bool>>(eq: ValueEq<Not<A>, B>) -> ValueNe<A, B> {
    // a != !a == b
    -not_a_ne_a() + eq
}
