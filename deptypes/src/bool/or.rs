use crate::{ops::Or, term::{Term, ValueEq}};

use super::{False, True};

pub fn or_false_eq_a<A: Term<Type = bool>>(
) -> ValueEq<Or<A, False>, A>
{
    unsafe {ValueEq::axiom()}
}

pub fn or_true_eq_true<A: Term<Type = bool>>(
) -> ValueEq<Or<A, True>, True>
{
    unsafe {ValueEq::axiom()}
}

pub fn or_commutative<A: Term<Type = bool>, B: Term<Type = bool>>(
) -> ValueEq<Or<A, B>, Or<B, A>>
{
    unsafe {ValueEq::axiom()}
}

pub fn or_a_a_eq_a<A: Term<Type = bool>>(
) -> ValueEq<Or<A, A>, A>
{
    unsafe {ValueEq::axiom()}
}

pub fn false_or_eq_b<B: Term<Type = bool>>(
) -> ValueEq<Or<False, B>, B>
{
    or_commutative() + or_false_eq_a()
}

pub fn true_or_eq_true<B: Term<Type = bool>>(
) -> ValueEq<Or<True, B>, True>
{
    or_commutative() + or_true_eq_true()
}
