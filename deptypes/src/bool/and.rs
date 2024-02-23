use crate::{ops::And, term::{Term, ValueEq}};

use super::{False, True};

pub fn and_false_eq_false<A: Term<Type = bool>>(
) -> ValueEq<And<A, False>, False>
{
    unsafe {ValueEq::axiom()}
}

pub fn and_true_eq_a<A: Term<Type = bool>>(
) -> ValueEq<And<A, True>, A>
{
    unsafe {ValueEq::axiom()}
}

pub fn and_commutative<A: Term<Type = bool>, B: Term<Type = bool>>(
) -> ValueEq<And<A, B>, And<B, A>>
{
    unsafe {ValueEq::axiom()}
}

pub fn and_a_a_eq_a<A: Term<Type = bool>>(
) -> ValueEq<And<A, A>, A>
{
    unsafe {ValueEq::axiom()}
}

pub fn false_and_eq_false<B: Term<Type = bool>>(
) -> ValueEq<And<False, B>, False>
{
    and_commutative() + and_false_eq_false()
}

pub fn true_and_eq_b<B: Term<Type = bool>>(
) -> ValueEq<And<True, B>, B>
{
    and_commutative() + and_true_eq_a()
}
