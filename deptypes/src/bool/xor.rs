use crate::{ops::{Xor, Not}, term::{Term, ValueEq}};

use super::{False, True};

pub fn xor_false_eq_a<A: Term<Type = bool>>(
) -> ValueEq<Xor<A, False>, A>
{
    unsafe {ValueEq::axiom()}
}

pub fn xor_true_eq_not_a<A: Term<Type = bool>>(
) -> ValueEq<Xor<A, True>, Not<A>>
{
    unsafe {ValueEq::axiom()}
}

pub fn xor_commutative<A: Term<Type = bool>, B: Term<Type = bool>>(
) -> ValueEq<Xor<A, B>, Xor<B, A>>
{
    unsafe {ValueEq::axiom()}
}

pub fn xor_a_a_eq_false<A: Term<Type = bool>>(
) -> ValueEq<Xor<A, A>, False>
{
    unsafe {ValueEq::axiom()}
}

pub fn false_xor_eq_b<B: Term<Type = bool>>(
) -> ValueEq<Xor<False, B>, B>
{
    xor_commutative() + xor_false_eq_a()
}

pub fn true_xor_eq_not_b<B: Term<Type = bool>>(
) -> ValueEq<Xor<True, B>, Not<B>>
{
    xor_commutative() + xor_true_eq_not_a()
}
