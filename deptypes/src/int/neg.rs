use crate::{int::add::add_0_a_eq_a, ops::{Add, Neg, Sub}, term::{Term, ValueEq}, type_eq::refl};

use super::{add::{a_plus_0_eq_a, s_a_eq_a_plus_1}, sub::{a_minus_0_eq_a, a_minus_a_eq_0, a_minus_sub_b_c_eq_a_plus_sub_c_b, add_sub_associative, sub_add_associative, sub_sub_associative}, Int, Pred, Succ, Zero};

/// Axiom (definition of negation): -a = 0 - a
pub fn neg_a_eq_0_minus_a<N, A: Term<Type = N>>(
    ) -> ValueEq<Neg<A>, Sub<Zero<N>, A>>
    where N: Int
{
    // SAFETY: this is true for mathematical integers and thus for all types that implement Int by the requirements of Int
    unsafe {ValueEq::axiom()}
}

/// Theorem: --a = a
pub fn neg_neg_a_eq_a<N, A: Term<Type = N>>(
    ) -> ValueEq<Neg<Neg<A>>,A>
    where N: Int
{
    // --a = 0 - -a = 0 - (0 - a) = (0 - 0) + a = 0 + a == a
    neg_a_eq_0_minus_a() + Sub::eq(refl(), neg_a_eq_0_minus_a()) + sub_sub_associative() + Add::eq(a_minus_a_eq_0(), refl()) + add_0_a_eq_a()
}

/// Theorem: a + -b = a - b
pub fn a_plus_neg_b_eq_a_sub_b<N, A: Term<Type = N>, B: Term<Type = N>>(
    ) -> ValueEq<Add<A, Neg<B>>, Sub<A, B>>
    where N: Int
{
    // a + -b == a + (0 - b) == (a + 0) - b == a - b
    Add::eq(refl(), neg_a_eq_0_minus_a()) + add_sub_associative() + Sub::eq(a_plus_0_eq_a(), refl())
}

/// Theorem: -(a + b) = -a - b
pub fn neg_add_a_b_eq_neg_a_minus_b<N, A: Term<Type = N>, B: Term<Type = N>>(
    ) -> ValueEq<Neg<Add<A, B>>, Sub<Neg<A>, B>>
    where N: Int
{
    // -(a + b) = 0 - (a + b) = (0 - a) - b = -a - b
    neg_a_eq_0_minus_a() + sub_add_associative() + Sub::eq(-neg_a_eq_0_minus_a(), refl())
}

/// Theorem: -(a - b) = b - a
pub fn neg_sub_a_b_eq_b_minus_a<N, A: Term<Type = N>, B: Term<Type = N>>(
    ) -> ValueEq<Neg<Sub<A, B>>, Sub<B, A>>
    where N: Int
{
    // -(a - b) = 0 - (a - b) = 0 + (b - a) = b - a
    neg_a_eq_0_minus_a() + a_minus_sub_b_c_eq_a_plus_sub_c_b() + add_0_a_eq_a()
}

/// Theorem: -0 = 0
pub fn neg_zero_eq_zero<N>(
    ) -> ValueEq<Neg<Zero<N>>, Zero<N>>
    where N: Int {
    // -0 == 0 - 0 == 0
    neg_a_eq_0_minus_a() + a_minus_0_eq_a()
}

/// Theorem: -S(a) = P(-a) = -a - S(0)
pub fn neg_s_a_eq_neg_a_minus_1<N, A: Term<Type = N>>(
    ) -> ValueEq<Neg<Succ<A>>, Pred<Neg<A>>>
    where N: Int {
    // -S(a) = -(a + S(0)) = -a - S(0)
    Neg::eq(s_a_eq_a_plus_1()) + neg_add_a_b_eq_neg_a_minus_b()
}

/// Theorem: -a == -b => a == b
pub fn neg_eq_to_eq<N, A: Term<Type = N>, B: Term<Type = N>>(
    eq: ValueEq<Neg<A>, Neg<B>>
    ) -> ValueEq<A, B>
    where N: Int
{
    // a == --a = --b = b
    -neg_neg_a_eq_a() + Neg::eq(eq) + neg_neg_a_eq_a()
}
