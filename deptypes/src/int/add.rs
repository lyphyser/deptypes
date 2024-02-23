use crate::term::{Term, ValueEq, ValueLe};
use crate::ops::Add;
use crate::type_eq::refl;

use super::uint::{a_ge_0, UInt};
use super::{Int, One, Succ, Zero};

// Axiom: a + 0 = a
pub fn a_plus_0_eq_a<N, A: Term<Type = N>>() -> ValueEq<Add<A, Zero<N>>, A>
where
    N: Int,
{
    unsafe {ValueEq::axiom()}
}

// Axiom: a + S(b) = S(a + b)
#[allow(non_snake_case)]
pub fn a_plus_s_b_eq_s_add_a_b<N, A: Term<Type = N>, B: Term<Type = N>>(
) -> ValueEq<Add<A, Succ<B>>, Succ<Add<A,B>>>
where
    N: Int,
{
    unsafe {ValueEq::axiom()}
}

// Axiom: a <= b && c <= d && a + c <= b + d
pub fn add_le<N, A: Term<Type = N>, B: Term<Type = N>, C: Term<Type = N>, D: Term<Type = N>>(
    _a_le_b: ValueLe<A, B>,
    _c_le_d: ValueLe<C, D>
    ) -> ValueLe<Add<A, C>, Add<B, D>>
    where N: Int
{
    unsafe {ValueLe::axiom()}
}

/// Axiom: a + c == b + d && c == d => a == b
pub fn add_eq_to_left_eq<N, A: Term<Type = N>, B: Term<Type = N>, C: Term<Type = N>, D: Term<Type = N>>(
    _eq: ValueEq<Add<A, C>, Add<B, D>>,
    _c_eq_d: ValueEq<C, D>
    ) -> ValueEq<A, B>
    where N: Int
{
    // this is circular
    // a == a + c - c == b + d - d == b
    //-a_plus_b_minus_b_eq_a() + crate::ops::Sub::eq(eq, c_eq_d) + a_plus_b_minus_b_eq_a();

    unsafe {ValueEq::axiom()}
}

/// Axiom: a + b = b + a
pub fn add_commutative<N, A: Term<Type = N>, B: Term<Type = N>>(
    ) -> ValueEq<Add<A, B>, Add<B, A>>
    where N: Int
{
    unsafe {ValueEq::axiom()}
}

/// Axiom: a + (b + c) = (a + b) + c
pub fn add_associative<N, A: Term<Type = N>, B: Term<Type = N>, C: Term<Type = N>>(
    ) -> ValueEq<Add<A, Add<B, C>>, Add<Add<A, B>, C>>
    where N: Int
{
    unsafe {ValueEq::axiom()}
}

pub fn add_eq_to_right_eq<N, A: Term<Type = N>, B: Term<Type = N>, C: Term<Type = N>, D: Term<Type = N>>(
    eq: ValueEq<Add<A, C>, Add<B, D>>, a_eq_b: ValueEq<A, B>
    ) -> ValueEq<C, D>
    where N: Int {
    // c + a == a + c == b + d == d + b
    add_eq_to_left_eq(add_commutative() + eq + add_commutative(), a_eq_b)
}

// 0 + a = a
pub fn add_0_a_eq_a<N, A: Term<Type = N>>() -> ValueEq<Add<Zero<N>, A>, A>
where
    N: Int,
{
    add_commutative() + a_plus_0_eq_a()
}

// S(a) = a + S(0)
pub fn s_a_eq_a_plus_1<N, A: Term<Type = N>>() -> ValueEq<Succ<A>, Add<A, One<N>>>
    where N: Int
{
    -Succ::eq(a_plus_0_eq_a()) - a_plus_s_b_eq_s_add_a_b()
}

// S(a) + b = S(a + b)
#[allow(non_snake_case)]
pub fn s_a_plus_b_eq_s_add_a_b<N, A: Term<Type = N>, B: Term<Type = N>>(
) -> ValueEq<Add<Succ<A>, B>, Succ<Add<A, B>>>
where
    N: Int,
{
    add_commutative() + a_plus_s_b_eq_s_add_a_b() + Succ::eq(add_commutative())
}

// S(a) + b = a + S(b)
#[allow(non_snake_case)]
pub fn s_a_plus_b_eq_a_plus_s_b<N, A: Term<Type = N>, B: Term<Type = N>>(
) -> ValueEq<Add<Succ<A>, B>, Add<A, Succ<B>>>
where
    N: Int,
{
    s_a_plus_b_eq_s_add_a_b() - a_plus_s_b_eq_s_add_a_b()
}

// Sa = S(a) and Sb = S(b) => Sa + b = a + Sb
pub fn sa_eq_s_a_and_sb_eq_s_b_implies_sa_plus_b_eq_a_plus_sb<N, A: Term<Type = N>, AN: Term<Type = N>, B: Term<Type = N>, BN: Term<Type = N>>(
    an_eq_s_a: ValueEq<AN, Succ<A>>,
    bn_eq_s_b: ValueEq<BN, Succ<B>>
) -> ValueEq<Add<AN, B>, Add<A, BN>>
    where N: Int {
    Add::eq(an_eq_s_a, ValueEq::refl()) + s_a_plus_b_eq_a_plus_s_b() - Add::eq(ValueEq::refl(), bn_eq_s_b)
}

// a <= a + b if b in Uint
pub fn a_le_a_plus_b<N, A: Term<Type = N>, B: Term<Type = N>>(
    ) -> ValueLe<A, Add<A, B>>
    where N: UInt
{
    // a <= a + 0 <= a + b
    (-a_plus_0_eq_a()).le() + add_le(refl().le(), a_ge_0())
}
