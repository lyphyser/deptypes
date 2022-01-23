use crate::term::{Term, ValueEq, ValueLt, ValueLe};
use crate::ops::Add;

use super::{Zero, One, Succ, WellBehavedUInt};

// a + 0 = a
pub fn a_plus_0_eq_a<N, A: Term<Type = N>>() -> ValueEq<Add<A, Zero<N>>, A>
where
    N: WellBehavedUInt,
{
    unsafe {ValueEq::axiom()}
}

// a + S(b) = S(a + b)
#[allow(non_snake_case)]
pub fn a_plus_s_b_eq_s_add_a_b<N, A: Term<Type = N>, B: Term<Type = N>>(
) -> ValueEq<Add<A, Succ<B>>, Succ<Add<A,B>>>
where
    N: WellBehavedUInt,
{
    unsafe {ValueEq::axiom()}
}

// a + b = b + a
pub fn add_commutative<N, A: Term<Type = N>, B: Term<Type = N>>() -> ValueEq<Add<A, B>, Add<B, A>>
where
    N: WellBehavedUInt,
{
    unsafe {ValueEq::axiom()}
}

// a + (b + c) = (a + b) + c
pub fn add_associative<N, A: Term<Type = N>, B: Term<Type = N>, C: Term<Type = N>>(
) -> ValueEq<Add<A, Add<B, C>>, Add<Add<A, B>, C>>
where
    N: WellBehavedUInt,
{
    unsafe {ValueEq::axiom()}
}

// 0 + a = a
pub fn add_0_a_eq_a<N, A: Term<Type = N>>() -> ValueEq<Add<Zero<N>, A>, A>
where
    N: WellBehavedUInt,
{
    add_commutative() + a_plus_0_eq_a()
}

// S(a) = a + S(0)
pub fn s_a_eq_a_plus_1<N, A: Term<Type = N>>() -> ValueEq<Succ<A>, Add<A, One<N>>>
    where N: WellBehavedUInt
{
    -Succ::eq(a_plus_0_eq_a()) - a_plus_s_b_eq_s_add_a_b()
}

// S(a) + b = S(a + b)
#[allow(non_snake_case)]
pub fn s_a_plus_b_eq_s_add_a_b<N, A: Term<Type = N>, B: Term<Type = N>>(
) -> ValueEq<Add<Succ<A>, B>, Succ<Add<A, B>>>
where
    N: WellBehavedUInt,
{
    add_commutative() + a_plus_s_b_eq_s_add_a_b() + Succ::eq(add_commutative())
}

// S(a) + b = a + S(b)
#[allow(non_snake_case)]
pub fn s_a_plus_b_eq_a_plus_s_b<N, A: Term<Type = N>, B: Term<Type = N>>(
) -> ValueEq<Add<Succ<A>, B>, Add<A, Succ<B>>>
where
    N: WellBehavedUInt,
{
    s_a_plus_b_eq_s_add_a_b() - a_plus_s_b_eq_s_add_a_b()
}

// Sa = S(a) and Sb = S(b) => Sa + b = a + Sb
pub fn sa_eq_s_a_and_sb_eq_s_b_implies_sa_plus_b_eq_a_plus_sb<N, A: Term<Type = N>, AN: Term<Type = N>, B: Term<Type = N>, BN: Term<Type = N>>(
    an_eq_s_a: ValueEq<AN, Succ<A>>,
    bn_eq_s_b: ValueEq<BN, Succ<B>>
) -> ValueEq<Add<AN, B>, Add<A, BN>>
    where N: WellBehavedUInt {
    Add::eq(an_eq_s_a, ValueEq::refl()) + s_a_plus_b_eq_a_plus_s_b() - Add::eq(ValueEq::refl(), bn_eq_s_b)
}

// a < S(a)
pub fn a_lt_s_a<N, A: Term<Type = N>>() -> ValueLt<A, Succ<A>>
where
    N: WellBehavedUInt
{
    unsafe {ValueLt::axiom()}
}

// a <= a + b
pub fn a_le_a_plus_b<N, A: Term<Type = N>, B: Term<Type = N>>() -> ValueLe<A, Add<A, B>>
where
    N: WellBehavedUInt
{
    unsafe {ValueLe::axiom()}
}
