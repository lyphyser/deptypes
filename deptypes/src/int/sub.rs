use crate::{ops::{Add, Sub}, term::{Term, ValueEq}, type_eq::refl};

use super::{add::{a_plus_0_eq_a, a_plus_s_b_eq_s_add_a_b, add_0_a_eq_a, add_associative, add_commutative, add_eq_to_left_eq, s_a_plus_b_eq_s_add_a_b}, succ_eq_to_eq, Int, Succ, Zero};

/// Axiom (definition of subtraction): (a - b) + b = a
pub fn a_minus_b_plus_b_eq_a<N, A: Term<Type = N>, B: Term<Type = N>>(
    ) -> ValueEq<Add<Sub<A, B>, B>, A>
    where N: Int
{
    // SAFETY: this is true for mathematical integers and thus for all types that implement Int by the requirements of Int
    unsafe {ValueEq::axiom()}
}

/// Theorem: a + (b - c) = (a + b) - c
pub fn add_sub_associative<N, A: Term<Type = N>, B: Term<Type = N>, C: Term<Type = N>>(
    ) -> ValueEq<Add<A, Sub<B, C>>, Sub<Add<A, B>, C>>
    where N: Int
{
    // (a + (b - c)) + c = a + ((b - c) + c) = a + b = (a + b)  - c + c
    let lemma = -add_associative() + Add::eq(refl(), a_minus_b_plus_b_eq_a()) - a_minus_b_plus_b_eq_a();

    add_eq_to_left_eq(lemma, refl())
}

// a + b - b + b = a + b
// a + b - b + b - b = a + b - b

/// Theorem: (a + b) - b = a
#[allow(non_snake_case)]
pub fn a_plus_b_minus_b_eq_a<N, A: Term<Type = N>, B: Term<Type = N>>(
    ) -> ValueEq<Sub<Add<A, B>, B>, A>
    where N: Int
{
    // (a + b) - b == a + (b - b) == a + 0 == a
    //-add_sub_associative() + Add::eq(ValueEq::refl(), a_minus_a_eq_0()) + a_plus_0_eq_a()

    add_eq_to_left_eq(a_minus_b_plus_b_eq_a(), refl())
}

/// Theorem: a - (b + c) = (a - b) - c
pub fn sub_add_associative<N, A: Term<Type = N>, B: Term<Type = N>, C: Term<Type = N>>(
) -> ValueEq<Sub<A, Add<B, C>>, Sub<Sub<A, B>, C>>
where N: Int
{
    // a - (b + c) + (b + c) = a == a - b + b == (((a - b) - c) + c) + b == ((a - b) - c) + (c + b) = ((a - b) - c) + (b + c)
    let lemma = a_minus_b_plus_b_eq_a() - a_minus_b_plus_b_eq_a() + Add::eq(-a_minus_b_plus_b_eq_a(), refl()) - add_associative() + Add::eq(refl(), add_commutative());

    add_eq_to_left_eq(lemma, refl())
}

/// Theorem: (a - b) + c = (a + c) - b
pub fn add_sub_commutative<N, A: Term<Type = N>, B: Term<Type = N>, C: Term<Type = N>>(
) -> ValueEq<Add<Sub<A, B>, C>, Sub<Add<A, C>, B>>
where N: Int
{
    // ((a - b) + c) + b == (a - b) + (c + b) == (a - b) + (b + c) == ((a - b) + b) + c == a + c == ((a + c) - b) + b
    let lemma = -add_associative() + Add::eq(refl(), add_commutative()) + add_associative() + Add::eq(a_minus_b_plus_b_eq_a(), refl()) - a_minus_b_plus_b_eq_a();

    add_eq_to_left_eq(lemma, refl())
}

/// Theorem: a - (b - c) == a + (c - b)
pub fn a_minus_sub_b_c_eq_a_plus_sub_c_b<N, A: Term<Type = N>, B: Term<Type = N>, C: Term<Type = N>>(
    ) -> ValueEq<Sub<A, Sub<B, C>>, Add<A, Sub<C, B>>>
    where N: Int
{
    // (a - (b - c)) + ((b - c) + c) == a - (b - c) + (b - c) + c == a + c == a + ((c - b) + b) == (a + (c - b)) + b == a + (c - b) + ((b - c) + c)
    let lemma = add_associative() + Add::eq(a_minus_b_plus_b_eq_a(), refl()) + Add::eq(refl(), -a_minus_b_plus_b_eq_a()) + add_associative() + Add::eq(refl(), -a_minus_b_plus_b_eq_a());

    add_eq_to_left_eq(lemma, refl())
}

/// Theorem: a - (b - c) = (a - b) + c
pub fn sub_sub_associative<N, A: Term<Type = N>, B: Term<Type = N>, C: Term<Type = N>>(
) -> ValueEq<Sub<A, Sub<B, C>>, Add<Sub<A, B>, C>>
where N: Int
{
    // a - (b - c) == a + (c - b) == (a + c) - b == (a - b) + c
    a_minus_sub_b_c_eq_a_plus_sub_c_b() + add_sub_associative() - add_sub_commutative()
}

/// Theorem: a - a = 0
pub fn a_minus_a_eq_0<N, A: Term<Type = N>>(
    ) -> ValueEq<Sub<A, A>, Zero<N>>
    where N: Int
{
    // (a - a) + a == a == a + 0 == 0 + a
    let lemma = a_minus_b_plus_b_eq_a() - a_plus_0_eq_a() + add_commutative();

    add_eq_to_left_eq(lemma, refl())
}

/// Theorem: a - 0 = a
pub fn a_minus_0_eq_a<N, A: Term<Type = N>>(
    ) -> ValueEq<Sub<A, Zero<N>>, A>
where N: Int
{
    // a - 0 + 0 == a == a + 0
    let lemma = a_minus_b_plus_b_eq_a() - a_plus_0_eq_a();

    add_eq_to_left_eq(lemma, refl())
}

/// Theorem: S(a) - S(b) = a - b
pub fn s_a_minus_s_b_eq_a_minus_b<N, A: Term<Type = N>, B: Term<Type = N>>(
    ) -> ValueEq<Sub<Succ<A>, Succ<B>>, Sub<A, B>>
    where N: Int
{
    // S(S(a) - S(b) + b) == (S(a) - S(b)) + S(b) == S(a)
    // S(a) - S(b) + b == a
    let lemma = succ_eq_to_eq(-a_plus_s_b_eq_s_add_a_b() + a_minus_b_plus_b_eq_a());

    // S(a) - S(b) == (S(a) - S(b) + b) - b == a - b
    -a_plus_b_minus_b_eq_a() + Sub::eq(lemma, refl())
}

/// Theorem: S(a) - b = S(a - b)
#[allow(non_snake_case)]
pub fn s_a_minus_b_eq_s_sub_a_b<N, A: Term<Type = N>, B: Term<Type = N>>(
    ) -> ValueEq<Sub<Succ<A>, B>, Succ<Sub<A, B>>>
    where N: Int
{
    // S(a - b) + b == S(a - b + b) == S(a)
    let lemma = s_a_plus_b_eq_s_add_a_b() + Succ::eq(a_minus_b_plus_b_eq_a());

    // S(a) - b == S(a - b) + b - b == S(a - b)
    -Sub::eq(lemma, refl()) + a_plus_b_minus_b_eq_a()
}

/// Theorem: S(a) - S(0) = a
pub fn s_a_minus_s_0_eq_a<N, A: Term<Type = N>>(
    ) -> ValueEq<Sub<Succ<A>, Succ<Zero<N>>>, A>
    where N: Int
{
    // S(a) - S(0) == a - 0 == a
    s_a_minus_s_b_eq_a_minus_b() + a_minus_0_eq_a()
}

/// Theorem: S(a - S(b)) = a - b
pub fn s_sub_a_s_b_eq_a_minus_b<N, A: Term<Type = N>, B: Term<Type = N>>(
    ) -> ValueEq<Succ<Sub<A, Succ<B>>>, Sub<A, B>>
    where N: Int
{
    // S(a - S(b)) == S(a) - S(b) == a - b
    -s_a_minus_b_eq_s_sub_a_b() + s_a_minus_s_b_eq_a_minus_b()
}

/// Theorem: S(a - S(0)) = a
pub fn s_sub_a_s_0_eq_a<N, A: Term<Type = N>>(
    ) -> ValueEq<Succ<Sub<A, Succ<Zero<N>>>>, A>
    where N: Int
{
    // S(a - S(0)) == a - 0 == a
    s_sub_a_s_b_eq_a_minus_b() + a_minus_0_eq_a()
}

/// a - c == b - d && c == d => a == b
pub fn sub_eq_to_left_eq<N, A: Term<Type = N>, B: Term<Type = N>, C: Term<Type = N>, D: Term<Type = N>>(
    eq: ValueEq<Sub<A, C>, Sub<B, D>>,
    c_eq_d: ValueEq<C, D>
    ) -> ValueEq<A, B>
    where N: Int
{
    // a == a - c + c == b - d + d == b
    -a_minus_b_plus_b_eq_a() + Add::eq(eq, c_eq_d) + a_minus_b_plus_b_eq_a()
}

/// Theorem: a - (a - b) = b
pub fn a_minus_sub_a_b_eq_b<N, A: Term<Type = N>, B: Term<Type = N>>(
) -> ValueEq<Sub<A, Sub<A, B>>, B>
where N: Int
{
    // a - (a - b) = (a - a) + b = 0 + b = b
    sub_sub_associative() + Add::eq(a_minus_a_eq_0(), refl()) + add_0_a_eq_a()
}

/// a - c == b - d && a == b => c == d
pub fn sub_eq_to_right_eq<N, A: Term<Type = N>, B: Term<Type = N>, C: Term<Type = N>, D: Term<Type = N>>(
    eq: ValueEq<Sub<A, C>, Sub<B, D>>,
    a_eq_b: ValueEq<A, B>
    ) -> ValueEq<C, D>
    where N: Int
{
    // c == a - (a - c) == b - (b - d) == d
    -a_minus_sub_a_b_eq_b() + Sub::eq(a_eq_b, eq) + a_minus_sub_a_b_eq_b()
}
