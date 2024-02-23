use generativity::Guard;

use crate::{term::{Term, Value, ValueEq, ValueGe, ValueNe}, var::Var};

use super::{is_zero, sub::s_sub_a_s_0_eq_a, Int, Pred, Succ, Zero};

/// A type representing a [0, N] subset of the integers (or the whole nonnegative integers)
/// Ops may either panic or wrap on overflow/underflow, so use Checked* when needed (Succ/Add/Sub/etc. use them automatically)
pub unsafe trait UInt: Int {}

macro_rules! impl_uint {
    ($($T:ty)*) => {
        $(unsafe impl UInt for $T {})*
    }
}

impl_uint! {u8 u16 u32 u64 u128 usize}

/// Axiom: a >= 0 if a is UInt
pub fn a_ge_0<N, A: Term<Type = N>>(
    ) -> ValueGe<A, Zero<N>>
    where N: UInt
{
    unsafe {ValueGe::axiom()}
}

pub fn uint_pred<'a, A: Term>(
    v: Value<A>,
) -> Result<
    Value<Pred<A>>,
    ValueEq<A, Zero<A::Type>>
> where
    A::Type: UInt,
{
    match is_zero(&v) {
        Ok(eq) => Err(eq),
        Err(_ne) => {
            Ok(Pred(v))
        }
    }
}

pub fn uint_as_succ<'a, A: Term>(
    guard: Guard<'a>,
    v: Value<A>,
) -> Result<
    (Value<Var<'a, A::Type>>, ValueEq<A, Succ<Var<'a, A::Type>>>),
    ValueEq<A, Zero<A::Type>>
> where
    A::Type: UInt,
{
    match uint_pred(v) {
        Ok(pred) => {
            let (var, eq) = Var::alias(guard, pred);
            Ok((var, -s_sub_a_s_0_eq_a() + Succ::eq(eq)))
        },
        Err(eq) => Err(eq)
    }
}

pub fn ne_zero_is_succ<'a, A: Term>(_ne: ValueNe<A, Zero<A::Type>>, _g: Guard<'a>) -> ValueEq<A, Succ<Var<'a, A::Type>>>
    where A::Type: UInt {
    unsafe {ValueEq::axiom()}
}
