pub mod add;

use crate::term::{Term, Value};
use crate::var::Var;
use crate::guard::Guard;
use crate::term::{ValueEq, ValueNe};

use core::ops;

// Asserts that:
// A + 0 = A
// A + B = B + A
// A + (B + C) = (A + B) + B
pub unsafe trait WellBehavedUInt:
    crate::num_traits::Zero
    + crate::num_traits::One
    + core::ops::Add<Self, Output = Self>
    + core::ops::Sub<Self, Output = Self>
{
}

pub type Zero<N> = crate::term::Def<N>;

term! {
    pub fn Succ(a) -> <a::Type as core::ops::Add<a::Type>>::Output
        where a::Type: ops::Add<a::Type> + crate::num_traits::One {
        a + crate::num_traits::One::one()
    }
}

pub type One<N> = Succ<Zero<N>>;

/// like check_value(v, Zero) but we use is_zero instead of equality
pub fn is_zero<A: Term>(v: &Value<A>) -> Result<ValueEq<A, Zero<A::Type>>, ValueNe<A, Zero<A::Type>>>
where
    A::Type: crate::num_traits::Zero,
{
    if <A::Type as crate::num_traits::Zero>::is_zero(v) {
        Ok(unsafe {ValueEq::axiom()})
    } else {
        Err(unsafe {ValueNe::axiom()})
    }
}

pub fn ne_zero_is_succ<'a, A: Term>(_ne: ValueNe<A, Zero<A::Type>>, _g: Guard<'a>) -> ValueEq<A, Succ<Var<'a, A::Type>>> {
    unsafe {ValueEq::axiom()}
}

pub fn value_of_succ<A: Term, B: Term<Type = A::Type>>(_eq: ValueEq<A, Succ<B>>, v: Value<A>) -> Value<B>
    where A::Type: core::ops::Sub<A::Type, Output = A::Type> + crate::num_traits::One {
    unsafe {Value::new_unchecked(v.into_inner() - crate::num_traits::One::one())}
}

pub fn uint_as_succ<'a, A: Term>(
    guard: Guard<'a>,
    v: Value<A>,
) -> Result<(Value<Var<'a, A::Type>>, ValueEq<A, Succ<Var<'a, A::Type>>>), ValueEq<A, Zero<A::Type>>>
where
    A::Type: crate::num_traits::Zero + crate::num_traits::One + core::ops::Sub<A::Type, Output = A::Type>,
{
    match is_zero(&v) {
        Ok(eq) => Err(eq),
        Err(ne) => {
            let eq = ne_zero_is_succ(ne, guard);
            let value = value_of_succ(eq, v);
            Ok((value, eq))
        }
    }
}

macro_rules! primitive_uint {
    ($($v:vis struct $S:ident($T:ty);)*) => {
        $(
            term! {
                $v fn $S<const N: $T>() -> $T {
                    N
                }
            }

            impl $S<0> {
                pub fn const_zero_is_zero() -> ValueEq<$S<0>, Zero::<usize>> {
                    unsafe {ValueEq::axiom()}
                }
            }

            impl $S<1> {
                pub fn const_one_is_one() -> ValueEq<$S<1>, One::<usize>> {
                    unsafe {ValueEq::axiom()}
                }
            }

            unsafe impl WellBehavedUInt for $T {}
        )*
    }
}

primitive_uint! {
    pub struct ConstU8(u8);
    pub struct ConstU16(u16);
    pub struct ConstU32(u32);
    pub struct ConstU64(u64);
    pub struct ConstU128(u128);
    pub struct ConstUsize(usize);
}
