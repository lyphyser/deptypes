pub mod add;
pub mod sub;
pub mod neg;
pub mod uint;

use num_traits::{CheckedAdd, CheckedDiv, CheckedMul, CheckedNeg, CheckedRem, CheckedSub};

use crate::ops::{ConstOps, Sub};
use crate::term::{value_cmp, Def, Term, Value, ValueLt};
use crate::type_eq::{refl, TypeOrdering};
use crate::var::Var;
use crate::guard::Guard;
use crate::term::{ValueEq, ValueNe};

use self::sub::{s_a_minus_s_0_eq_a, s_sub_a_s_0_eq_a};

/// A type representing a [-A, B] subset of the integers (or the whole integers)
/// Ops may either panic or wrap on overflow/underflow, so use Checked* when needed (Succ/Add/Sub/etc. use them automatically)
pub unsafe trait Int:
    Ord + ConstOps + Clone + num_traits::One + num_traits::Zero + Default
    + CheckedAdd + CheckedSub + CheckedMul + CheckedDiv + CheckedRem + CheckedNeg
    + core::ops::Add<Self, Output = Self> + core::ops::Sub<Self, Output = Self> + core::ops::Mul<Self, Output = Self> + core::ops::Div<Self, Output = Self> + core::ops::Rem<Self, Output = Self>
{
}

pub type Zero<N> = Def<N>;

#[allow(non_snake_case)]
pub fn Zero<N>() -> Value<Zero<N>>
    where N: Default {
    Def()
}

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

pub type ValueIsZero<T> = ValueEq<T, Zero<<T as Term>::Type>>;

term! {
    /// Successor of an integer
    ///
    /// Note that a value for this term can be formed even for zero for unsigned integers (for example, a Value<Succ<Pred<Zero<T>>>> can be formed by coercing a Value<Zero<T>> using a ValueEq proof)
    ///
    /// To make sure that Succ<L> is not zero, you need to require a Value<L>, not a Value<Succ<L>> (and require that L::Type: UInt)! Alternatively, if you don't require the value, you can get a ValueNe<A, Zero<T>> or ValueGt<A, Zero<T>>
    pub fn Succ(a) -> unsafe <a::Type as core::ops::Add<a::Type>>::Output
        where a::Type: CheckedAdd + crate::num_traits::One {
        a.checked_add(&crate::num_traits::One::one()).expect("Succ() overflowed")
    }
}

/// Axiom: a < S(a)
pub fn a_lt_s_a<N, A: Term<Type = N>>(
    ) -> ValueLt<A, Succ<A>>
    where N: Int
{
    unsafe {ValueLt::axiom()}
}

/// Axiom: S(a) == S(b) => a == b
pub fn succ_eq_to_eq<N, A: Term<Type = N>, B: Term<Type = N>>(
    _eq: ValueEq<Succ<A>, Succ<B>>
    ) -> ValueEq<A, B>
    where N: Int
{
    unsafe {ValueEq::axiom()} // TODO
}


pub type One<N> = Succ<Zero<N>>;

#[allow(non_snake_case)]
pub fn One<N>() -> Value<Succ<Zero<N>>>
    where N: Default + CheckedAdd + crate::num_traits::One {
    Succ(Zero())
}

pub type Pred<A> = Sub<A, One<<A as Term>::Type>>;

#[allow(non_snake_case)]
pub fn Pred<A: Term>(a: Value<A>) -> Value<Pred<A>>
    where A::Type: ConstOps + Default + CheckedAdd + crate::num_traits::One + CheckedSub {
    Sub(a, One())
}

pub fn int_pred_or_succ<'a, A: Term>(
    v: Value<A>,
) -> Result<
    Result<
        Value<Pred<A>>,
        Value<Succ<A>>,
    >,
    ValueEq<A, Zero<A::Type>>
> where
    A::Type: Int,
{
    match value_cmp(v.clone(), Zero()) {
        TypeOrdering::Eq(eq) => Err(eq),
        TypeOrdering::Lt(_lt) => {
            Ok(Err(Succ(v)))
        }
        TypeOrdering::Gt(_gt) => {
            Ok(Ok(Pred(v)))
        }
    }
}

pub fn int_as_succ_or_pred<'a, A: Term>(
    guard: Guard<'a>,
    v: Value<A>,
) -> Result<
    (Value<Var<'a, A::Type>>, Result<
        ValueEq<A, Succ<Var<'a, A::Type>>>,
        ValueEq<A, Pred<Var<'a, A::Type>>>,
    >),
    ValueEq<A, Zero<A::Type>>
> where
    A::Type: Int,
{
    match int_pred_or_succ(v) {
        Err(eq) => Err(eq),
        Ok(Err(succ)) => {
            let (var, eq) = Var::alias(guard, succ);
            // i = p(s(i)) = p(a)
            Ok((var, Err(-s_a_minus_s_0_eq_a() + Sub::eq(eq, refl()))))
        }
        Ok(Ok(pred)) => {
            let (var, eq) = Var::alias(guard, pred);
            // a == s(p(a)) == a
            Ok((var, Ok(-s_sub_a_s_0_eq_a() + Succ::eq(eq))))
        }
    }
}

macro_rules! primitive_int {
    ($($v:vis struct $S:ident($T:ty);)*) => {
        $(
            term! {
                $v fn $S<const N: $T>() -> unsafe $T {
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

            unsafe impl Int for $T {}
        )*
    }
}

primitive_int! {
    pub struct ConstU8(u8);
    pub struct ConstU16(u16);
    pub struct ConstU32(u32);
    pub struct ConstU64(u64);
    pub struct ConstU128(u128);
    pub struct ConstUsize(usize);
    pub struct ConstI8(i8);
    pub struct ConstI16(i16);
    pub struct ConstI32(i32);
    pub struct ConstI64(i64);
    pub struct ConstI128(i128);
    pub struct ConstIsize(isize);
}
