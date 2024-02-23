use crate::term::{Term, Value};
use core::num::{Wrapping, Saturating};

/// Asserts that all core::ops traits that are implemented are a constant function of the arguments (or panic)
/// Meaning that for two sequences of arguments which are equal (according to Eq or TotalCmp for floats), then the results are also equal, if neither panics
pub unsafe trait ConstOps {}

macro_rules! impl_const_ops {
    ($($T:ty)*) => {
        $(unsafe impl ConstOps for $T {})*
    };
    (@int $($T:ty)*) => {
        $(impl_const_ops! {$T Wrapping<$T> Saturating<$T>})*
    }
}

impl_const_ops! {
    ()
    bool char    
    f32 f64
}

impl_const_ops! {
    @int 
    u8 u16 u32 u64 u128 usize
    i8 i16 i32 i64 i128 isize
}

#[cfg(feature = "never")]
impl_const_ops! {!}

macro_rules! impl_op2 {
    ($($term:ident = $op:ident::$func:ident)*) => {
        $(
            term! {
                /// Term that represents the arithmetic operation on the base type and whose evalutations just call the base type operation
                pub fn $term(a, b) -> unsafe <a::Type as core::ops::$op<b::Type>>::Output
                where a::Type: core::ops::$op<b::Type> + ConstOps {
                    core::ops::$op::$func(a, b)
                }
            }

            impl<A: Term, B: Term> core::ops::$op<Value<B>> for Value<A>
                where A::Type: core::ops::$op<B::Type> + ConstOps {
                type Output = Value<$term<A, B>>;

                fn $func(self, b: Value<B>) -> Self::Output {
                    $term(self, b)
                }
            }
        )*
    };
}

macro_rules! impl_op2_overflowing {
    ($($xterm:ident $term:ident = $op:ident::$func:ident $cop:ident::$cfunc:ident)*) => {
        $(
            term! {
                /// Term that represents the arithmetic operation on the base type and whose evalutations just call the base type operation
                ///
                /// For primitive integers, this may be the operation on mathematical integers or on the Z mod 2**b ring depending on whether overflow checks are on or not.
                pub fn $xterm(a, b) -> unsafe <a::Type as core::ops::$op<b::Type>>::Output
                where a::Type: core::ops::$op<b::Type> + ConstOps {
                    core::ops::$op::$func(a, b)
                }
            }

            term! {
                /// Term that represents the arithmetic operation on mathematical integers and whose evaluations always panics on overflow of the base type
                pub fn $term(a, b) -> unsafe a::Type
                where b: Term<Type = a::Type>, a::Type: num_traits::ops::checked::$cop + ConstOps {
                    num_traits::ops::checked::$cop::$cfunc(&a, &b).expect("Overflow in arithmetic operation in term evaluation")
                }
            }

            impl<A: Term, B: Term<Type = A::Type>> core::ops::$op<Value<B>> for Value<A>
                where A::Type: num_traits::ops::checked::$cop + ConstOps {
                type Output = Value<$term<A, B>>;

                fn $func(self, b: Value<B>) -> Self::Output {
                    $term(self, b)
                }
            }
        )*
    };
}

macro_rules! impl_op1 {
    ($($op:ident::$func:ident)*) => {
        $(
            term! {
                pub fn $op(a) -> unsafe <a::Type as core::ops::$op>::Output
                   where a::Type: core::ops::$op + ConstOps {
                    core::ops::$op::$func(a)
                }
            }

            impl<A: Term> core::ops::$op for Value<A>
                where A::Type: core::ops::$op + ConstOps {
                type Output = Value<$op<A>>;

                fn $func(self) -> Self::Output {
                    $op(self)
                }
            }
        )*
    };
}

macro_rules! impl_op1_overflowing {
    ($($xterm:ident $term:ident = $op:ident::$func:ident $cop:ident::$cfunc:ident)*) => {
        $(
            term! {
                /// Term that represents the arithmetic operation on the base type and whose evalutations just call the base type operation
                ///
                /// For primitive integers, this may be the operation on mathematical integers or on the Z mod 2**b ring depending on whether overflow checks are on or not.
                pub fn $xterm(a) -> unsafe <a::Type as core::ops::$op>::Output
                where a::Type: core::ops::$op + ConstOps {
                    core::ops::$op::$func(a)
                }
            }

            term! {
                /// Term that represents the arithmetic operation on mathematical integers and whose evaluations always panics on overflow of the base type
                pub fn $term(a) -> unsafe a::Type
                where a::Type: num_traits::ops::checked::$cop + ConstOps {
                    num_traits::ops::checked::$cop::$cfunc(&a).expect("Overflow in arithmetic operation in term evaluation")
                }
            }

            impl<A: Term> core::ops::$op for Value<A>
                where A::Type: num_traits::ops::checked::$cop + ConstOps {
                type Output = Value<$term<A>>;

                fn $func(self) -> Self::Output {
                    $term(self)
                }
            }
        )*
    };
}

impl_op2_overflowing! {
    XAdd Add = Add::add CheckedAdd::checked_add
    XSub Sub = Sub::sub CheckedSub::checked_sub
    XMul Mul = Mul::mul CheckedMul::checked_mul
    XDiv Div = Div::div CheckedDiv::checked_div
    XRem Rem = Rem::rem CheckedRem::checked_rem
}

impl_op2! {
    And = BitAnd::bitand
    Or = BitOr::bitor
    Xor = BitXor::bitxor
}

// TODO: shl     XShl Shl = Shl::shl CheckedShl::checked_shl
// TODO: shr

impl_op1! {
    Not::not
}

impl_op1_overflowing! {
    XNeg Neg = Neg::neg CheckedNeg::checked_neg
}
