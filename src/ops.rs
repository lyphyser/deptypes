use crate::term::{Term, Value};

macro_rules! impl_op2 {
    ($($op:ident::$func:ident)*) => {
        $(
            term! {
                pub fn $op(a, b) -> <a::Type as core::ops::$op<b::Type>>::Output
                where a::Type: core::ops::$op<b::Type> {
                    core::ops::$op::$func(a, b)
                }
            }

            impl<A: Term, B: Term> core::ops::$op<Value<B>> for Value<A>
                where A::Type: core::ops::$op<B::Type> {
                type Output = Value<$op<A, B>>;

                fn $func(self, b: Value<B>) -> Self::Output {
                    $op(self, b)
                }
            }
        )*
    };
}

macro_rules! impl_op1 {
    ($($op:ident::$func:ident)*) => {
        $(
            term! {
                pub fn $op(a) -> <a::Type as core::ops::$op>::Output
                   where a::Type: core::ops::$op {
                    core::ops::$op::$func(a)
                }
            }

            impl<A: Term> core::ops::$op for Value<A>
                where A::Type: core::ops::$op {
                type Output = Value<$op<A>>;

                fn $func(self) -> Self::Output {
                    $op(self)
                }
            }
        )*
    };
}

impl_op2! {
    Add::add
    Sub::sub
    Mul::mul
    Div::div
    Rem::rem
    Shl::shl
    Shr::shr
    BitAnd::bitand
    BitOr::bitor
    BitXor::bitxor
}

impl_op1! {
    Not::not
    Neg::neg
}
