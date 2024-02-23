pub mod not;
pub mod or;
pub mod and;
pub mod xor;

use crate::{term::{Term, Value, value_eq}, term::{ValueEq, ValueNe}};

term! {
    pub const fn ConstBool<const B: bool>() -> unsafe bool {
        B
    }
}

pub type True = ConstBool<true>;
pub type False = ConstBool<false>;

#[allow(non_upper_case_globals)]
pub const True: Value<True> = ConstBool();
#[allow(non_upper_case_globals)]
pub const False: Value<False> = ConstBool();

/// Axiom (|bool| >= 2): true != false
pub fn true_ne_false() -> ValueNe<True, False> {
    unsafe {ValueNe::axiom()}
}

/// Axiom (|bool| <= 2): a != c && b != c => a == b
pub fn ne_ne_implies_eq<A: Term<Type = bool>, B: Term<Type = bool>, C: Term<Type = bool>>(_a_ne: ValueNe<A, C>, _b_ne: ValueNe<B, C>) -> ValueEq<A, B> {
    unsafe {ValueEq::axiom()}
}

/// Theorem: x != true => x == false
pub fn ne_true_implies_false<T: Term<Type = bool>>(ne: ValueNe<T, True>) -> ValueEq<T, False> {
    ne_ne_implies_eq(ne, -true_ne_false())
}

/// Theorem: x != false => x == true
pub fn ne_false_implies_true<T: Term<Type = bool>>(ne: ValueNe<T, False>) -> ValueEq<T, True> {
    ne_ne_implies_eq(ne, true_ne_false())
}

pub fn choose<B: Term<Type = bool>>(b: Value<B>) -> Result<
    ValueEq<B, True>,
    ValueEq<B, False>
> {
    match value_eq(b, True) {
        Ok(eq) => Ok(eq),
        Err(ne) => Err(ne_true_implies_false(ne))
    }
}
