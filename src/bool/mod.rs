pub mod not;

use crate::{term::{Term, Value, check_value}, term::{ValueEq, ValueNe}, uninhabited::{Inhabited}};
use crate::total::TotalFn;

term! {
    pub const fn ConstBool<const B: bool>() -> bool {
        B
    }
}

pub type True = ConstBool<true>;
pub type False = ConstBool<false>;

#[allow(non_upper_case_globals)]
pub const True: Value<True> = ConstBool();
#[allow(non_upper_case_globals)]
pub const False: Value<False> = ConstBool();

pub fn ne_true_implies_false<T: Term<Type = bool>>(_eq: ValueNe<T, True>) -> ValueEq<T, False> {
    unsafe {ValueEq::axiom()}
}

pub fn ne_false_implies_true<P, T: Term<Type = bool>>(_eq: ValueNe<T, False>) -> ValueEq<T, True> {
    unsafe {ValueEq::axiom()}
}

pub fn true_ne_false() -> ValueNe<True, False> {
    unsafe {ValueNe::axiom()}
}

pub fn choose<B: Term<Type = bool>>(b: Value<B>) -> Result<
    ValueEq<B, True>,
    ValueEq<B, False>
> {
    match check_value(b, True) {
        Ok(eq) => Ok(eq),
        Err(ne) => Err(ne_true_implies_false(ne))
    }
}

pub fn bool_is_true_or_false<T: Term<Type = bool>>(hyp: Inhabited<Value<T>>) -> Inhabited<Result<ValueEq<T, True>, ValueEq<T, False>>> {
    hyp.map(unsafe {TotalFn::new(choose::<T>)})
}
