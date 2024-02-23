pub mod uninhabited;
pub mod total;
pub mod induction;

use deptypes::{bool::{choose, False, True}, guard::Guard, int::{uint::uint_as_succ, Succ, Zero}, term::{Term, Value, ValueEq}, var::Var};
use total::TotalFn;
use uninhabited::Inhabited;

pub trait Term2Term {
    type Output<T: Term>: Term;
}

pub fn bool_is_true_or_false<T: Term<Type = bool>>(hyp: Inhabited<Value<T>>) -> Inhabited<Result<ValueEq<T, True>, ValueEq<T, False>>> {
    hyp.map(unsafe {TotalFn::new(choose::<T>)})
}

pub fn uint_is_zero_or_succ<'a, T: Term<Type = u64>>(hyp: Inhabited<Value<T>>, guard: Guard<'a>) -> Inhabited<
    Result<(Value<Var<'a, T::Type>>, ValueEq<T, Succ<Var<'a, T::Type>>>), ValueEq<T, Zero<T::Type>>>
> {
    hyp.map(unsafe {TotalFn::new(|x| uint_as_succ(guard, x))})
}
