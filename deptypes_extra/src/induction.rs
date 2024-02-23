use deptypes::int::uint::{uint_as_succ, UInt};
use deptypes::num_traits::{self, CheckedAdd};
use deptypes::term::{Term, Value, ValueEq};
use crate::total::TotalFn;
use deptypes::transmutable::{coerce, Equiv};
use deptypes::int::{Succ, Zero};
use deptypes::guard::make_guard;
use crate::uninhabited::Inhabited;

// P(0) and P(x) => P(S(x)) -> for all x P(x)

// a + 0 = 0 + a
// a + b = b + a -> a + S(b) = S(b) + a

// term -> type kind
pub trait Pred {
    type Arg;
    type Output<A: Term<Type = Self::Arg>>;

    fn pred_output_eq<A: Term<Type = Self::Arg>, B: Term<Type = Self::Arg>>(_: ValueEq<A, B>) -> Equiv<Self::Output<A>, Self::Output<B>> {
        unsafe {Equiv::axiom()}
    }
}

// 
pub trait InductiveStep<P: Pred>
    where P::Arg: CheckedAdd + num_traits::One
{
    fn call<A: Term<Type = P::Arg>>(&mut self, a: Value<A>, hyps: P::Output<A>) -> P::Output<Succ<A>>;
}

pub fn compute_by_induction<P: Pred, I: InductiveStep<P>, X: Term<Type = P::Arg>>(base: P::Output<Zero<P::Arg>>, step: &mut I, x: Value<X>) -> P::Output<X>
    where P::Arg: UInt
{
    make_guard!(g);
    match uint_as_succ(g, x) {
        Ok((xp, eq)) => {
            let hyp = compute_by_induction(base, step, xp.clone());
            let thesis = step.call(xp, hyp);
            coerce(thesis, P::pred_output_eq(-eq))
        },
        Err(eq) => {
            coerce(base, P::pred_output_eq(-eq))
        }
    }
}

pub fn prove_by_induction<P: Pred, I: InductiveStep<P>, X: Term<Type = P::Arg>>(base: P::Output<Zero<P::Arg>>, step: &mut I, x: Inhabited<Value<X>>) -> Inhabited<P::Output<X>>
    where P::Arg: UInt + Clone + num_traits::Zero
{
    x.map(unsafe {TotalFn::new(|x| compute_by_induction(base, step, x))})
}

/*
mod test {
    use core::marker::PhantomData;
    use crate::term::{Term, ValueEq};
    use crate::induction::{Pred, InductiveStep, induction};
    use crate::ops::Add;
    use crate::uint::add::{a_plus_0_eq_a, add_0_a_eq_a};

    struct AddCommutative<T, B>(PhantomData<T>, PhantomData<B>);

    impl<T, B: Term<Type = T>> Pred for AddCommutative<T, B> {
        type Arg = T;
        type Output<A: Term<Type = Self::Arg>> = ValueEq<Add<A, B>, Add<B, A>>;
    }

    fn add_commutative<A: Term, B: Term>() -> ValueEq<Add<A, B>, Add<B, A>> {
        let base = add_0_a_eq_a() + a_plus_0_eq_a();
        induction(_base, add_0_a_eq_a())
    }
}
*/
