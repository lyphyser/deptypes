use core::marker::PhantomData;

use generativity::{make_guard, Guard};

use crate::{int::{uint::{uint_as_succ, UInt}, Succ, Zero}, kinds::{Term2S, L2S, L2S_}, term::{Term, Value, ValueEq}, transmutable::{coerce, Equiv}, type_eq::refl, var::Var};

pub fn until_err<'n, S: L2S, R>(initial: S::Type<'n>, mut body: impl for<'a, 'b> FnMut(Guard<'b>, S::Type<'a>)
    -> Result<S::Type<'b>, R>) -> R {
    make_guard!(l);
    let l = l.into();
    // SAFETY: this is equivalent to passing the Guard from make_guard directly
    let mut state = coerce(initial, S::equiv(unsafe {Guard::new(l)}));
    loop {
        make_guard!(b);
        match body(b, state) {
            Ok(next) => {
                // SAFETY: 'l is no longer used since the call to body consumed state that was the only user
                state = coerce(next, S::equiv(unsafe {Guard::new(l)}));
            }
            Err(res) => break res
        };
    }
}

pub fn repeat_to_zero<'n, S: Term2S<A::Type>, A: Term, F>(num: Value<A>, initial: S::Type<A>, body: F) -> S::Type<Zero<A::Type>>
    where A::Type: UInt, F: for<'a> FnMut(Value<Var<'a, A::Type>>, S::Type<Succ<Var<'a, A::Type>>>) -> S::Type<Var<'a, A::Type>>
{
    #[repr(C)]
    struct UntilState<'a, T, S: Term2S<T>, F>(F, S::Type<Var<'a, T>>, Value<Var<'a, T>>);

    impl<'a, T, S: Term2S<T>, F> UntilState<'a, T, S, F> {
        fn equiv<'b>(var_eq: ValueEq<Var<'a, T>, Var<'b, T>>) -> Equiv<UntilState<'a, T, S, F>, UntilState<'b, T, S, F>> {
            let _: (Equiv<F, F>, Equiv<S::Type<Var<'a, T>>, S::Type<Var<'b, T>>>, Equiv<Value<Var<'a, T>>, Value<Var<'b, T>>>) = (refl(), S::equiv(var_eq), Value::equiv(var_eq));
            unsafe {Equiv::axiom()}
        }
    }

    struct UntilStateFamily<T, S: Term2S<T>, F>(PhantomData<(T, S, F)>);

    // SAFETY: Considering transmute-eq to a unique lifetime, Var<'a, T> is equivalent due to Var::erase, S::Type due to Term2S definition, and Value due to Value::equiv
    impl<T, S: Term2S<T>, F> L2S for UntilStateFamily<T, S, F>
        where for<'a> S::Type<Var<'a, T>>: Sized,
            F: for<'a> FnMut(Value<Var<'a, T>>, S::Type<Succ<Var<'a, T>>>) -> S::Type<Var<'a, T>> {
        type Type<'a> = UntilState<'a, T, S, F>;

        fn equiv<'a, 'b>(b: Guard<'b>) -> Equiv<Self::Type<'a>, Self::Type<'b>> {
            UntilState::equiv(Var::erase(b))
        }
    }

    fn ue_body<'a, 'b, T, S: Term2S<T>, F>(b: Guard<'b>, UntilState(mut f, state, num): L2S_<'a, UntilStateFamily<T, S, F>>)
        -> Result<L2S_<'b, UntilStateFamily<T, S, F>>, S::Type<Zero<T>>>
        where T: UInt, for<'x> S::Type<Var<'x, T>>: Sized, S::Type<Zero<T>>: Sized,
        F: for<'x> FnMut(Value<Var<'x, T>>, S::Type<Succ<Var<'x, T>>>) -> S::Type<Var<'x, T>> {
        match uint_as_succ(b, num) {
            Ok((pred_num, eq)) => {
                let state = coerce(state, S::equiv(eq));
                let state = f(pred_num.clone(), state);
                Ok(UntilState(f, state, pred_num))
            },
            Err(empty) => {
                let state = coerce(state, S::equiv(empty));
                Err(state)
            }
        }
    }

    make_guard!(g);
    let erase = Var::erase(g);
    let initial = coerce(initial, S::equiv(erase));
    let num = coerce(num, Value::equiv(erase));
    let initial = UntilState(body, initial, num);

    until_err::<UntilStateFamily<_, _, _>, _>(initial, ue_body)
}
