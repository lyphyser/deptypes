use core::marker::PhantomData;

use generativity::{make_guard, Guard, Id};

use crate::{kinds::{Term2S, L2S, L2S_}, int::{uint::{uint_as_succ, UInt}, Succ, Zero}, term::{Term, Value}, transmutable::coerce, var::Var};

pub fn until_err<'n, S: L2S, R>(initial: S::Type<'n>, mut body: impl for<'a, 'b> FnMut(Guard<'b>, S::Type<'a>)
    -> Result<S::Type<'b>, R>) -> R {
    make_guard!(l);
    let l = l.into();
    let mut initial = coerce(initial, S::equiv());
    loop {
        make_guard!(b);
        match until_err_inner::<S, R>(l, b, initial, &mut body) {
            Ok(next) => initial = next,
            Err(res) => break res
        }
    }
}

fn until_err_inner<'l, 'g, S: L2S, R>(_l: Id<'l>, g: Guard<'g>, state: S::Type<'l>, mut body: impl for<'a, 'b> FnMut(Guard<'b>, S::Type<'a>)
    -> Result<S::Type<'b>, R>) -> Result<S::Type<'l>, R> {
    match body(g, state) {
        Ok(next) => {
            let next = coerce(next, S::equiv());
            Ok(next)
        }
        Err(res) => Err(res)
    }
}

pub fn repeat_to_zero<'n, S: Term2S<A::Type>, A: Term, F>(num: Value<A>, initial: S::Type<A>, body: F) -> S::Type<Zero<A::Type>>
    where A::Type: UInt, F: for<'a> FnMut(Value<Var<'a, A::Type>>, S::Type<Succ<Var<'a, A::Type>>>) -> S::Type<Var<'a, A::Type>>
{
    #[repr(C)]
    struct UntilState<'a, T, S: Term2S<T>, F>(F, S::Type<Var<'a, T>>, Value<Var<'a, T>>);

    struct UntilStateFamily<T, S: Term2S<T>, F>(PhantomData<(T, S, F)>);

    unsafe impl<T, S: Term2S<T>, F> L2S for UntilStateFamily<T, S, F>
        where for<'a> S::Type<Var<'a, T>>: Sized,
            F: for<'a> FnMut(Value<Var<'a, T>>, S::Type<Succ<Var<'a, T>>>) -> S::Type<Var<'a, T>> {
        type Type<'a> = UntilState<'a, T, S, F>;
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
