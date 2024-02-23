use generativity::Guard;

use crate::{kinds::Term2S, term::{Def, Erased, Term, Value}, transmutable::{coerce, id_equiv, mut_equiv, ref_equiv}, var::Var};

#[repr(C)] // to support trasmutation by Term2S::equiv
pub struct DPair<T, F: Term2S<T>>(
    Value<Erased<T>>,
    F::Type<Erased<T>>,
);

macro_rules! impl_accessor {
    ($($(#[$m:meta])* $v:vis fn $fn:ident($($t:tt)*) = $equiv:ident;)*) => {
        $(
            $(#[$m])* $v fn $fn<'g>($($t)* self, g: Guard<'g>) -> (
                $($t)* Value<Var<'g, T>>,
                $($t)* F::Type<Var<'g, T>>,
            ) {
                let unerase = Var::erase(g);
                let Self(a, b) = self;
                
                let a = coerce(a, $equiv(unerase));
                let b = coerce(b, $equiv(F::equiv(unerase)));
        
                (a, b)
            }
        )*
    }
}

impl<T, F: Term2S<T>> DPair<T, F> {
    pub fn new<A: Term<Type = T>>(a: Value<A>, b: F::Type<A>) -> Self {
        let erase = unsafe {Erased::erase::<A>()};

        let a = coerce(a, erase);
        let b = coerce(b, F::equiv(erase));
        
        Self(a, b)
    }

    impl_accessor! {
        pub fn get(&) = ref_equiv;
        pub fn get_mut(&mut) = mut_equiv;
        pub fn into_inner() = id_equiv;
    }
}

impl<T, F: Term2S<T>> Default for DPair<T, F>
    where T: Default, F::Type<Def<T>>: Default,
{
    fn default() -> Self {
        Self::new(Def(), Default::default())
    }
}
