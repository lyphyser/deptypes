use core::{hint::unreachable_unchecked, marker::PhantomData};

use crate::total::TotalFn;

/// Idris: Prelude.Basics.Not
pub struct Uninhabited<T: ?Sized>(PhantomData<fn(T) -> !>);

impl<T: ?Sized> Clone for Uninhabited<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: ?Sized> Copy for Uninhabited<T> {}

impl<T: ?Sized> core::fmt::Debug for Uninhabited<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("Uninhabited<")?;
        f.write_str(core::any::type_name::<T>())?;
        f.write_str(">")?;
        Ok(())
    }
}

#[cfg(feature = "never")]
pub type Never = !;

#[cfg(not(feature = "never"))]
pub type Never = core::convert::Infallible;

impl<T> Uninhabited<T> {
    pub const unsafe fn axiom() -> Self {
        // this should be Uninhabited(PhantomData), but we can't use that because the compiler complains about function pointers in const fns
        core::mem::transmute(())
    }

    pub fn by_contradiction(f: TotalFn<impl FnOnce(T) -> Never>) -> Uninhabited<T> {
        never_is_uninhabited().rev_map(f)
    }

    pub fn by_contradiction_rejecting_example(f: TotalFn<impl FnOnce(T) -> Uninhabited<T>>) -> Uninhabited<T>
        where T: Clone {
        uninhabited_and_value_is_uninhabited().rev_map(unsafe {TotalFn::new(|g: T| {
            (f.into_inner()(g.clone()), g)
        })})
    }

    pub fn rev_map<U>(self, _f: TotalFn<impl FnOnce(U) -> T>) -> Uninhabited<U> {
        unsafe {
            Uninhabited::axiom()
        }
    }

    pub fn impossible(self, _x: T) -> ! {
        unsafe {
            unreachable_unchecked()
        }
    }
}

pub fn never_is_uninhabited() -> Uninhabited<Never> {
    unsafe {Uninhabited::axiom()}
}

pub type Inhabited<T> = Uninhabited<Uninhabited<T>>;

impl<T> Inhabited<T> {
    pub fn from(x: T) -> Self {
        unit_is_inhabited().map(unsafe {TotalFn::new(|_u: ()| x)})
    }

    pub fn by_contradiction_giving_example(f: TotalFn<impl FnOnce(Uninhabited<T>) -> T>) -> Inhabited<T> {
        uninhabited_and_value_is_uninhabited().rev_map(unsafe {TotalFn::new(|g: Uninhabited<_>| {
            (g, f.into_inner()(g))
        })})
    }

    pub fn map<U>(self, _f: TotalFn<impl FnOnce(T) -> U>) -> Inhabited<U> {
        unsafe {Inhabited::axiom()}
    }
}

pub fn unit_is_inhabited() -> Inhabited<()> {
    unsafe {Inhabited::axiom()}
}

pub fn uninhabited_result_implies_uninhabited_ok<A, B>(e: Uninhabited<Result<A, B>>) -> Uninhabited<A> {
    e.rev_map(unsafe {TotalFn::new(|x| Ok(x))})
}

pub fn uninhabited_result_implies_uninhabited_err<A, B>(e: Uninhabited<Result<A, B>>) -> Uninhabited<B> {
    e.rev_map(unsafe {TotalFn::new(|x| Err(x))})
}

pub fn uninhabited_and_value_is_uninhabited<T>() -> Uninhabited<(Uninhabited<T>, T)> {
    Uninhabited::by_contradiction(unsafe {TotalFn::new(|f: (Uninhabited<T>, T)| {
        f.0.impossible(f.1)
    })})
}

/// Also known as the double negation of the principle of excluded middle
/// Idris: Data.Logic.Propositional.pemDN
pub fn type_has_elements_or_uninhabited<T>() -> Inhabited<Result<T, Uninhabited<T>>> {
    Inhabited::by_contradiction_giving_example(unsafe {TotalFn::new(|f: Uninhabited<_>| {
        Err(uninhabited_result_implies_uninhabited_ok(f))
    })})
}

pub fn a_or_b_and_not_a_implies_b<A, B>(a_or_b: Inhabited<Result<A, B>>, not_a: Uninhabited<A>) -> Inhabited<B> {
    a_or_b.map(unsafe {TotalFn::new(|a_or_b|
        match a_or_b {
            Ok(a) => not_a.impossible(a),
            Err(b) => b
        }
    )})
}
