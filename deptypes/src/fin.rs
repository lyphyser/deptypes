use core::ops::AddAssign;

use num_traits::CheckedAdd;

use crate::term::{Term, Value, ValueEq, ValueLe};
use crate::transmutable::{Transm, Equiv};
use crate::ops::{Add, ConstOps};

#[repr(transparent)]
pub struct Fin<A: Term>(A::Type);

impl_newtype! {
    impl [A] [B] Fin(<A as Term>::Type) where [A: Term] [B: Term]
}

impl<A: Term> core::fmt::Debug for Fin<A>
    where A::Type: core::fmt::Debug
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        f.write_str("Fin<")?;
        f.write_str(core::any::type_name::<A>())?;
        f.write_str(">(")?;
        core::fmt::Debug::fmt(&self.0, f)?;
        f.write_str(")")
    }
}

impl<A: Term> Fin<A>
    where A::Type: PartialOrd {
    pub fn from(a: Value<A>, x: A::Type) -> Option<Fin<A>> {
        if x < a.into_inner() {
            Some(Fin(x))
        } else {
            None
        }
    }
}

impl<A: Term> Fin<A>
    where A::Type: num_traits::Zero {
    pub fn range(a: Value<A>) -> FinRange<A> {
        FinRange(num_traits::Zero::zero(), a)
    }
}

impl<A: Term, B: Term<Type = A::Type>> core::ops::Add<Fin<B>> for Fin<A>
    where A::Type: CheckedAdd + ConstOps {
    type Output = Fin<Add<A, B>>;

    fn add(self, rhs: Fin<B>) -> Self::Output {
        Fin(self.0 + rhs.0)
    }
}

impl<A: Term> Fin<A> {
    pub fn equiv<B: Term<Type = A::Type>>(_: ValueEq<A, B>) -> Equiv<Fin<A>, Fin<B>> {
        unsafe {Equiv::axiom()}
    }

    pub fn transm<B: Term<Type = A::Type>>(_: ValueLe<A, B>) -> Transm<Fin<A>, Fin<B>> {
        unsafe {Transm::axiom()}
    }
}

#[repr(C)]
pub struct FinRange<A: Term>(pub A::Type, pub Value<A>);

impl<A: Term> Iterator for FinRange<A>
    where A::Type: PartialOrd + AddAssign + num_traits::One + Clone {
    type Item = Fin<A>;

    fn next(&mut self) -> Option<Fin<A>> {
        match Fin::from(self.1.clone(), self.0.clone()) {
            Some(fin) => {
                self.0 += num_traits::One::one();
                Some(fin)
            },
            None => None
        }
    }
}
