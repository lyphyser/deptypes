use core::hint::unreachable_unchecked;

/// Trait to handle supposedly unreachable cases
pub trait Unreachable {
    /// SAFETY: you must make sure that the unreachable case never happens, i.e. that code paths that call unreachable() are never executed
    unsafe fn new() -> Self;

    /// Either panics (for UnreachablePanic) or causes undefined behavior (for UnreachableUnchecked)
    ///
    /// This is a safe function because new() and the UnreachableUnchecked constructor are unsafe
    fn unreachable(&self) -> !;
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(C)]
/// Assumes that the unreachable case cannot happen, resulting in undefined behavior if it does
pub struct UnreachableUnchecked(());

impl UnreachableUnchecked {
    /// SAFETY: you must make sure that the unreachable case never happens, i.e. that code paths that call unreachable() are never executed
    pub unsafe fn new() -> Self {
        Self(())
    }
}

impl Unreachable for UnreachableUnchecked {
    unsafe fn new() -> Self {
        Self(())
    }

    fn unreachable(&self) -> ! {
        unsafe { unreachable_unchecked() }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
#[repr(C)]
/// Panics if the unreachable case happens
pub struct UnreachablePanic;

impl Unreachable for UnreachablePanic {
    unsafe fn new() -> Self {
        Self
    }

    fn unreachable(&self) -> ! {
        unreachable!()
    }
}
