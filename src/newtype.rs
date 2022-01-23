pub unsafe trait NewType: core::ops::Deref  {
    unsafe fn new_unchecked(x: Self::Target) -> Self;
    fn into_inner(self) -> Self::Target;
}

macro_rules! impl_newtype {
    (impl [$($A:tt)*] [$($B:tt)*] $T:ident ($V:ty) where [$($AW:tt)*] [$($BW:tt)*]) => {
        impl<$($A)*> Clone for $T<$($A)*>
            where $V: Clone, $($AW)*
        {
            fn clone(&self) -> Self {
                unsafe {Self::new_unchecked(self.0.clone())}
            }
        }

        impl<$($A)*> Copy for $T<$($A)*>
            where $V: Copy, $($AW)*
        {}

        impl<$($A)*> core::fmt::Debug for $T<$($A)*>
            where $V: core::fmt::Debug, $($AW)*
        {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                self.0.fmt(f)
            }
        }

        impl<$($A)*> core::fmt::Display for $T<$($A)*>
            where $V: core::fmt::Display, $($AW)*
        {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                self.0.fmt(f)
            }
        }

        impl<$($A)*, $($B)*> PartialOrd<$T<$($B)*>> for $T<$($A)*>
        where $V: PartialOrd<<$T<$($B)*> as core::ops::Deref>::Target>, $($AW)*, $($BW)*
        {
            fn partial_cmp(&self, other: &$T<$($B)*>) -> Option<core::cmp::Ordering> {
                self.0.partial_cmp(other)
            }

            fn lt(&self, other: &$T<$($B)*>) -> bool {
                self.0.lt(&*other)
            }

            fn le(&self, other: &$T<$($B)*>) -> bool {
                self.0.le(&*other)
            }

            fn gt(&self, other: &$T<$($B)*>) -> bool {
                self.0.gt(&*other)
            }

            fn ge(&self, other: &$T<$($B)*>) -> bool {
                self.0.ge(&*other)
            }
        }

        impl<$($A)*> Ord for $T<$($A)*>
            where $V: Ord, $($AW)*
        {
            fn cmp(&self, other: &$T<$($A)*>) -> core::cmp::Ordering {
                self.0.cmp(other)
            }
        }

        impl<$($A)*, $($B)*> PartialEq<$T<$($B)*>> for $T<$($A)*>
            where $V: PartialEq<<$T<$($B)*> as core::ops::Deref>::Target>, $($AW)*, $($BW)*
        {
            fn eq(&self, other: &$T<$($B)*>) -> bool {
                self.0.eq(&*other)
            }

            fn ne(&self, other: &$T<$($B)*>) -> bool {
                self.0.ne(&*other)
            }
        }

        impl<$($A)*> Eq for $T<$($A)*>
            where $V: Eq, $($AW)*
        {}

        impl<$($A)*> core::hash::Hash for $T<$($A)*>
            where $V: core::hash::Hash, $($AW)*
        {
            fn hash<H: core::hash::Hasher>(&self, hasher: &mut H) {
                self.0.hash(hasher);
            }
        }

        impl<$($A)*> $T<$($A)*>
        where $V: Sized, $($AW)*
        {
            pub unsafe fn new_unchecked(x: $V) -> Self{
                $T(x)
            }
        }

        impl<$($A)*> $T<$($A)*>
        where $V: Sized, $($AW)*
        {
            // TODO: any way of implementing From?
            pub fn into_inner(self) -> $V {
                self.0
            }
        }

        unsafe impl<$($A)*> $crate::newtype::NewType for $T<$($A)*>
        where $V: Sized, $($AW)*
        {
            unsafe fn new_unchecked(x: $V) -> Self {
                $T(x)
            }

            // TODO: any way of implementing From?
            fn into_inner(self) -> $V {
                self.0
            }
        }

        /*
        impl<$($A)*> From<$T<$($A)*>> for $V {
            fn from(self: $T<$($A)*>) -> Self {
                self.0
            }
        }
        */

        impl<$($A)*> core::ops::Deref for $T<$($A)*>
        where $($AW)* {
            type Target = $V;
            fn deref(&self) -> &Self::Target {
                &self.0
            }
        }
    }
}
