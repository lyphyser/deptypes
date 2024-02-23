#[macro_export]
macro_rules! impl_zst {
    (impl $([$($A:tt)*] [$($B:tt)*])? $T:ident $(where [$($AW:tt)*][$($BW:tt)*])?) => {
        impl<$($($A)*)?> Clone for $T<$($($A)*)?>
            $(where $($AW)*)?
        {
            fn clone(&self) -> Self {
                *self
            }
        }

        impl<$($($A)*)?> Copy for $T<$($($A)*)?>
            $(where $($AW)*)?
        {}

        impl<$($($A)*, $($B)*)?> PartialOrd<$T<$($($B)*)?>> for $T<$($($A)*)?>
            $(where $($AW)*, $($BW)*)?
        {
            fn partial_cmp(&self, _other: &$T<$($($B)*)?>) -> Option<core::cmp::Ordering> {
                Some(core::cmp::Ordering::Equal)
            }

            fn lt(&self, _other: &$T<$($($B)*)?>) -> bool {
                false
            }

            fn le(&self, _other: &$T<$($($B)*)?>) -> bool {
                true
            }

            fn gt(&self, _other: &$T<$($($B)*)?>) -> bool {
                false
            }

            fn ge(&self, _other: &$T<$($($B)*)?>) -> bool {
                true
            }
        }

        impl<$($($A)*)?> Ord for $T<$($($A)*)?>
            $(where $($AW)*)?
        {
            fn cmp(&self, _other: &$T<$($($A)*)?>) -> core::cmp::Ordering {
                core::cmp::Ordering::Equal
            }
        }

        impl<$($($A)*, $($B)*)?> PartialEq<$T<$($($B)*)?>> for $T<$($($A)*)?>
            $(where $($AW)*, $($BW)*)?
        {
            fn eq(&self, _other: &$T<$($($B)*)?>) -> bool {
                true
            }

            fn ne(&self, _other: &$T<$($($B)*)?>) -> bool {
                false
            }
        }

        impl<$($($A)*)?> Eq for $T<$($($A)*)?>
            $(where $($AW)*)?
        {}

        impl<$($($A)*)?> core::hash::Hash for $T<$($($A)*)?>
            $(where $($AW)*)?
        {
            fn hash<H: core::hash::Hasher>(&self, _hasher: &mut H) {
            }
        }
    }
}
