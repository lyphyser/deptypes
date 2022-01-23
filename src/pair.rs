#[macro_export]
macro_rules! DPair {
    () => {};

    (
        $(#[$attrs:meta])* $vis:vis unsafe type $DPair:ident $($rest:tt)*
    ) => {
        $crate::generics_parse! {
            $crate::DPair {
                @callback [[$(#[$attrs])* $vis] $DPair]
            }
            $($rest)*
        }
    };

    (
        @callback
        $(#[$attrs:meta])* $ctx:tt
        [$($gen:tt)*] [$($arg:tt)*] [$($where:tt)*]
        = ($T:ty, $($F:tt)*);

        $($rest:tt)*
    ) => {
        $crate::DPair! {
            @rev_generics
            [$ctx [$($gen)*] [$($arg)*] [$($where)*] $T]
            [$($F)*] []
        }

        $crate::DPair! {$($rest)*}
    };

    (
        @rev_generics
        $ctx:tt
        [$token:tt $($tokens:tt)*] [$($rev:tt)*]
    ) => {
        $crate::DPair! {
            @rev_generics
            $ctx
            [$($tokens)*] [$token $($rev)*]
        }
    };

    (
        @rev_generics
        $ctx:tt
        [] $rev:tt
    ) => {
        $crate::DPair! {
            @parse_args
            $ctx
            $rev
        }
    };

    (
        @parse_args
        $ctx:tt
        [> < $($rev:tt)*]
    ) => {
        $crate::DPair! {
            @rev
            [$ctx []]
            [$($rev)*] []
        }
    };

    (
        @parse_args
        $ctx:tt
        [> $($rev:tt)*]
    ) => {
        $crate::DPair! {
            @parse_args_generics
            $ctx
            [$($rev)*] [,]
        }
    };

    (
        @parse_args
        $ctx:tt
        $rev:tt
    ) => {
        $crate::DPair! {
            @rev
            [$ctx []]
            $rev []
        }
    };

    (
        @parse_args_generics
        $ctx:tt
        [< $($rev:tt)*] $arg:tt
    ) => {
        $crate::DPair! {
            @rev
            [$ctx $arg]
            [$($rev)*] []
        }
    };

    (
        @parse_args_generics
        $ctx:tt
        [$token:tt $($rev:tt)*] [$($arg:tt)*]
    ) => {
        $crate::DPair! {
            @parse_args_generics
            $ctx
            [$($rev)*] [$token $($arg)*]
        }
    };

    (
        @rev
        $ctx:tt
        [$token:tt $($rev:tt)*] [$($F:tt)*]
    ) => {
        $crate::DPair! {
            @rev
            $ctx
            [$($rev)*] [$token $($F)*]
        }
    };

    (
        @rev
        $ctx:tt
        [] $F:tt
    ) => {
        $crate::DPair! {
            @one
            $ctx
            $F    
        }
    };

    (@one
        [
            [
                [
                    [$($struct_pre:tt)*] $DPair:ident
                ]
                [$($gen:tt)*] [$($arg:tt)*] [$($where:tt)*] $T:ty
            ]
            [$($F_arg:tt)*]
        ]
        [$($F:tt)*] 
    ) => {
        $($struct_pre)* struct $DPair $($gen)* ($crate::term::Erased<$T>, $($F)*<$($F_arg)* $crate::term::Erased<$T>>) $($where)*;

        #[allow(dead_code)]
        impl $($gen)* $DPair $($arg)*
            $($where)* {
            pub fn new<A: $crate::term::Term<Type = $T>>(a: $crate::term::Value<A>, b: $($F)*<$($F_arg)* A>) -> Self {
                unsafe {Self($crate::internal::transmute_copy(&a), $crate::internal::transmute_copy(&b))}
            }
            pub fn get<'g>(&self, _g: $crate::guard::Guard<'g>) -> (&$crate::term::Value<$crate::var::Var<'g, $T>>, &$($F)*<$($F_arg)* $crate::var::Var<'g, $T>>) {
                unsafe {($crate::internal::transmute_copy(&&self.0), $crate::internal::transmute_copy(&&self.1))}
            }
            pub fn get_mut<'g>(&mut self, _g: $crate::guard::Guard<'g>) -> (&mut $crate::term::Value<$crate::var::Var<'g, $T>>, &mut $($F)*<$($F_arg)* $crate::var::Var<'g, $T>>) {
                unsafe {($crate::internal::transmute_copy(&&mut self.0), $crate::internal::transmute_copy(&&mut self.1))}
            }
            pub fn into_inner<'g>(self, _g: $crate::guard::Guard<'g>) -> ($crate::term::Value<$crate::var::Var<'g, $T>>, $($F)*<$($F_arg)* $crate::var::Var<'g, $T>>) {
                unsafe {($crate::internal::transmute_copy(&self.0), $crate::internal::transmute_copy(&self.1))}
            }
        }

        impl $($gen)* Default for $DPair $($arg)*
            where $T: $crate::internal::Default, $($F)*<$($F_arg)* $crate::term::Def<$T>>: $crate::internal::Default {
                fn default() -> Self {
                    Self::new($crate::term::Def(), $crate::internal::Default::default())
                }
        }
    };
}

/// Must ensure that it's fine to transmute the lifetime of the Output type
#[cfg(feature = "gat")]
pub unsafe trait DPairType {
    type Output<T: crate::term::Term>;
}

/*
DPair! {
    #[cfg(feature = "gat")]   
    pub unsafe type DPair<T, F: DPairType> = (T, F::Output);
}
*/