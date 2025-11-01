pub use generativity::*;

#[cfg(feature = "super_let")]
#[cfg_attr(docsrs, doc(cfg(feature = "super_let")))]
#[macro_export]
/// Create and return a [`generativity::Guard`] with a unique brand.
///
/// This macro mirrors [`make_guard!`] but produces the guard directly instead
/// of binding it to a user-provided identifier. Because it relies on the
/// unstable `super_let` language feature, it is only available when the
/// crate's `"super_let"` feature is enabled (or through the `"nightly"`
/// feature, which enables `"super_let"`).
macro_rules! guard {
    () => {{
        super let branded_place = unsafe { $crate::guard::Id::new() };
        #[allow(unused)]
        let lifetime_brand = unsafe { $crate::guard::LifetimeBrand::new(&branded_place) };
        unsafe { $crate::guard::Guard::new(branded_place) }
    }};
}
