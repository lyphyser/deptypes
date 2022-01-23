macro_rules! link_error {
    ($s:tt) => {
        extern "Rust" {
            #[link_name = concat!("\nerror: link_error! macro call reachable at runtime, with following error\nerror: ", $s)]
            fn __link_error() -> !;
        }
        unsafe {
            __link_error();
        }
    }
}
