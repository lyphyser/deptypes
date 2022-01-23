/// Asserts that function T of A is pure and total, i.e. it cannot recurse infinitely or panic for any value
#[repr(transparent)]
pub struct TotalFn<T>(T);

impl_newtype! {
    impl [T] [U] TotalFn(T) where [T: Sized] [U: Sized]
}

impl<T> TotalFn<T> {
    pub unsafe fn new(v: T) -> Self{
        TotalFn(v)
    }
}
