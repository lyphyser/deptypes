use deptypes::impl_newtype;

/// Asserts that function T of A is pure and total, i.e. it cannot recurse infinitely or panic for any value
#[repr(transparent)]
pub struct TotalFn<T>(T);

impl_newtype! {
    impl [T] [U] TotalFn(T)
}


impl<T> core::fmt::Debug for TotalFn<T>
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        f.write_str("TotalFn<")?;
        f.write_str(core::any::type_name::<T>())?;
        f.write_str(">")
    }
}

impl<T> TotalFn<T> {
    pub unsafe fn new(v: T) -> Self{
        TotalFn(v)
    }
}
