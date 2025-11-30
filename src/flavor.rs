use std::path::Path;

mod private {
    pub trait Sealed {}
}

pub trait PathFlavor {
    /// Defines the invariant of the path flavor.
    fn accepts<P: AsRef<Path> + ?Sized>(path: &P) -> bool;
}

pub struct Absolute;
pub struct Raw;

impl private::Sealed for Absolute {}
impl private::Sealed for Raw {}

impl PathFlavor for Absolute {
    fn accepts<P: AsRef<Path> + ?Sized>(path: &P) -> bool {
        path.as_ref().is_absolute()
    }
}

impl PathFlavor for Raw {
    fn accepts<P: AsRef<Path> + ?Sized>(_: &P) -> bool {
        true
    }
}
