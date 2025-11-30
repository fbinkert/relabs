use std::path::Path;

mod private {
    pub trait Sealed {}
}

pub trait PathFlavor: private::Sealed {
    /// Defines the invariant of the path flavor.
    fn accepts<P: AsRef<Path> + ?Sized>(path: &P) -> bool;
}

/// Invariant: 'Path::is_absolute()' must be true.
pub struct Absolute;
/// Invariant: 'Path::is_relative()' must be true.
pub struct Relative;
/// No invariants.
pub struct Raw;

impl private::Sealed for Absolute {}
impl private::Sealed for Relative {}
impl private::Sealed for Raw {}

impl PathFlavor for Absolute {
    fn accepts<P: AsRef<Path> + ?Sized>(path: &P) -> bool {
        path.as_ref().is_absolute()
    }
}

impl PathFlavor for Relative {
    fn accepts<P: AsRef<Path> + ?Sized>(path: &P) -> bool {
        path.as_ref().is_relative()
    }
}

impl PathFlavor for Raw {
    fn accepts<P: AsRef<Path> + ?Sized>(_: &P) -> bool {
        true
    }
}

pub trait CanJoin<Rhs: PathFlavor>: PathFlavor + private::Sealed {
    type Output: PathFlavor;
}

impl CanJoin<Relative> for Absolute {
    type Output = Absolute;
}

impl CanJoin<Relative> for Relative {
    type Output = Relative;
}
