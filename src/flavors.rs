use std::path::Path;

mod private {
    pub trait Sealed {}
}

/// A trait that defines an invariant ofr the different kinds of path flavors.
/// The flavors are:
/// - [`Absolute`]: a strictly absolute path.
/// - [`Relative`]: a strictly relative path.
/// - [`Any`]: a path with no invariants. It can either be absolute or relative.
pub trait PathFlavor: private::Sealed {
    /// Defines the invariant of the path flavor.
    fn accepts<P: AsRef<Path> + ?Sized>(path: &P) -> bool;
}

/// Invariant: [`Path::is_absolute()`] must be true.
pub struct Absolute;
/// Invariant: [`Path::is_relative()`] must be true.
pub struct Relative;
/// No invariants.
pub struct Any;

impl private::Sealed for Absolute {}
impl private::Sealed for Relative {}
impl private::Sealed for Any {}

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

impl PathFlavor for Any {
    fn accepts<P: AsRef<Path> + ?Sized>(_: &P) -> bool {
        true
    }
}

pub trait StdJoin: PathFlavor {
    type Output: PathFlavor;
}
impl StdJoin for Any {
    type Output = Self;
}
impl StdJoin for Relative {
    type Output = Self;
}
impl StdJoin for Absolute {
    type Output = Self;
}

// Standard push is disallowed for relative
pub trait StdPush: PathFlavor {}
impl StdPush for Any {}
impl StdPush for Absolute {}
