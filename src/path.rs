use std::{marker::PhantomData, path::Path as StdPath};

use crate::flavor::{Absolute, PathFlavor, Raw};

/// Newtype wrapper around `std::path::Path`.
#[repr(transparent)]
pub struct Path<F = Raw> {
    _flavor: PhantomData<F>,
    inner: StdPath,
}

/// Path that is absolute.
pub type AbsPath = Path<Absolute>;

impl<F: PathFlavor> Path<F> {}
