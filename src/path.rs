use std::{marker::PhantomData, path::Path as StdPath};

use crate::{
    errors::PathFlavorError,
    flavors::{Absolute, PathFlavor, Raw, Relative},
    internal,
    pathbuf::AbsPathBuf,
};

/// Newtype wrapper around `std::path::Path`.
#[repr(transparent)]
pub struct Path<Flavor = Raw> {
    _flavor: PhantomData<Flavor>,
    inner: StdPath,
}

/// Borrowed, typed, absolute path ('Path<Absolute>').
///
/// Invariant: 'Path::is_absolute()' must be true.
pub type AbsPath = Path<Absolute>;

/// Borrowed, typed, relative path ('Path<Relative>').
///
/// Invariant: 'Path::is_relative()' must be true.
pub type RelPath = Path<Relative>;

impl<Flavor> Path<Flavor>
where
    Flavor: PathFlavor,
{
    #[inline]
    pub fn new<P: AsRef<StdPath> + ?Sized>(path: &P) -> Option<&Self> {
        let path = path.as_ref();
        Flavor::accepts(path).then(|| internal::convert_ref(path))
    }

    #[inline]
    pub fn try_new<P: AsRef<StdPath> + ?Sized>(path: &P) -> Result<&Self, PathFlavorError> {
        let path = path.as_ref();
        Self::new(path).ok_or_else(|| PathFlavorError::WrongFlavor(path.to_path_buf()))
    }

    pub fn as_inner(&self) -> &StdPath {
        &self.inner
    }
}

// Public per-flavor wrappers for flavor-specific documentation.

impl Path<Absolute> {
    /// Joins a relative path onto this absolute path.
    ///
    /// The result remains absolute.
    pub fn join(&self, rhs: &RelPath) -> AbsPathBuf {
        internal::join_impl(self, rhs)
    }
}
