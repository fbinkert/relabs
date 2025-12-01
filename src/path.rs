use std::{marker::PhantomData, path::Path as StdPath};

use crate::{
    errors::PathFlavorError,
    flavors::{Absolute, PathFlavor, Raw, Relative},
    internal,
    pathbuf::{AbsPathBuf, RelPathBuf},
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
    pub fn join(&self, path: &RelPath) -> AbsPathBuf {
        internal::join_impl(self, path)
    }

    /// Tries to join a path-like value onto this absolute path.
    ///
    /// This is the fallible counterpart to [`join`]. It first validates that
    /// `path` is a relative path, and then joins it. The result remains absolute.
    pub fn try_join<P: AsRef<StdPath>>(&self, path: P) -> Result<AbsPathBuf, PathFlavorError> {
        Ok(self.join(RelPath::try_new(&path)?))
    }
}

impl Path<Relative> {
    /// Joins a relative path onto this relatvie path.
    ///
    /// The result remains relarive.
    pub fn join(&self, path: &RelPath) -> RelPathBuf {
        internal::join_impl(self, path)
    }

    /// Tries to join a path-like value onto this relative path.
    ///
    /// This is the fallible counterpart to [`join`]. It first validates that
    /// `path` is a relative path, and then joins it. The result remains relative.
    pub fn try_join<P: AsRef<StdPath>>(&self, path: P) -> Result<RelPathBuf, PathFlavorError> {
        Ok(self.join(RelPath::try_new(&path)?))
    }
}
