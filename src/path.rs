use std::{ffi::OsStr, fmt, marker::PhantomData, path::Path as StdPath};

use crate::{
    errors::PathFlavorError,
    flavors::{Absolute, Any, PathFlavor, Relative},
    internal,
    pathbuf::{AbsPathBuf, RelPathBuf},
};

/// Newtype wrapper around `std::path::Path`.
#[repr(transparent)]
pub struct Path<Flavor = Any> {
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
    /// Caller must ensure `invariant` holds.
    pub(crate) fn new_trusted<P: AsRef<StdPath> + ?Sized>(path: &P) -> &Self {
        internal::convert_ref(path.as_ref())
    }

    #[inline]
    pub fn new<P: AsRef<StdPath> + ?Sized>(path: &P) -> Option<&Self> {
        let path = path.as_ref();
        Flavor::accepts(path).then(|| Self::new_trusted(path))
    }

    #[inline]
    pub fn try_new<P: AsRef<StdPath> + ?Sized>(path: &P) -> Result<&Self, PathFlavorError> {
        let path = path.as_ref();
        Self::new(path).ok_or_else(|| PathFlavorError::WrongFlavor(path.to_path_buf()))
    }

    #[inline]
    pub fn as_inner(&self) -> &StdPath {
        &self.inner
    }
}

impl<Flavor> AsRef<OsStr> for Path<Flavor> {
    #[inline]
    fn as_ref(&self) -> &OsStr {
        self.inner.as_os_str()
    }
}

impl<Flavor> AsRef<StdPath> for Path<Flavor> {
    #[inline]
    fn as_ref(&self) -> &StdPath {
        &self.inner
    }
}

// Public per-flavor wrappers.

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

impl<Flavor> fmt::Debug for Path<Flavor>
where
    Flavor: PathFlavor,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_inner().fmt(f)
    }
}

impl<Flavor: PathFlavor> PartialEq for Path<Flavor> {
    fn eq(&self, other: &Self) -> bool {
        self.inner == other.inner
    }
}
