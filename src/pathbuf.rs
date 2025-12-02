use std::{
    ffi::OsStr,
    fmt,
    marker::PhantomData,
    path::{Path as StdPath, PathBuf as StdPathBuf},
};

use crate::{
    flavors::{Absolute, Any, PathFlavor, Relative},
    internal,
    path::{Path, RelPath},
};

/// Newtype wrapper around `std::path::PathBuf`.
#[repr(transparent)]
pub struct PathBuf<Flavor = Any> {
    _flavor: PhantomData<Flavor>,
    inner: StdPathBuf,
}

/// Owned, typed, absolute path ('PathBuf<Absolute>').
///
/// Invariant: 'Path::is_absolute()' must be true.
pub type AbsPathBuf = PathBuf<Absolute>;

/// Owned, typed, relative path ('PathBuf<Relative>').
///
/// Invariant: 'Path::is_is_relative()' must be true.
pub type RelPathBuf = PathBuf<Relative>;

impl<Flavor> PathBuf<Flavor>
where
    Flavor: PathFlavor,
{
    /// Create a new [`PathBuf<Flavor>`] from a `std::path::PathBuf` withour validating the invariant.
    /// Caller must ensure `invariant` holds.
    pub(crate) fn new_trusted(path: std::path::PathBuf) -> Self {
        debug_assert!(Flavor::accepts(&path));
        Self {
            _flavor: PhantomData,
            inner: path,
        }
    }

    /// Coerces to a [`Path<Flavor>`] slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use relabs::{AbsPath, PathBuf, AbsPathBuf};
    ///
    /// let p = AbsPathBuf::try_from("/test").unwrap();
    /// assert_eq!(AbsPath::new("/test").unwrap(), p.as_path());
    /// ```
    #[inline]
    pub fn as_path(&self) -> &Path<Flavor> {
        internal::convert_ref(&self.inner)
    }

    #[must_use]
    #[inline]
    pub fn into_inner(self) -> StdPathBuf {
        self.inner
    }

    #[inline]
    pub fn push(&mut self, rhs: &RelPath) {
        self.inner.push(rhs.as_inner());
    }

    /// Replaces the path with the given path.
    #[inline]
    pub fn set<P: AsRef<Path>>(&mut self, new: P) {
        self.inner = new.as_ref().as_inner().to_path_buf();
    }
}

// Public per-flavor wrappers.

impl PathBuf {
    #[inline]
    pub fn new() -> Self {
        Self::new_trusted(std::path::PathBuf::new())
    }
}

impl Default for PathBuf<Any> {
    fn default() -> Self {
        Self {
            _flavor: PhantomData,
            inner: StdPathBuf::default(),
        }
    }
}

impl<Flavor> TryFrom<std::path::PathBuf> for PathBuf<Flavor>
where
    Flavor: PathFlavor,
{
    type Error = std::path::PathBuf;

    fn try_from(path: std::path::PathBuf) -> Result<Self, Self::Error> {
        if Flavor::accepts(&path) {
            Ok(Self::new_trusted(path))
        } else {
            Err(path)
        }
    }
}

impl<Flavor> TryFrom<&std::path::Path> for PathBuf<Flavor>
where
    Flavor: PathFlavor,
{
    type Error = StdPathBuf;

    fn try_from(path: &std::path::Path) -> Result<Self, Self::Error> {
        Self::try_from(path.to_path_buf())
    }
}

impl<Flavor> TryFrom<&str> for PathBuf<Flavor>
where
    Flavor: PathFlavor,
{
    type Error = StdPathBuf;

    fn try_from(s: &str) -> Result<Self, Self::Error> {
        // TODO: We should probably just use `relabs::PathBuf::from(s)` directly.
        Self::try_from(std::path::PathBuf::from(s))
    }
}

impl<Flavor> TryFrom<String> for PathBuf<Flavor>
where
    Flavor: PathFlavor,
{
    type Error = StdPathBuf;

    fn try_from(s: String) -> Result<Self, Self::Error> {
        // TODO: We should probably just use `relabs::PathBuf::from(s)` directly.
        Self::try_from(std::path::PathBuf::from(s))
    }
}

impl<Flavor> AsRef<OsStr> for PathBuf<Flavor> {
    #[inline]
    fn as_ref(&self) -> &OsStr {
        self.inner.as_os_str()
    }
}

impl<Flavor> AsRef<StdPath> for PathBuf<Flavor> {
    #[inline]
    fn as_ref(&self) -> &StdPath {
        &self.inner
    }
}

impl<Flavor> fmt::Debug for PathBuf<Flavor>
where
    Flavor: PathFlavor,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

impl<Flavor: PathFlavor> PartialEq for PathBuf<Flavor> {
    fn eq(&self, other: &Self) -> bool {
        self.inner == other.inner
    }
}
