use std::{ffi::OsStr, marker::PhantomData, path::Path as StdPath, path::PathBuf as StdPathBuf};

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
    /// use relabse-path::{Path, PathBuf, AbsPathBuf};
    ///
    /// let p = AbsPathBuf::try_from("/test").unwrap();
    /// assert_eq!(AbsPath::new("/test"), p.as_path());
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

    fn try_from(buf: std::path::PathBuf) -> Result<Self, Self::Error> {
        if Flavor::accepts(&buf) {
            Ok(Self {
                _flavor: PhantomData,
                inner: buf,
            })
        } else {
            Err(buf)
        }
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
