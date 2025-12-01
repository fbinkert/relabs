use std::{marker::PhantomData, path::PathBuf as StdPathBuf};

use crate::{
    errors::PathFlavorError,
    flavors::{Absolute, PathFlavor, Raw},
    path::{Path, RelPath},
};

/// Newtype wrapper around `std::path::PathBuf`.
#[repr(transparent)]
pub struct PathBuf<Flavor = Raw> {
    _flavor: PhantomData<Flavor>,
    inner: StdPathBuf,
}

impl<F> PathBuf<F>
where
    F: PathFlavor,
{
    #[inline]
    pub fn try_new(path: StdPathBuf) -> Result<Self, PathFlavorError> {
        if F::accepts(&path) {
            Ok(Self {
                _flavor: PhantomData,
                inner: path,
            })
        } else {
            Err(PathFlavorError::WrongFlavor(path))
        }
    }

    /// Caller must ensure `invariant` holds.
    pub(crate) fn new_trusted(path: StdPathBuf) -> Self {
        debug_assert!(F::accepts(&path));
        Self {
            _flavor: PhantomData,
            inner: path,
        }
    }

    #[must_use]
    #[inline]
    pub fn into_inner(self) -> StdPathBuf {
        self.inner
    }

    #[inline]
    pub fn as_path(&self) -> &Path<F> {
        // Safety: relies on the type invariant that F::accepts(inner) holds; upheld by constructors
        unsafe { Path::new_unchecked(&self.inner) }
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

// Public per-flavor wrappers for flavor-specific documentation.

impl Default for PathBuf<Raw> {
    fn default() -> Self {
        Self {
            _flavor: PhantomData,
            inner: StdPathBuf::default(),
        }
    }
}

/// Owned, typed, absolute path ('PathBuf<Absolute>').
///
/// Invariant: 'Path::is_absolute()' must be true.
pub type AbsPathBuf = PathBuf<Absolute>;
