use std::{marker::PhantomData, path::PathBuf as StdPathBuf};

use crate::{
    errors::PathFlavorError,
    flavors::{Absolute, PathFlavor, Raw},
    path::{AbsPath, Path, RelPath},
};

/// Newtype wrapper around `std::path::PathBuf`.
#[repr(transparent)]
pub struct PathBuf<F = Raw> {
    _flavor: PhantomData<F>,
    inner: StdPathBuf,
}

impl<F> PathBuf<F>
where
    F: PathFlavor,
{
    pub fn new() -> Self {
        Self {
            _flavor: PhantomData,
            inner: StdPathBuf::new(),
        }
    }

    pub fn try_new(path: StdPathBuf) -> Result<Self, PathFlavorError> {
        if F::accepts(&path) {
            // Safety: invariants was checked
            Ok(unsafe { Self::new_unchecked(path) })
        } else {
            Err(PathFlavorError::WrongFlavor(path))
        }
    }

    /// # Safety
    ///
    /// Caller must ensure `invariant` holds; otherwise this causes UB when reinterpreting.
    pub(crate) unsafe fn new_unchecked(path: StdPathBuf) -> Self {
        Self {
            _flavor: PhantomData,
            inner: path,
        }
    }

    pub fn into_inner(self) -> StdPathBuf {
        self.inner
    }

    pub fn as_inner_mut(&mut self) -> &mut StdPathBuf {
        &mut self.inner
    }

    pub fn as_path(&self) -> &Path<F> {
        // Safety: caller guarantees F::accepts(&self.inner)
        unsafe { Path::new_unchecked(&self.inner) }
    }

    #[inline]
    pub fn push(&mut self, rhs: &RelPath) {
        self.inner.push(rhs.as_inner());
    }

    /// Replaces the path with the given path.
    #[inline]
    pub fn set<P: AsRef<AbsPath>>(&mut self, new: P) {
        self.inner = new.as_ref().as_inner().to_path_buf();
    }
}

impl<F: PathFlavor> Default for PathBuf<F> {
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
