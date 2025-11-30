use std::{marker::PhantomData, path::Path as StdPath, path::PathBuf as StdPathBuf};

use crate::{
    errors::PathFlavorError,
    flavor::{Absolute, PathFlavor, Raw},
};

/// Newtype wrapper around `std::path::Path`.
#[repr(transparent)]
pub struct Path<F = Raw> {
    _flavor: PhantomData<F>,
    inner: StdPath,
}

/// Newtype wrapper around `std::path::PathBuf`.
#[repr(transparent)]
pub struct PathBuf<F = Raw> {
    _flavor: PhantomData<F>,
    inner: StdPathBuf,
}

pub type AbsPath = Path<Absolute>;
pub type AbsPathBuf = PathBuf<Absolute>;

impl<F> Path<F>
where
    F: PathFlavor,
{
    #[inline]
    pub fn new<P: AsRef<StdPath> + ?Sized>(path: &P) -> Option<&Self> {
        let path = path.as_ref();
        F::accepts(path).then(|| unsafe { Self::new_unchecked(path) })
    }

    #[inline]
    pub fn try_new<P: AsRef<StdPath> + ?Sized>(path: &P) -> Result<&Self, PathFlavorError> {
        let path = path.as_ref();
        Self::new(path).ok_or_else(|| PathFlavorError::WrongFlavor(path.to_path_buf()))
    }

    /// # Safety
    ///
    /// Caller must ensure `p.is_absolute()` holds; otherwise this causes UB when reinterpreting.
    pub(crate) unsafe fn new_unchecked(path: &StdPath) -> &Self {
        unsafe { &*(path as *const StdPath as *const Self) }
    }
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

    pub fn as_path(&self) -> &Path<F> {
        // Safety: caller guarantees F::accepts(&self.inner)
        unsafe { Path::new_unchecked(&self.inner) }
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
