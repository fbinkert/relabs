use std::{marker::PhantomData, path::Path as StdPath};

use crate::{
    errors::PathFlavorError,
    flavors::{Absolute, PathFlavor, Raw, Relative},
    internal,
    pathbuf::AbsPathBuf,
};

/// Newtype wrapper around `std::path::Path`.
#[repr(transparent)]
pub struct Path<F = Raw> {
    _flavor: PhantomData<*const F>,
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
        debug_assert!(F::accepts(path));
        unsafe { &*(path as *const StdPath as *const Self) }
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
