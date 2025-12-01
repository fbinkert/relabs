use std::path::Path as StdPath;

use crate::{
    flavors::{CanJoin, PathFlavor},
    path::Path,
    pathbuf::PathBuf,
};

// Generic join core restricted to flavor-compatible LHS and RHS.
#[must_use]
#[inline]
pub(crate) fn join_impl<L, R>(lhs: &Path<L>, rhs: &Path<R>) -> PathBuf<<L as CanJoin<R>>::Output>
where
    L: CanJoin<R>,
    R: PathFlavor,
{
    let joined = lhs.as_inner().join(rhs.as_inner());
    // Safety: allowed pairs guarantee the resulting flavor matches CanJoin::Output
    debug_assert!(L::accepts(&joined));
    PathBuf::new_trusted(joined)
}

/// Internal helper to perform the zero-cost reference conversion.
///
/// # Safety
///
/// 1. Caller must ensure that the std::path::Path is actually valid for the target Flavor.
/// 2. `Path<F>` is #[repr(transparent)] around `std::path::Path` guarnteeing the same memory layout.
/// 3. The lifetime of the returned reference is the same as the lifetime of the input reference.
pub(crate) fn convert_ref<F: PathFlavor>(path: &StdPath) -> &Path<F> {
    debug_assert!(F::accepts(path));
    unsafe { &*(path as *const StdPath as *const Path<F>) }
}
