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
    //
    debug_assert!(<<L as CanJoin<R>>::Output as PathFlavor>::accepts(&joined));
    PathBuf::new_trusted(joined)
}

/// Internal helper to perform the zero-cost reference conversion.
///
/// # Safety
///
/// 1. Caller must ensure that the std::path::Path is actually valid for the target Flavor.
/// 2. `Path<F>` is #[repr(transparent)] around `std::path::Path` guarnteeing the same memory layout.
/// 3. The lifetime of the returned reference is the same as the lifetime of the input reference.
pub(crate) fn convert_ref<F: PathFlavor>(path: &std::path::Path) -> &Path<F> {
    debug_assert!(F::accepts(path));
    unsafe { &*(path as *const std::path::Path as *const Path<F>) }
}

/// Internal helper to perform the zero-cost boxed conversion.
///
/// # Safety
///
/// 1. Caller must ensure that the std::path::Path is actually valid for the target `Flavor`.
/// 2. `Path<F>` is `#[repr(transparent)]` around `std::path::Path` guaranteeing the same memory layout.
/// 3. The allocation and metadata (for the DST) are preserved; only the type is changed.
/// 4. The resulting `Box<Path<F>>` will deallocate the same allocation as the input `Box<std::path::Path>`.
pub(crate) fn convert_box<F: PathFlavor>(path: Box<std::path::Path>) -> Box<Path<F>> {
    debug_assert!(F::accepts(path.as_ref()));
    let raw: *mut std::path::Path = Box::into_raw(path);
    unsafe { Box::from_raw(raw as *mut Path<F>) }
}
