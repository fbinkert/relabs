use crate::{flavors::PathFlavor, path::Path};

/// Internal helper to perform the zero-cost reference conversion.
///
/// # Safety
///
/// 1. Caller must ensure that the std::path::Path is actually valid for the target Flavor.
/// 2. `Path<F>` is #[repr(transparent)] around `std::path::Path` guaranteeing the same memory layout.
/// 3. The lifetime of the returned reference is the same as the lifetime of the input reference.
pub(crate) fn convert_ref<F: PathFlavor>(path: &std::path::Path) -> &Path<F> {
    debug_assert!(F::accepts(path));
    unsafe { &*(path as *const std::path::Path as *const Path<F>) }
}

/// Internal helper to perform the zero-cost *mutable* reference conversion.
///
/// # Safety
///
/// This function is safe to call. Its internal `unsafe` relies on:
/// - `Path<F>` being `#[repr(transparent)]` over `std::path::Path`.
/// - The input path actually being valid for the target `F` (checked by `F::accepts` in debug).
///
/// The usual Rust aliasing and lifetime rules for `&mut` are enforced by the type system.
pub(crate) fn convert_mut<F: PathFlavor>(path: &mut std::path::Path) -> &mut Path<F> {
    debug_assert!(F::accepts(path));
    unsafe { &mut *(path as *mut std::path::Path as *mut Path<F>) }
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
