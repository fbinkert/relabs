# RelAbs-path

> ⚠️ **Status: Active Development** This crate is currently in the early stages of development. APIs are subject to change.

Type-safe Relative/Absolute wrappers around Rust's `std::path::Path` and `std::path::PathBuf`. Zero-cost, zero-dependency and fully compatible with the standard library.

## Why

Standard Rust paths are "stringly typed". A `PathBuf` could be absolute, relative, or nonsense. This forces you to write runtime checks (`if path.is_absolute() { ... }`) or implicit assumptions that often lead to bugs when joining paths.

Typed Paths moves these checks to the boundary. Once you have an `AbsPathBuf`, you know that it is absolute.

```rust
// Before (Std)
fn load_config(base: &Path, rel: &Path) {
    // Runtime check required, or silent bugs if 'rel' is actually absolute
    if rel.is_absolute() { panic!("Expected relative path!"); }
    let p = base.join(rel); 
}

// After (Relabs)
fn load_config(base: &AbsPath, rel: &RelPath) {
    // Compiler guarantees 'base' is absolute and 'rel' is relative.
    // No runtime checks needed.
    let p = base.join(rel); 
}
```

## Key Features

- **Zero-Cost Abstractions:** Uses `#[repr(transparent)]` to guarantee the same memory layout as `std::path::PathBuf`.
- **Compile-Time Safety:** Prevents logic errors (e.g., joining two absolute paths) via trait bounds.
- **Zero Dependencies:** Lightweight implementation relying only on std.
- **Sealed Traits:** Uses the Sealed Trait pattern to control the "Flavor" ecosystem.

## Safety

This crate contains a single, small unsafe operation to enable a zero-cost reference conversion:

```rust
/// Internal helper to perform the zero-cost reference conversion.
///
/// # Safety
///
/// 1. Caller must ensure that the `std::path::Path` is actually valid for the target Flavor.
/// 2. `Path<F>` is `#[repr(transparent)]` around `std::path::Path` guaranteeing the same memory layout.
/// 3. The lifetime of the returned reference is the same as the lifetime of the input reference.
pub(crate) fn convert_ref<F: PathFlavor>(path: &std::path::Path) -> &Path<F> {
    unsafe { &*(path as *const StdPath as *const Path<F>) }
}
```

All public constructors and methods that produce `&Path<Flavor>` enforce the flavor invariant before calling `new_unchecked`. A `debug_assert!` double-checks it in debug builds.

Our goal is to keep the unsafe surface minimal, well-documented, and justified. If you find a path that reaches new_unchecked without validating the invariant, please open an issue.

## Roadmap

- [ ] Complete std::path::Path API parity (metadata, ancestors, etc.).
- [ ] `Serde` support (behind a feature flag).
- [ ] Display and Debug implementations that respect flavors.
- [ ] Windows/Unix specific extensions.

## License

MIT
