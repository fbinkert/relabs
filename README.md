# RelAbs-path

> ⚠️ **Status: Active Development** This crate is currently in the early stages of development. APIs are subject to change.

Type-safe Relative/Absolute wrappers around Rust's `std::path::Path` and `std::path::PathBuf`. Zero-cost, zero-dependency and fully compatible with the standard library.

## Why

Standard Rust paths are "stringly typed": a `PathBuf` could be absolute, relative, or nonsense. This forces you to write runtime checks (`if path.is_absolute() { ... }`) or implicit assumptions that often lead to bugs when joining paths.

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

This crate contains a single, small unsafe operation to enable a zero-cost borrowed typed path:

```rust
/// # Safety
///
/// Caller must ensure invariant` Flavor::accepts(path)` holds.
pub(crate) unsafe fn new_unchecked(path: &StdPath) -> &Self {
    debug_assert!(Flavor::accepts(path));
    &*(path as*const StdPath as *const Self)
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
