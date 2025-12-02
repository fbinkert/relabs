# RelAbs

![License](https://img.shields.io/badge/license-MIT-blue.svg)

Type-safe zero-cost relative/absolute path wrappers for Rust.

> ⚠️ **Status: Active Development** This crate is currently in the early stages of development. APIs are subject to change.

## Why

Standard Rust paths (`std::path::Path`/`PathBuf`) are "stringly typed". A `PathBuf` could be absolute, relative, or nonsense. This forces you to write repetitive runtime checks or rely on implicit assumptions.

`RelAbs` moves these checks to the system boundary. By encoding the path type (Absolute vs. Relative) into the type system, we prevent logic errors at compile time.

## The Problem

In standard Rust, joining paths requires implicit knowledge about the data:

```rust
// Standard Library Approach
fn load_config(base: &Path, rel: &Path) {
    // Runtime Risk: If 'rel' is absolute, .join() replaces 'base' entirely.
    // Boilerplate: You must manually check .is_absolute() or hope for the best.
    if rel.is_absolute() { panic!("Expected relative path!"); }
    let p = base.join(rel);
}
```

## The Solution

With `RelAbs`, the compiler enforces correctness:

```rust
use relabs::{AbsPath, RelPath};

fn load_config(base: &AbsPath, rel: &RelPath) {
    // Compile-Time Guarantee: 'base' is absolute, 'rel' is relative.
    // Zero-Cost: No runtime checks occur here.
    let p = base.join(rel);
}
```

## Key Features

- **Zero-Cost Abstractions:** Uses `#[repr(transparent)]` to guarantee the same memory layout as `std::path::PathBuf`.
- **Compile-Time Safety:** Trait bounds prevent logical errors, such as joining two absolute paths or appending an absolute path to a relative one.
- **Zero Dependencies:** Lightweight implementation relying exclusively on the standard library.
- **Ecosystem Compatibility:** Designed to interoperate seamlessly with std::fs and std::path.

## Safety

To achieve true zero-cost conversion from `&std::path::Path` to `&Path<F>`, we rely on a single, carefully isolated unsafe operation.

This crate contains a single, small unsafe operation to enable a zero-cost reference conversion:

```rust
/// Internal helper to perform the zero-cost reference conversion.
///
/// # Safety
///
/// 1. Caller must ensure that the `std::path::Path` is actually valid for the target Flavor.
/// 2. `Path<F>` is `#[repr(transparent)]` around `std::path::Path` guaranteeing the same memory layout.
pub(crate) fn convert_ref<F: PathFlavor>(path: &std::path::Path) -> &Path<F> {
    unsafe { &*(path as *const StdPath as *const Path<F>) }
}
```

All public constructors and methods that produce `&Path<F>` enforce the path invariant before delegating to internal unsafe constructors.

Our goal is to keep the unsafe surface minimal, well-documented, and justified. If you find a path that reaches new_unchecked without validating the invariant, please open an issue.

## Roadmap

- [ ] Complete std::path::Path API parity (metadata, ancestors, etc.).
- [ ] `Serde` support (behind a feature flag).
- [ ] Test with Miri
- [ ] Display and Debug implementations that respect flavors.
- [ ] Windows/Unix specific extensions.

## License

MIT
