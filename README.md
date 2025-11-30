# relabs-path

> ⚠️ **Status: Active Development** This crate is currently in the early stages of development. APIs are subject to change.

Zero-cost, zero-dependency, type-safe wrappers around Rust's `std::path::Path` and `std::path::PathBuf`.

`relabs-path` leverages Rust's type system to enforce path invariants at compile time. It provides Newtype wrappers around `std::path::Path` and `std::path::PathBuf` to track whether a path is absolute, relative without any runtime overhead and while remaining fully compatible with the standard library.

## Why

Standard Rust paths are "stringly typed": a `PathBuf` could be absolute, relative, or nonsense. This forces you to write runtime checks (`if path.is_absolute() { ... }`) or implicit assumptions that often lead to bugs when joining paths.

Typed Paths moves these checks to the boundary. Once you have an `AbsPathBuf`, you know that it is absolute.

## Key Features

- **Zero-Cost Abstractions:** Uses `#[repr(transparent)]` to guarantee the same memory layout as `std::path::PathBuf`.
- **Compile-Time Safety:** Prevents logic errors (e.g., joining two absolute paths) via trait bounds.
- **Zero Dependencies:** Lightweight implementation relying only on std.
- **Sealed Traits:** Uses the Sealed Trait pattern to control the "Flavor" ecosystem.

## Roadmap

- [ ] Complete std::path::Path API parity (metadata, ancestors, etc.).
- [ ] `Serde` support (behind a feature flag).
- [ ] Display and Debug implementations that respect flavors.
- [ ] Windows/Unix specific extensions.

## License

MIT
