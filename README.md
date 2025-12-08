# RelAbs

[![Crates.io](https://img.shields.io/crates/v/relabs.svg)](https://crates.io/crates/relabs)
[![Docs.rs](https://docs.rs/relabs/badge.svg)](https://docs.rs/relabs)
![License](https://img.shields.io/badge/license-MIT-blue.svg)

**Strict, compile-time validation for absolute and relative paths in Rust.**

`RelAbs` lifts the distinction between absolute and relative paths into the type system. It prevents common directory traversal bugs, logic errors, and "stringly typed" confusion by ensuring you never accidentally mix them up.

> ⚠️ **Status: Active Development** This crate is currently in the early stages of development. APIs are subject to change.

## Motivation

Standard Rust paths (`std::path::Path`/`PathBuf`) are "stringly typed". A value may be absolute, relative, or nonsense. This forces you to rely on repetitive runtime checks or, worse, implicit assumptions.

`RelAbs` introduces **flavors** to encode invariants in the type system.

## Flavors: Typed Paths

Core types:

- `AbsPath`, `AbsPathBuf` – paths that are guaranteed to be **absolute**.
- `RelPath`, `RelPathBuf` – paths that are guaranteed to be **relative**.
- `Path<Any>`, `AnyPathBuf` – unconstrained, analogous to `std::path::Path` / `PathBuf`.

All flavored types are zero-cost wrappers.

### Constructing typed paths

```rust
use relabs::{AbsPath, RelPath, AbsPathBuf, RelPathBuf};

// Fallible construction from &str / &Path
let root: &AbsPath = AbsPath::try_new("/var/www")?;
let rel : &RelPath = RelPath::try_new("static/app.css")?;

// Owned variants
let abs_buf = AbsPathBuf::try_from("/etc/passwd")?;
let rel_buf = RelPathBuf::try_from("src/lib.rs")?;

```

If the invariant doesn’t hold (e.g. constructing `AbsPath` from a relative string), construction fails instead of silently accepting it.

## Typed Composition (`push` / `join`)

For flavored paths, composition is typed:

- `AbsPath` + `RelPath` → `AbsPathBuf`
- `RelPath` + `RelPath` → `RelPathBuf`

This avoids relying on the overloaded semantics of `PathBuf::push` / `Path::join` (where passing an absolute RHS replaces the base). For **flavored** paths, `push` and `join` are append-only and only accept **relative** components.

```rust
use relabs::{RelPathBuf, AbsPathBuf, RelPath, AbsPath};

// Relative base
let mut work_dir = RelPathBuf::try_from("projects/rust").unwrap();

// Typed append: only RelPath is accepted
work_dir.push(RelPath::try_new("src").unwrap());

// Absolute base
let root = AbsPath::try_new("/var/www").unwrap();

// join: AbsPath + RelPath -> AbsPathBuf
let full = root.join(RelPath::try_new("static").unwrap());
assert_eq!(full.as_path(), AbsPath::try_new("/var/www/static").unwrap());

// These do not compile:
// work_dir.push(AbsPath::try_new("/etc/passwd").unwrap());
// root.join(AbsPath::try_new("/etc/passwd").unwrap());
```

You cannot “accidentally replace the base” just by passing an absolute path. The type system rules it out.

### Escape hatch: typed `push_std`/`join_std`

If you explicitly want the standard library semantics (where an absolute RHS can replace the base), `RelAbs` provides the `push_std` and `join_std` methods.
These methods are still fully typed and preserve the flavor invariant (`AbsPathBuf` remains absolute, `RelPathBuf` remains relative, etc.).

Example:

```rust
use relabs::AbsPathBuf;

let mut path = AbsPathBuf::try_from("/var/www")?;

// Std-like semantics: absolute RHS replaces the base,
// relative RHS is appended, while the result stays `AbsPathBuf`.
path.push_std("/etc/passwd");
assert_eq!(path.as_std(), std::path::Path::new("/etc/passwd"));
```

This keeps the default push / join behavior safe and predictable, while still making it possible to opt into std-like behavior when you really want it.

## Self-Documenting APIs

With flavors, signatures communicate intent.

```rust
use relabs::{AbsPath, RelPath};

fn init_workspace(root: &AbsPath, config: &RelPath) {
    // `root` is guaranteed absolute
    // `config` is guaranteed relative
}
```

No manual `is_absolute` / `is_relative` checks needed.

## Batteries Included

`RelAbs` is designed to be a drop-in replacement for `std::path::Path` and `PathBuf` at your application's IO boundaries.

## Key Features

- **Zero-Cost:** `RelPath` and `AbsPath` are `#[repr(transparent)]` wrappers around `std::path::Path`. No memory overhead.
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
