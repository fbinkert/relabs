# RelAbs: Typed Paths for Rust

[![Crates.io](https://img.shields.io/crates/v/relabs.svg)](https://crates.io/crates/relabs)
[![Docs.rs](https://docs.rs/relabs/badge.svg)](https://docs.rs/relabs)
![License](https://img.shields.io/badge/license-MIT-blue.svg)
[![Build Status](https://github.com/fbinkert/relabs/workflows/CI/badge.svg)](https://github.com/fbinkert/relabs/actions)
[![Downloads](https://img.shields.io/crates/d/relabs.svg)](https://crates.io/crates/relabs)

`RelAbs` is a zero-cost extension of the `std::path` module that adds new **Absolute** and **Relative** path types. It enforces path invariants in the type system, preventing directory traversal bugs and logic errors by exposing stronger semantic guarantees for operations like joining, pushing, and serialization.

## What is `RelAbs`?

`RelAbs` provides `AbsPath`/`AbsPathBuf` and `RelPath`/`RelPathBuf`. These types are like the standard library's `Path` and `PathBuf`, except their "flavor" (absolute or relative) is guaranteed by the type system.

The standard `std::path` types are semantically dynamic. A single `PathBuf` can hold an absolute path at one moment and a relative one the next. This flexibility is useful for general-purpose tools, but it creates a specific class of "silent" bugs:

- The Replacement Problem: `PathBuf::push` replaces the entire path if the input is absolute. A simple `base.push(user_input)` can accidentally redirect your logic from `/var/app/uploads` to `/etc/passwd` if the input isn't strictly validated.
- API Ambiguity: Documentation often says "Note: `base` must be absolute," but the compiler can't help you enforce it. Errors often occur far away from where the invalid path was originally introduced.
- Redundant Validation: Without typed paths, you often find yourself calling `.is_absolute()` repeatedly on the same variable just to be safe.

`RelAbs` allows you to validate your paths once at the system boundary (e.g., config loading or CLI parsing) and then manipulate them as strictly typed flavors from there on.

## Zero-Cost Integration

`RelAbs` is designed to be a "boring" library. It is a thin, `#[repr(transparent)]` wrapper around `std::path`.

- No Overhead: All validation is lexical. There are no syscalls and no extra memory allocations beyond what `std::path` requires.

- Drop-in Compatibility: Every flavored path is a valid `std::path::Path`. `RelAbs` types implement `AsRef<Path>`, meaning they work seamlessly with any existing Rust API that accepts standard paths.

- Safety: `RelAbs` relies on unsafe only for the zero-cost pointer casts between standard paths and flavored paths (e.g., `&Path` to `&AbsPath`), which is sound due to the transparent representation.

## Examples

### Construction & Validation

Validation happens only once at the boundary (construction). Host OS rules apply.

```rust
use relabs::{AbsPathBuf, RelPathBuf};

// Using TryFrom
let root = AbsPathBuf::try_from("/usr/local").unwrap();

// Using Parse (FromStr)
let config: RelPathBuf = "config/app.toml".parse().unwrap();
let logs: AbsPathBuf = "/var/log".parse().unwrap();

// Error Handling:
// Cannot create RelPath from an absolute string
assert!(RelPathBuf::try_from("/etc/hosts").is_err());
```

## Type-Safe Composition

You can only `join` or `push` a relative path onto an absolute base. This is enforced at compile time.

```rust
use relabs::{AbsPathBuf, RelPathBuf};

let mut path = "/root".parse::<AbsPathBuf>().unwrap();
let rel = "workdir".parse::<RelPathBuf>().unwrap();

// push a RelPath
path.push(rel);

// try push a relative string literal
path.try_push("rel").unwrap();

// Cannot push an absolute path.
assert!(path.try_push("/abs").is_err());
```

If you really need the standard library behavior (where absolute paths replace the base), use the explicit escape hatch `push_std`:

```rust
use relabs::AbsPathBuf;
let mut path = AbsPathBuf::try_from("/usr/local").unwrap();

// Explicitly opt-in to replacement semantics
path.push_std("/new/root");
```

### Self-Documenting Signatures

Stop writing documentation like "Note: `base` must be absolute." Let the type system enforce it.

```rust
use relabs::{AbsPath, RelPath};

fn deploy(destination: &AbsPath, assets: &RelPath) {
    // It is impossible to call this function with mixed-up paths.
    let target = destination.join(assets);
}
```

### Comparison

| Feature | **RelAbs** | `std::path` | `camino` | `relative-path` | `abs_path` |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **Scope** | **Unified (Abs & Rel)** | Unified (dynamic) | Unified (UTF-8) | Relative Only | Absolute Only |
| **Encoding** | **OS-native** | OS-native | UTF-8 only | UTF-8 | OS-native |
| **Safety** | **Compile-time** | Runtime checks | Runtime checks | Compile-time | Compile-time |
| **Integration** | **Zero-cost Wrapper** | N/A | Wrapper | Virtual Type | Wrapper |

**Why `RelAbs`**

- **vs. `std::path`**: `RelAbs` enforces path direction (absolute vs. relative) in the type system, preventing logic errors where a path is assumed to be one or the other.
- **vs. `camino`**: `RelAbs` focuses on **absolute/relative validation**, whereas `camino` focuses on **UTF-8 encoding**. `RelAbs` wraps `std::path` and supports non-UTF-8 OS paths.
- **vs. `relative-path`/`abs_path`**: These crates solve half the problem each. `RelAbs` provides a unified system where you can safely join a `RelPath` onto an `AbsPath` to get a new `AbsPath`.

## Roadmap

- [ ] `Serde` support
- [ ] Clap Integration
- [ ] Test with Miri
- [ ] Windows/Unix-specific extensions

## License

MIT
