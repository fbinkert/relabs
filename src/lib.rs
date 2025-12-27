#![doc = include_str!("../README.md")]

pub mod errors;
pub(crate) mod flavors;
pub mod path;
pub mod pathbuf;

#[doc(hidden)]
pub(crate) mod internal;

pub use path::{AbsPath, AnyPath, Path, RelPath};
pub use pathbuf::{AbsPathBuf, AnyPathBuf, PathBuf, RelPathBuf};
