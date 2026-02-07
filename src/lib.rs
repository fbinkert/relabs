#![doc = include_str!("../README.md")]

mod errors;
mod flavors;
mod path;
mod pathbuf;
mod traits;

#[doc(hidden)]
pub(crate) mod internal;

pub use errors::PathFlavorError;
pub use flavors::{Absolute, Any, PathFlavor, Relative};
pub use path::{AbsPath, Ancestors, AnyPath, Path, RelPath};
pub use pathbuf::{AbsPathBuf, AnyPathBuf, PathBuf, RelPathBuf};
