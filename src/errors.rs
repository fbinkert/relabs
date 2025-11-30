use std::path::PathBuf;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PathFlavorError {
    WrongFlavor(PathBuf),
}
