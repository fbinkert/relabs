use std::{
    borrow::Cow,
    ffi::OsStr,
    fmt::{self},
    fs, io,
    iter::FusedIterator,
    marker::PhantomData,
    path::{Components, StripPrefixError},
};

use crate::{
    errors::PathFlavorError,
    flavors::{Absolute, Any, PathFlavor, Relative, StdJoin},
    internal,
    pathbuf::PathBuf,
};

/// Newtype wrapper around `std::path::Path`.
#[repr(transparent)]
pub struct Path<Flavor = Any> {
    _flavor: PhantomData<Flavor>,
    inner: std::path::Path,
}

/// Borrowed, typed, absolute path ('Path<Absolute>').
///
/// Invariant: 'Path::is_absolute()' must be true.
pub type AbsPath = Path<Absolute>;

/// Borrowed, typed, relative path ('Path<Relative>').
///
/// Invariant: 'Path::is_relative()' must be true.
pub type RelPath = Path<Relative>;

/// Borrowed, unconstrained path ('Path<Any>').
///
/// Invariant: No invariant
pub type AnyPath = Path<Any>;

impl<Flavor> Path<Flavor>
where
    Flavor: PathFlavor,
{
    /// Caller must ensure `invariant` holds.
    pub(crate) fn new_trusted<P: AsRef<std::path::Path> + ?Sized>(path: &P) -> &Self {
        internal::convert_ref(path.as_ref())
    }

    /// Attempt to create a new [`Path`] from a reference of another type.
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// use relabs::{AbsPath, RelPath};
    ///
    /// assert!(AbsPath::try_new("foo.txt").is_err());
    /// assert!(RelPath::try_new("foo.txt").is_ok());
    /// ```
    #[inline]
    pub fn try_new<P: AsRef<std::path::Path> + ?Sized>(path: &P) -> Result<&Self, PathFlavorError> {
        let path = path.as_ref();
        Flavor::accepts(path)
            .then(|| Self::new_trusted(path))
            .ok_or_else(|| PathFlavorError::WrongFlavor(path.to_path_buf()))
    }

    #[inline]
    pub fn as_std(&self) -> &std::path::Path {
        &self.inner
    }

    /// Yields the underlying [`OsStr`] slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use relabs::Path;
    ///
    /// let os_str = Path::new("foo.txt").as_os_str();
    /// assert_eq!(os_str, std::ffi::OsStr::new("foo.txt"));
    /// ```
    #[must_use]
    #[inline]
    pub fn as_os_str(&self) -> &OsStr {
        self.inner.as_os_str()
    }

    /// Yields a [`&str`] slice if the `Path` is valid unicode.
    ///
    /// This conversion may entail doing a check for UTF-8 validity.
    /// Note that validation is performed because non-UTF-8 strings are
    /// perfectly valid for some OS.
    ///
    /// [`&str`]: str
    ///
    /// # Examples
    ///
    /// ```
    /// use relabs::Path;
    ///
    /// let path = Path::new("foo.txt");
    /// assert_eq!(path.to_str(), Some("foo.txt"));
    /// ```
    #[must_use]
    #[inline]
    pub fn to_str(&self) -> Option<&str> {
        self.inner.to_str()
    }

    /// Converts a `Path` to a [`Cow<str>`].
    ///
    /// Any non-UTF-8 sequences are replaced with
    /// [`U+FFFD REPLACEMENT CHARACTER`][U+FFFD].
    ///
    /// [U+FFFD]: super::char::REPLACEMENT_CHARACTER
    ///
    /// # Examples
    ///
    /// Calling `to_string_lossy` on a `Path` with valid unicode:
    ///
    /// ```
    /// use relabs::Path;
    ///
    /// let path = Path::new("foo.txt");
    /// assert_eq!(path.to_string_lossy(), "foo.txt");
    /// ```
    ///
    /// Had `path` contained invalid unicode, the `to_string_lossy` call might
    /// have returned `"fo�.txt"`.
    #[must_use]
    #[inline]
    pub fn to_string_lossy(&self) -> Cow<'_, str> {
        self.inner.to_string_lossy()
    }

    /// Converts a `Path` to an owned [`PathBuf`].
    ///
    /// # Examples
    ///
    /// ```
    /// use relabs::{Path, PathBuf};
    ///
    /// let path_buf = Path::new("foo.txt").to_path_buf();
    /// assert_eq!(path_buf, PathBuf::from("foo.txt"));
    /// ```
    #[must_use]
    pub fn to_path_buf(&self) -> PathBuf<Flavor> {
        PathBuf::<Flavor>::new_trusted(self.inner.to_path_buf())
    }

    /// Returns `true` if the `Path` is absolute, i.e., if it is independent of
    /// the current directory.
    ///
    /// * On Unix, a path is absolute if it starts with the root, so
    /// `is_absolute` and [`has_root`] are equivalent.
    ///
    /// * On Windows, a path is absolute if it has a prefix and starts with the
    /// root: `c:\windows` is absolute, while `c:temp` and `\temp` are not.
    ///
    /// # Examples
    ///
    /// ```
    /// use relabs::Path;
    ///
    /// assert!(!Path::new("foo.txt").is_absolute());
    /// ```
    ///
    /// [`has_root`]: Path::has_root
    #[must_use]
    #[inline]
    pub fn is_absolute(&self) -> bool {
        self.inner.is_absolute()
    }

    /// Returns `true` if the `Path` is relative, i.e., not absolute.
    ///
    /// See [`is_absolute`]'s documentation for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// use relabs::Path;
    ///
    /// assert!(Path::new("foo.txt").is_relative());
    /// ```
    ///
    /// [`is_absolute`]: Path::is_absolute
    #[must_use]
    #[inline]
    pub fn is_relative(&self) -> bool {
        self.inner.is_relative()
    }

    /// Returns `true` if the `Path` has a root.
    ///
    /// * On Unix, a path has a root if it begins with `/`.
    ///
    /// * On Windows, a path has a root if it:
    ///     * has no prefix and begins with a separator, e.g., `\windows`
    ///     * has a prefix followed by a separator, e.g., `c:\windows` but not `c:windows`
    ///     * has any non-disk prefix, e.g., `\\server\share`
    ///
    /// # Examples
    ///
    /// ```
    /// use relabs::Path;
    ///
    /// assert!(Path::new("/etc/passwd").has_root());
    /// ```
    #[must_use]
    #[inline]
    pub fn has_root(&self) -> bool {
        self.inner.has_root()
    }

    /// Returns the `Path` without its final component, if there is one.
    ///
    /// This means it returns `Some("")` for relative paths with one component.
    ///
    /// Returns [`None`] if the path terminates in a root or prefix, or if it's
    /// the empty string.
    ///
    /// # Examples
    ///
    /// ```
    /// use relabs::Path;
    ///
    /// let path = Path::new("/foo/bar");
    /// let parent = path.parent().unwrap();
    /// assert_eq!(parent, Path::new("/foo"));
    ///
    /// let grand_parent = parent.parent().unwrap();
    /// assert_eq!(grand_parent, Path::new("/"));
    /// assert_eq!(grand_parent.parent(), None);
    ///
    /// let relative_path = Path::new("foo/bar");
    /// let parent = relative_path.parent();
    /// assert_eq!(parent, Some(Path::new("foo")));
    /// let grand_parent = parent.and_then(Path::parent);
    /// assert_eq!(grand_parent, Some(Path::new("")));
    /// let great_grand_parent = grand_parent.and_then(Path::parent);
    /// assert_eq!(great_grand_parent, None);
    /// ```
    #[must_use]
    #[inline]
    pub fn parent(&self) -> Option<&Path<Flavor>> {
        self.inner.parent().map(Path::new_trusted)
    }

    /// Produces an iterator over `Path` and its ancestors.
    ///
    /// The iterator will yield the `Path` that is returned if the [`parent`] method is used zero
    /// or more times. If the [`parent`] method returns [`None`], the iterator will do likewise.
    /// The iterator will always yield at least one value, namely `Some(&self)`. Next it will yield
    /// `&self.parent()`, `&self.parent().and_then(Path::parent)` and so on.
    ///
    /// # Examples
    ///
    /// ```
    /// use relabs::Path;
    ///
    /// let mut ancestors = Path::new("/foo/bar").ancestors();
    /// assert_eq!(ancestors.next(), Some(Path::new("/foo/bar")));
    /// assert_eq!(ancestors.next(), Some(Path::new("/foo")));
    /// assert_eq!(ancestors.next(), Some(Path::new("/")));
    /// assert_eq!(ancestors.next(), None);
    ///
    /// let mut ancestors = Path::new("../foo/bar").ancestors();
    /// assert_eq!(ancestors.next(), Some(Path::new("../foo/bar")));
    /// assert_eq!(ancestors.next(), Some(Path::new("../foo")));
    /// assert_eq!(ancestors.next(), Some(Path::new("..")));
    /// assert_eq!(ancestors.next(), Some(Path::new("")));
    /// assert_eq!(ancestors.next(), None);
    /// ```
    ///
    /// [`parent`]: Path::parent
    #[inline]
    pub fn ancestors(&self) -> Ancestors<'_, Flavor> {
        Ancestors {
            _flavor: PhantomData,
            inner: self.inner.ancestors(),
        }
    }

    /// Returns the final component of the `Path`, if there is one.
    ///
    /// If the path is a normal file, this is the file name. If it's the path of a directory, this
    /// is the directory name.
    ///
    /// Returns [`None`] if the path terminates in `..`.
    ///
    /// # Examples
    ///
    /// ```
    /// use relabs::Path;
    /// use std::ffi::OsStr;
    ///
    /// assert_eq!(Some(OsStr::new("bin")), Path::new("/usr/bin/").file_name());
    /// assert_eq!(Some(OsStr::new("foo.txt")), Path::new("tmp/foo.txt").file_name());
    /// assert_eq!(Some(OsStr::new("foo.txt")), Path::new("foo.txt/.").file_name());
    /// assert_eq!(Some(OsStr::new("foo.txt")), Path::new("foo.txt/.//").file_name());
    /// assert_eq!(None, Path::new("foo.txt/..").file_name());
    /// assert_eq!(None, Path::new("/").file_name());
    /// ```
    #[must_use]
    #[inline]
    pub fn file_name(&self) -> Option<&OsStr> {
        self.inner.file_name()
    }

    /// Returns a path that, when joined onto `base`, yields `self`.
    ///
    /// # Errors
    ///
    /// If `base` is not a prefix of `self` (i.e., [`starts_with`]
    /// returns `false`), returns [`Err`].
    ///
    /// [`starts_with`]: Path::starts_with
    ///
    /// # Examples
    ///
    /// ```
    /// use relabs::{AnyPath, PathBuf, RelPath};
    ///
    /// let path = AnyPath::new("/test/haha/foo.txt");
    ///
    /// assert_eq!(path.strip_prefix("/").unwrap(), RelPath::try_new("test/haha/foo.txt").unwrap());
    /// assert_eq!(path.strip_prefix("/test").unwrap(), RelPath::try_new("haha/foo.txt").unwrap());
    /// assert_eq!(path.strip_prefix("/test/").unwrap(), RelPath::try_new("haha/foo.txt").unwrap());
    /// assert_eq!(path.strip_prefix("/test/haha/foo.txt").unwrap(), RelPath::try_new("").unwrap());
    /// assert_eq!(path.strip_prefix("/test/haha/foo.txt/").unwrap(), RelPath::try_new("").unwrap());
    ///
    /// assert!(path.strip_prefix("test").is_err());
    /// assert!(path.strip_prefix("/te").is_err());
    /// assert!(path.strip_prefix("/haha").is_err());
    ///
    /// let prefix = PathBuf::from("/test/");
    /// assert_eq!(path.strip_prefix(prefix).unwrap(), RelPath::try_new("haha/foo.txt").unwrap());
    /// ```
    pub fn strip_prefix<P>(&self, base: P) -> Result<&RelPath, StripPrefixError>
    where
        P: AsRef<std::path::Path>,
    {
        self.inner
            .strip_prefix(base.as_ref())
            .map(RelPath::new_trusted)
    }

    /// Determines whether `base` is a prefix of `self`.
    ///
    /// Only considers whole path components to match.
    ///
    /// # Examples
    ///
    /// ```
    /// use relabs::Path;
    ///
    /// let path = Path::new("/etc/passwd");
    ///
    /// assert!(path.starts_with("/etc"));
    /// assert!(path.starts_with("/etc/"));
    /// assert!(path.starts_with("/etc/passwd"));
    /// assert!(path.starts_with("/etc/passwd/")); // extra slash is okay
    /// assert!(path.starts_with("/etc/passwd///")); // multiple extra slashes are okay
    ///
    /// assert!(!path.starts_with("/e"));
    /// assert!(!path.starts_with("/etc/passwd.txt"));
    ///
    /// assert!(!Path::new("/etc/foo.rs").starts_with("/etc/foo"));
    /// ```
    #[must_use]
    #[inline]
    pub fn starts_with<P: AsRef<std::path::Path>>(&self, base: P) -> bool {
        self.inner.starts_with(base.as_ref())
    }

    /// Determines whether `child` is a suffix of `self`.
    ///
    /// Only considers whole path components to match.
    ///
    /// # Examples
    ///
    /// ```
    /// use relabs::Path;
    ///
    /// let path = Path::new("/etc/resolv.conf");
    ///
    /// assert!(path.ends_with("resolv.conf"));
    /// assert!(path.ends_with("etc/resolv.conf"));
    /// assert!(path.ends_with("/etc/resolv.conf"));
    ///
    /// assert!(!path.ends_with("/resolv.conf"));
    /// assert!(!path.ends_with("conf")); // use .extension() instead
    /// ```
    #[must_use]
    #[inline]
    pub fn ends_with<P: AsRef<std::path::Path>>(&self, child: P) -> bool {
        self.inner.ends_with(child.as_ref())
    }

    /// Extracts the stem (non-extension) portion of [`self.file_name`].
    ///
    /// [`self.file_name`]: Path::file_name
    ///
    /// The stem is:
    ///
    /// * [`None`], if there is no file name;
    /// * The entire file name if there is no embedded `.`;
    /// * The entire file name if the file name begins with `.` and has no other `.`s within;
    /// * Otherwise, the portion of the file name before the final `.`
    ///
    /// # Examples
    ///
    /// ```
    /// use relabs::Path;
    ///
    /// assert_eq!("foo", Path::new("foo.rs").file_stem().unwrap());
    /// assert_eq!("foo.tar", Path::new("foo.tar.gz").file_stem().unwrap());
    /// ```
    ///
    /// # See Also
    /// This method is similar to [`Path::file_prefix`], which extracts the portion of the file name
    /// before the *first* `.`
    ///
    /// [`Path::file_prefix`]: Path::file_prefix
    ///
    #[must_use]
    #[inline]
    pub fn file_stem(&self) -> Option<&OsStr> {
        self.inner.file_stem()
    }

    /// Extracts the extension (without the leading dot) of [`self.file_name`], if possible.
    ///
    /// The extension is:
    ///
    /// * [`None`], if there is no file name;
    /// * [`None`], if there is no embedded `.`;
    /// * [`None`], if the file name begins with `.` and has no other `.`s within;
    /// * Otherwise, the portion of the file name after the final `.`
    ///
    /// [`self.file_name`]: Path::file_name
    ///
    /// # Examples
    ///
    /// ```
    /// use relabs::Path;
    ///
    /// assert_eq!("rs", Path::new("foo.rs").extension().unwrap());
    /// assert_eq!("gz", Path::new("foo.tar.gz").extension().unwrap());
    /// ```
    #[must_use]
    #[inline]
    pub fn extension(&self) -> Option<&OsStr> {
        self.inner.extension()
    }

    /// Creates an owned [`PathBuf`] like `self` but with the given file name.
    ///
    /// See [`PathBuf::set_file_name`] for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// use relabs::{Path, PathBuf};
    ///
    /// let path = Path::new("/tmp/foo.png");
    /// assert_eq!(path.with_file_name("bar"), PathBuf::from("/tmp/bar"));
    /// assert_eq!(path.with_file_name("bar.txt"), PathBuf::from("/tmp/bar.txt"));
    ///
    /// let path = Path::new("/tmp");
    /// assert_eq!(path.with_file_name("var"), PathBuf::from("/var"));
    /// ```
    #[must_use]
    #[inline]
    pub fn with_file_name<S: AsRef<OsStr>>(&self, file_name: S) -> PathBuf<Flavor> {
        PathBuf::new_trusted(self.inner.with_file_name(file_name))
    }

    /// Creates an owned [`PathBuf`] like `self` but with the given extension.
    ///
    /// See [`PathBuf::set_extension`] for more details.
    ///
    /// # Examples
    ///
    /// ```
    /// use relabs::Path;
    ///
    /// let path = Path::new("foo.rs");
    /// assert_eq!(path.with_extension("txt"), Path::new("foo.txt"));
    /// assert_eq!(path.with_extension(""), Path::new("foo"));
    /// ```
    ///
    /// Handling multiple extensions:
    ///
    /// ```
    /// use relabs::Path;
    ///
    /// let path = Path::new("foo.tar.gz");
    /// assert_eq!(path.with_extension("xz"), Path::new("foo.tar.xz"));
    /// assert_eq!(path.with_extension("").with_extension("txt"), Path::new("foo.txt"));
    /// ```
    ///
    /// Adding an extension where one did not exist:
    ///
    /// ```
    /// use relabs::Path;
    ///
    /// let path = Path::new("foo");
    /// assert_eq!(path.with_extension("rs"), Path::new("foo.rs"));
    /// ```
    #[inline]
    pub fn with_extension<S: AsRef<OsStr>>(&self, extension: S) -> PathBuf<Flavor> {
        PathBuf::new_trusted(self.inner.with_extension(extension))
    }

    /// Produces an iterator over the [`Component`]s of the path.
    ///
    /// When parsing the path, there is a small amount of normalization:
    ///
    /// * Repeated separators are ignored, so `a/b` and `a//b` both have
    ///   `a` and `b` as components.
    ///
    /// * Occurrences of `.` are normalized away, except if they are at the
    ///   beginning of the path. For example, `a/./b`, `a/b/`, `a/b/.` and
    ///   `a/b` all have `a` and `b` as components, but `./a/b` starts with
    ///   an additional [`CurDir`] component.
    ///
    /// * A trailing slash is normalized away, `/a/b` and `/a/b/` are equivalent.
    ///
    /// Note that no other normalization takes place; in particular, `a/c`
    /// and `a/b/../c` are distinct, to account for the possibility that `b`
    /// is a symbolic link (so its parent isn't `a`).
    ///
    /// # Examples
    ///
    /// ```
    /// use relabs::AnyPath;
    /// use std::path::Component;
    /// use std::ffi::OsStr;
    ///
    /// let mut components = AnyPath::new("/tmp/foo.txt").components();
    ///
    /// assert_eq!(components.next(), Some(Component::RootDir));
    /// assert_eq!(components.next(), Some(Component::Normal(OsStr::new("tmp"))));
    /// assert_eq!(components.next(), Some(Component::Normal(OsStr::new("foo.txt"))));
    /// assert_eq!(components.next(), None)
    /// ```
    ///
    /// [`CurDir`]: Component::CurDir
    pub fn components(&self) -> Components<'_> {
        self.inner.components()
    }

    /// Produces an iterator over the path's components viewed as [`OsStr`]
    /// slices.
    ///
    /// For more information about the particulars of how the path is separated
    /// into components, see [`components`].
    ///
    /// [`components`]: Path::components
    ///
    /// # Examples
    ///
    /// ```
    /// use relabs::{self, Path};
    /// use std::ffi::OsStr;
    ///
    /// let mut it = Path::new("/tmp/foo.txt").iter();
    /// assert_eq!(it.next(), Some(OsStr::new(&std::path::MAIN_SEPARATOR.to_string())));
    /// assert_eq!(it.next(), Some(OsStr::new("tmp")));
    /// assert_eq!(it.next(), Some(OsStr::new("foo.txt")));
    /// assert_eq!(it.next(), None)
    /// ```
    #[inline]
    pub fn iter(&self) -> std::path::Iter<'_> {
        self.inner.iter()
    }

    /// Returns an object that implements [`Display`] for safely printing paths
    /// that may contain non-Unicode data. This may perform lossy conversion,
    /// depending on the platform.  If you would like an implementation which
    /// escapes the path please use [`Debug`] instead.
    ///
    /// [`Display`]: fmt::Display
    /// [`Debug`]: fmt::Debug
    ///
    /// # Examples
    ///
    /// ```
    /// use relabs::Path;
    ///
    /// let path = Path::new("/tmp/foo.rs");
    ///
    /// println!("{}", path.display());
    /// ```
    #[must_use]
    #[inline]
    pub fn display(&self) -> std::path::Display<'_> {
        self.inner.display()
    }

    /// Queries the file system to get information about a file, directory, etc.
    ///
    /// This function will traverse symbolic links to query information about the
    /// destination file.
    ///
    /// This is an alias to [`fs::metadata`].
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use relabs::Path;
    ///
    /// let path = Path::new("/Minas/tirith");
    /// let metadata = path.metadata().expect("metadata call failed");
    /// println!("{:?}", metadata.file_type());
    /// ```
    #[inline]
    pub fn metadata(&self) -> io::Result<fs::Metadata> {
        self.inner.metadata()
    }

    /// Queries the metadata about a file without following symlinks.
    ///
    /// This is an alias to [`fs::symlink_metadata`].
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use relabs::Path;
    ///
    /// let path = Path::new("/Minas/tirith");
    /// let metadata = path.symlink_metadata().expect("symlink_metadata call failed");
    /// println!("{:?}", metadata.file_type());
    /// ```
    #[inline]
    pub fn symlink_metadata(&self) -> io::Result<fs::Metadata> {
        self.inner.symlink_metadata()
    }

    /// Returns the canonical, absolute form of the path with all intermediate
    /// components normalized and symbolic links resolved.
    ///
    /// This is an alias to [`fs::canonicalize`].
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use relabs::{Path, PathBuf};
    ///
    /// let path = Path::new("/foo/test/../test/bar.rs");
    /// assert_eq!(path.canonicalize().unwrap(), PathBuf::from("/foo/test/bar.rs"));
    /// ```
    #[inline]
    pub fn canonicalize(&self) -> io::Result<PathBuf> {
        todo!()
    }

    /// Returns an iterator over the entries within a directory.
    ///
    /// The iterator will yield instances of <code>[io::Result]<[fs::DirEntry]></code>. New
    /// errors may be encountered after an iterator is initially constructed.
    ///
    /// This is an alias to [`fs::read_dir`].
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use relabs::Path;
    ///
    /// let path = Path::new("/laputa");
    /// for entry in path.read_dir().expect("read_dir call failed") {
    ///     if let Ok(entry) = entry {
    ///         println!("{:?}", entry.path());
    ///     }
    /// }
    /// ```
    #[inline]
    pub fn read_dir(&self) -> io::Result<fs::ReadDir> {
        self.inner.read_dir()
    }

    /// Returns `true` if the path points at an existing entity.
    ///
    /// Warning: this method may be error-prone, consider using [`try_exists()`] instead!
    /// It also has a risk of introducing time-of-check to time-of-use ([TOCTOU]) bugs.
    ///
    /// This function will traverse symbolic links to query information about the
    /// destination file.
    ///
    /// If you cannot access the metadata of the file, e.g. because of a
    /// permission error or broken symbolic links, this will return `false`.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use relabs::Path;
    /// assert!(!Path::new("does_not_exist.txt").exists());
    /// ```
    ///
    /// # See Also
    ///
    /// This is a convenience function that coerces errors to false. If you want to
    /// check errors, call [`Path::try_exists`].
    ///
    /// [`try_exists()`]: Self::try_exists
    #[must_use]
    #[inline]
    pub fn exists(&self) -> bool {
        self.inner.exists()
    }

    /// Returns `Ok(true)` if the path points at an existing entity.
    ///
    /// This function will traverse symbolic links to query information about the
    /// destination file. In case of broken symbolic links this will return `Ok(false)`.
    ///
    /// [`Path::exists()`] only checks whether or not a path was both found and readable. By
    /// contrast, `try_exists` will return `Ok(true)` or `Ok(false)`, respectively, if the path
    /// was _verified_ to exist or not exist. If its existence can neither be confirmed nor
    /// denied, it will propagate an `Err(_)` instead. This can be the case if e.g. listing
    /// permission is denied on one of the parent directories.
    ///
    /// Note that while this avoids some pitfalls of the `exists()` method, it still can not
    /// prevent time-of-check to time-of-use ([TOCTOU]) bugs. You should only use it in scenarios
    /// where those bugs are not an issue.
    ///
    /// This is an alias for [`std::fs::exists`](crate::fs::exists).
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use relabs::Path;
    /// assert!(!Path::new("does_not_exist.txt").try_exists().expect("Can't check existence of file does_not_exist.txt"));
    /// assert!(Path::new("/root/secret_file.txt").try_exists().is_err());
    /// ```
    ///
    /// [`exists()`]: Self::exists
    #[inline]
    pub fn try_exists(&self) -> io::Result<bool> {
        self.inner.try_exists()
    }

    /// Returns `true` if the path exists on disk and is pointing at a regular file.
    ///
    /// This function will traverse symbolic links to query information about the
    /// destination file.
    ///
    /// If you cannot access the metadata of the file, e.g. because of a
    /// permission error or broken symbolic links, this will return `false`.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use relabs::Path;
    /// assert_eq!(Path::new("./is_a_directory/").is_file(), false);
    /// assert_eq!(Path::new("a_file.txt").is_file(), true);
    /// ```
    ///
    /// # See Also
    ///
    /// This is a convenience function that coerces errors to false. If you want to
    /// check errors, call [`fs::metadata`] and handle its [`Result`]. Then call
    /// [`fs::Metadata::is_file`] if it was [`Ok`].
    ///
    /// When the goal is simply to read from (or write to) the source, the most
    /// reliable way to test the source can be read (or written to) is to open
    /// it. Only using `is_file` can break workflows like `diff <( prog_a )` on
    /// a Unix-like system for example. See [`fs::File::open`] or
    /// [`fs::OpenOptions::open`] for more information.
    #[must_use]
    #[inline]
    pub fn is_file(&self) -> bool {
        self.inner.is_file()
    }

    /// Returns `true` if the path exists on disk and is pointing at a directory.
    ///
    /// This function will traverse symbolic links to query information about the
    /// destination file.
    ///
    /// If you cannot access the metadata of the file, e.g. because of a
    /// permission error or broken symbolic links, this will return `false`.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use relabs::Path;
    /// assert_eq!(Path::new("./is_a_directory/").is_dir(), true);
    /// assert_eq!(Path::new("a_file.txt").is_dir(), false);
    /// ```
    ///
    /// # See Also
    ///
    /// This is a convenience function that coerces errors to false. If you want to
    /// check errors, call [`fs::metadata`] and handle its [`Result`]. Then call
    /// [`fs::Metadata::is_dir`] if it was [`Ok`].
    #[must_use]
    #[inline]
    pub fn is_dir(&self) -> bool {
        self.inner.is_dir()
    }

    /// Returns `true` if the path exists on disk and is pointing at a symbolic link.
    ///
    /// This function will not traverse symbolic links.
    /// In case of a broken symbolic link this will also return true.
    ///
    /// If you cannot access the directory containing the file, e.g., because of a
    /// permission error, this will return false.
    ///
    /// # Examples
    ///
    #[cfg_attr(unix, doc = "```no_run")]
    #[cfg_attr(not(unix), doc = "```ignore")]
    /// use relabs::Path;
    /// use std::os::unix::fs::symlink;
    ///
    /// let link_path = Path::new("link");
    /// symlink("/origin_does_not_exist/", link_path).unwrap();
    /// assert_eq!(link_path.is_symlink(), true);
    /// assert_eq!(link_path.exists(), false);
    /// ```
    ///
    /// # See Also
    ///
    /// This is a convenience function that coerces errors to false. If you want to
    /// check errors, call [`fs::symlink_metadata`] and handle its [`Result`]. Then call
    /// [`fs::Metadata::is_symlink`] if it was [`Ok`].
    #[must_use]
    pub fn is_symlink(&self) -> bool {
        self.inner.is_symlink()
    }

    /// Converts a [`Box<Path>`](Box) into a [`PathBuf`] without copying or
    /// allocating.
    #[must_use]
    pub fn into_path_buf(self: Box<Self>) -> PathBuf<Flavor> {
        todo!()
    }

    /// Joins a relative path onto this path.
    ///
    /// The result remains invariant.
    pub fn join<P: AsRef<RelPath>>(&self, path: P) -> PathBuf<Flavor> {
        let joined_std = self.inner.join(path.as_ref().as_std());
        debug_assert!(Flavor::accepts(&joined_std));
        PathBuf::<Flavor>::new_trusted(joined_std)
    }

    /// Tries to join a path-like value onto this path.
    ///
    /// This is the fallible counterpart to [`join`]. It first validates that
    /// `path` is a relative path, and then joins it. The flavor remains invariant.
    pub fn try_join<P: AsRef<std::path::Path>>(
        &self,
        path: P,
    ) -> Result<PathBuf<Flavor>, PathFlavorError> {
        Ok(self.join(RelPath::try_new(&path)?))
    }
}

impl<Flavor: StdJoin> Path<Flavor> {
    /// Creates an owned [`PathBuf`] with `path` adjoined to `self`.
    ///
    /// If `path` is absolute, it replaces the current path and creates a new absolute path.
    ///
    /// See [`PathBuf::push`] for more details on what it means to adjoin a path.
    ///
    /// # Examples
    ///
    /// ```
    /// use relabs::{Path, PathBuf};
    ///
    /// assert_eq!(Path::new("/etc").join("passwd"), PathBuf::from("/etc/passwd"));
    /// assert_eq!(Path::new("/etc").join("/bin/sh"), PathBuf::from("/bin/sh"));
    /// ```
    #[must_use]
    #[inline]
    pub fn join_std<P: AsRef<Path>>(&self, path: P) -> PathBuf<Flavor::Output> {
        PathBuf::<Flavor::Output>::new_trusted(self.inner.join(&path.as_ref().inner))
    }
}

impl AnyPath {
    /// Directly wraps a string slice as a `Path<Flavor = Any>` slice.
    ///
    /// This is a cost-free conversion.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::path::Path;
    ///
    /// Path::new("foo.txt");
    /// ```
    ///
    /// You can create `Path`s from `String`s, or even other `Path`s:
    ///
    /// ```
    /// use std::path::Path;
    ///
    /// let string = String::from("foo.txt");
    /// let from_string = Path::new(&string);
    /// let from_path = Path::new(&from_string);
    /// assert_eq!(from_string, from_path);
    /// ```
    #[inline]
    pub fn new<P: AsRef<std::path::Path> + ?Sized>(path: &P) -> &Self {
        Self::new_trusted(path)
    }
}

impl AsRef<AnyPath> for str {
    fn as_ref(&self) -> &AnyPath {
        AnyPath::new(self)
    }
}

impl<Flavor: PathFlavor> AsRef<OsStr> for Path<Flavor> {
    #[inline]
    fn as_ref(&self) -> &OsStr {
        self.inner.as_os_str()
    }
}

impl<Flavor: PathFlavor> AsRef<std::path::Path> for Path<Flavor> {
    #[inline]
    fn as_ref(&self) -> &std::path::Path {
        &self.inner
    }
}

impl<Flavor: PathFlavor> AsRef<Path<Flavor>> for Path<Flavor> {
    #[inline]
    fn as_ref(&self) -> &Path<Flavor> {
        self
    }
}

// Public per-flavor wrappers.

impl Path<Absolute> {
    /// Reads a symbolic link, returning the file that the link points to.
    ///
    /// This is an alias to [`fs::read_link`].
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use relabs::AbsPath;
    ///
    /// let path = AbsPath::try_new("/laputa/sky_castle.rs").unwrap();
    /// let path_link = path.read_link().expect("read_link call failed");
    /// ```
    #[inline]
    pub fn read_link(&self) -> io::Result<PathBuf<Any>> {
        self.inner.read_link().map(PathBuf::new_trusted)
    }
}

impl Path<Relative> {}

impl<Flavor> fmt::Debug for Path<Flavor>
where
    Flavor: PathFlavor,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_std().fmt(f)
    }
}

impl<Flavor: PathFlavor> PartialEq for Path<Flavor> {
    fn eq(&self, other: &Self) -> bool {
        self.inner == other.inner
    }
}

impl<Flavor: PathFlavor> Eq for Path<Flavor> {}

impl<Flavor: PathFlavor> PartialEq<PathBuf<Flavor>> for Path<Flavor> {
    fn eq(&self, other: &PathBuf<Flavor>) -> bool {
        self == other.as_path()
    }
}

impl<Flavor: PathFlavor> PartialEq<PathBuf<Flavor>> for &Path<Flavor> {
    fn eq(&self, other: &PathBuf<Flavor>) -> bool {
        *self == other.as_path()
    }
}

/// An iterator over [`Path`] and its ancestors.
///
/// This `struct` is created by the [`ancestors`] method on [`Path`].
/// See its documentation for more.
///
/// # Examples
///
/// ```
/// use relabs::Path;
///
/// let path = Path::new("/foo/bar");
///
/// for ancestor in path.ancestors() {
///     println!("{}", ancestor.display());
/// }
/// ```
///
/// [`ancestors`]: Path::ancestors
#[derive(Copy, Clone, Debug)]
#[must_use]
pub struct Ancestors<'a, Flavor: PathFlavor> {
    _flavor: PhantomData<Flavor>,
    inner: std::path::Ancestors<'a>,
}

impl<'a, Flavor: PathFlavor + 'a> Iterator for Ancestors<'a, Flavor> {
    type Item = &'a Path<Flavor>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(Path::new_trusted)
    }
}

impl<'a, Flavor: PathFlavor + 'a> FusedIterator for Ancestors<'a, Flavor> {}
