use std::{
    collections::TryReserveError,
    ffi::{OsStr, OsString},
    fmt,
    marker::PhantomData,
};

use crate::{
    flavors::{Absolute, Any, PathFlavor, Relative},
    internal,
    path::{Path, RelPath},
};

/// Newtype wrapper around `std::path::PathBuf`.
#[repr(transparent)]
pub struct PathBuf<Flavor = Any> {
    _flavor: PhantomData<Flavor>,
    inner: std::path::PathBuf,
}

/// Owned, typed, absolute path ('PathBuf<Absolute>').
///
/// Invariant: 'Path::is_absolute()' must be true.
pub type AbsPathBuf = PathBuf<Absolute>;

/// Owned, typed, relative path ('PathBuf<Relative>').
///
/// Invariant: 'Path::is_is_relative()' must be true.
pub type RelPathBuf = PathBuf<Relative>;

impl<Flavor> PathBuf<Flavor>
where
    Flavor: PathFlavor,
{
    /// Create a new [`PathBuf<Flavor>`] from a `std::path::PathBuf` withour validating the invariant.
    /// Caller must ensure `invariant` holds.
    pub(crate) fn new_trusted(path: std::path::PathBuf) -> Self {
        debug_assert!(Flavor::accepts(&path));
        Self {
            _flavor: PhantomData,
            inner: path,
        }
    }

    /// Coerces to a [`Path<Flavor>`] slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use relabs::{AbsPath, AbsPathBuf, PathBuf, Path};
    ///
    /// let abs_path = AbsPathBuf::try_from("/test").unwrap();
    /// let any_path = PathBuf::from("/test");
    /// assert_eq!(AbsPath::new("/test").unwrap(), abs_path.as_path());
    /// assert_eq!(Path::new("/test"), any_path.as_path());
    /// ```
    #[inline]
    pub fn as_path(&self) -> &Path<Flavor> {
        internal::convert_ref(&self.inner)
    }

    #[must_use]
    #[inline]
    pub fn into_inner(self) -> std::path::PathBuf {
        self.inner
    }

    /// Truncates `self` to [`self.parent`].
    ///
    /// Returns `false` and does nothing if [`self.parent`] is [`None`].
    /// Otherwise, returns `true`.
    ///
    /// [`self.parent`]: Path::parent
    ///
    /// # Examples
    ///
    /// ```
    /// use relabs::{Path, PathBuf};
    ///
    /// let mut p = PathBuf::from("/spirited/away.rs");
    ///
    /// p.pop();
    /// assert_eq!(Path::new("/spirited"), p);
    /// p.pop();
    /// assert_eq!(Path::new("/"), p);
    /// ```
    pub fn pop(&mut self) -> bool {
        self.inner.pop()
    }

    /// Updates [`self.file_name`] to `file_name`.
    ///
    /// If [`self.file_name`] was [`None`], this is equivalent to pushing
    /// `file_name`.
    ///
    /// Otherwise it is equivalent to calling [`pop`] and then pushing
    /// `file_name`. The new path will be a sibling of the original path.
    /// (That is, it will have the same parent.)
    ///
    /// The argument is not sanitized, so can include separators. This
    /// behavior may be changed to a panic in the future.
    ///
    /// [`self.file_name`]: Path::file_name
    /// [`pop`]: PathBuf::pop
    ///
    /// # Examples
    ///
    /// ```
    /// use relabs::PathBuf;
    ///
    /// let mut buf = PathBuf::from("/");
    /// assert!(buf.file_name() == None);
    ///
    /// buf.set_file_name("foo.txt");
    /// assert!(buf == PathBuf::from("/foo.txt"));
    /// assert!(buf.file_name().is_some());
    ///
    /// buf.set_file_name("bar.txt");
    /// assert!(buf == PathBuf::from("/bar.txt"));
    ///
    /// buf.set_file_name("baz");
    /// assert!(buf == PathBuf::from("/baz"));
    ///
    /// buf.set_file_name("../b/c.txt");
    /// assert!(buf == PathBuf::from("/../b/c.txt"));
    ///
    /// buf.set_file_name("baz");
    /// assert!(buf == PathBuf::from("/../b/baz"));
    /// ```
    pub fn set_file_name<S: AsRef<OsStr>>(&mut self, file_name: S) {
        self.inner.set_file_name(file_name)
    }

    /// Updates [`self.extension`] to `Some(extension)` or to `None` if
    /// `extension` is empty.
    ///
    /// Returns `false` and does nothing if [`self.file_name`] is [`None`],
    /// returns `true` and updates the extension otherwise.
    ///
    /// If [`self.extension`] is [`None`], the extension is added; otherwise
    /// it is replaced.
    ///
    /// If `extension` is the empty string, [`self.extension`] will be [`None`]
    /// afterwards, not `Some("")`.
    ///
    /// # Panics
    ///
    /// Panics if the passed extension contains a path separator (see
    /// [`is_separator`]).
    ///
    /// # Caveats
    ///
    /// The new `extension` may contain dots and will be used in its entirety,
    /// but only the part after the final dot will be reflected in
    /// [`self.extension`].
    ///
    /// If the file stem contains internal dots and `extension` is empty, part
    /// of the old file stem will be considered the new [`self.extension`].
    ///
    /// See the examples below.
    ///
    /// [`self.file_name`]: Path::file_name
    /// [`self.extension`]: Path::extension
    ///
    /// # Examples
    ///
    /// ```
    /// use relabs::{Path, PathBuf};
    ///
    /// let mut p = PathBuf::from("/feel/the");
    ///
    /// p.set_extension("force");
    /// assert_eq!(Path::new("/feel/the.force"), p.as_path());
    ///
    /// p.set_extension("dark.side");
    /// assert_eq!(Path::new("/feel/the.dark.side"), p.as_path());
    ///
    /// p.set_extension("cookie");
    /// assert_eq!(Path::new("/feel/the.dark.cookie"), p.as_path());
    ///
    /// p.set_extension("");
    /// assert_eq!(Path::new("/feel/the.dark"), p.as_path());
    ///
    /// p.set_extension("");
    /// assert_eq!(Path::new("/feel/the"), p.as_path());
    ///
    /// p.set_extension("");
    /// assert_eq!(Path::new("/feel/the"), p.as_path());
    /// ```
    pub fn set_extension<S: AsRef<OsStr>>(&mut self, extension: S) -> bool {
        self.inner.set_extension(extension)
    }

    /// Yields a mutable reference to the underlying [`OsString`] instance.
    ///
    /// # Examples
    ///
    /// ```
    /// use relabs::{Path, PathBuf};
    ///
    /// let mut path = PathBuf::from("/foo");
    ///
    /// path.push("bar");
    /// assert_eq!(path, Path::new("/foo/bar"));
    ///
    /// // OsString's `push` does not add a separator.
    /// path.as_mut_os_string().push("baz");
    /// assert_eq!(path, Path::new("/foo/barbaz"));
    /// ```
    #[must_use]
    #[inline]
    pub fn as_mut_os_string(&mut self) -> &mut OsString {
        self.inner.as_mut_os_string()
    }

    /// Consumes the `PathBuf`, yielding its internal [`OsString`] storage.
    ///
    /// # Examples
    ///
    /// ```
    /// use relabs::PathBuf;
    ///
    /// let p = PathBuf::from("/the/head");
    /// let os_str = p.into_os_string();
    /// ```
    #[must_use]
    #[inline]
    pub fn into_os_string(self) -> OsString {
        self.inner.into_os_string()
    }

    /// Converts this `PathBuf` into a [boxed](Box) [`Path`].
    #[must_use]
    #[inline]
    pub fn into_boxed_path(self) -> Box<Path<Flavor>> {
        todo!()
    }

    /// Invokes [`capacity`] on the underlying instance of [`OsString`].
    ///
    /// [`capacity`]: OsString::capacity
    #[must_use]
    #[inline]
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    /// Invokes [`clear`] on the underlying instance of [`OsString`].
    ///
    /// [`clear`]: OsString::clear
    #[inline]
    pub fn clear(&mut self) {
        self.inner.clear()
    }

    /// Invokes [`reserve`] on the underlying instance of [`OsString`].
    ///
    /// [`reserve`]: OsString::reserve
    #[inline]
    pub fn reserve(&mut self, additional: usize) {
        self.inner.reserve(additional)
    }

    /// Invokes [`try_reserve`] on the underlying instance of [`OsString`].
    ///
    /// [`try_reserve`]: OsString::try_reserve
    #[inline]
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.inner.try_reserve(additional)
    }

    /// Invokes [`reserve_exact`] on the underlying instance of [`OsString`].
    ///
    /// [`reserve_exact`]: OsString::reserve_exact
    #[inline]
    pub fn reserve_exact(&mut self, additional: usize) {
        self.inner.reserve_exact(additional)
    }

    /// Invokes [`try_reserve_exact`] on the underlying instance of [`OsString`].
    ///
    /// [`try_reserve_exact`]: OsString::try_reserve_exact
    #[inline]
    pub fn try_reserve_exact(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.inner.try_reserve_exact(additional)
    }

    /// Invokes [`shrink_to_fit`] on the underlying instance of [`OsString`].
    ///
    /// [`shrink_to_fit`]: OsString::shrink_to_fit
    #[inline]
    pub fn shrink_to_fit(&mut self) {
        self.inner.shrink_to_fit()
    }

    /// Invokes [`shrink_to`] on the underlying instance of [`OsString`].
    ///
    /// [`shrink_to`]: OsString::shrink_to
    #[inline]
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.inner.shrink_to(min_capacity)
    }
}

// Public per-flavor wrappers.

// PatBuf<Flavor = Any>
impl PathBuf {
    /// Allocates an empty [`PathBuf<Falvor = Any>`].
    ///
    /// # Examples
    ///
    /// ```
    /// use relabs::PathBuf;
    ///
    /// let path = PathBuf::new();
    /// ```
    #[inline]
    pub fn new() -> Self {
        Self::new_trusted(std::path::PathBuf::new())
    }

    /// Creates a new [`PathBuf<Flavor = Any>`] with a given capacity used to create the
    /// internal [`std::path::PathBuf`].
    ///
    /// # Examples
    ///
    /// ```
    /// use relabs::PathBuf;
    ///
    /// let mut path = PathBuf::with_capacity(10);
    /// let capacity = path.capacity();
    ///
    /// // This push is done without reallocating
    /// path.push(r"C:\");
    ///
    /// assert_eq!(capacity, path.capacity());
    /// ```
    #[inline]
    pub fn with_capacity(capacity: usize) -> PathBuf {
        Self::new_trusted(std::path::PathBuf::with_capacity(capacity))
    }

    #[inline]
    pub fn set<P: AsRef<Path>>(&mut self, new: P) {
        self.inner = new.as_ref().as_inner().to_path_buf();
    }

    #[inline]
    pub fn push<P: AsRef<Path>>(&mut self, rhs: P) {
        self.inner.push(rhs.as_ref().as_inner());
        debug_assert!(Any::accepts(&self.inner));
    }
}

impl PathBuf<Relative> {
    #[inline]
    pub fn push<P: AsRef<RelPath>>(&mut self, rhs: P) {
        self.inner.push(rhs.as_ref().as_inner());
        debug_assert!(Relative::accepts(&self.inner));
    }
}

impl PathBuf<Absolute> {
    #[inline]
    pub fn push<P: AsRef<Path>>(&mut self, rhs: P) {
        self.inner.push(rhs.as_ref().as_inner());
        debug_assert!(Relative::accepts(&self.inner));
    }
}

impl Default for PathBuf {
    fn default() -> Self {
        Self {
            _flavor: PhantomData,
            inner: std::path::PathBuf::default(),
        }
    }
}

//////////////////////////////////////////////////////////////
// Conversions
//////////////////////////////////////////////////////////////

impl<Flavor> TryFrom<std::path::PathBuf> for PathBuf<Flavor>
where
    Flavor: PathFlavor,
{
    type Error = std::path::PathBuf;

    fn try_from(path: std::path::PathBuf) -> Result<Self, Self::Error> {
        if Flavor::accepts(&path) {
            Ok(Self::new_trusted(path))
        } else {
            Err(path)
        }
    }
}

impl<Flavor> TryFrom<&std::path::Path> for PathBuf<Flavor>
where
    Flavor: PathFlavor,
{
    type Error = std::path::PathBuf;

    fn try_from(path: &std::path::Path) -> Result<Self, Self::Error> {
        Self::try_from(path.to_path_buf())
    }
}

impl<Flavor> TryFrom<&str> for PathBuf<Flavor>
where
    Flavor: PathFlavor,
{
    type Error = std::path::PathBuf;

    fn try_from(s: &str) -> Result<Self, Self::Error> {
        // TODO: We should probably just use `relabs::PathBuf::from(s)` directly.
        Self::try_from(std::path::PathBuf::from(s))
    }
}

impl<Flavor> TryFrom<String> for PathBuf<Flavor>
where
    Flavor: PathFlavor,
{
    type Error = std::path::PathBuf;

    fn try_from(s: String) -> Result<Self, Self::Error> {
        // TODO: We should probably just use `relabs::PathBuf::from(s)` directly.
        Self::try_from(std::path::PathBuf::from(s))
    }
}

impl<Flavor> AsRef<OsStr> for PathBuf<Flavor> {
    #[inline]
    fn as_ref(&self) -> &OsStr {
        self.inner.as_os_str()
    }
}

impl<Flavor> AsRef<std::path::Path> for PathBuf<Flavor> {
    #[inline]
    fn as_ref(&self) -> &std::path::Path {
        &self.inner
    }
}

impl<Flavor> fmt::Debug for PathBuf<Flavor>
where
    Flavor: PathFlavor,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

impl<Flavor: PathFlavor> PartialEq for PathBuf<Flavor> {
    fn eq(&self, other: &Self) -> bool {
        self.inner == other.inner
    }
}
