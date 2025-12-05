use std::{
    collections::TryReserveError,
    ffi::{OsStr, OsString},
    fmt,
    marker::PhantomData,
};

use crate::{
    AbsPath, AnyPath,
    errors::PathFlavorError,
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
/// Invariant: 'Path::is_relative()' must be true.
pub type RelPathBuf = PathBuf<Relative>;

/// Owned, unconstrained path ('PathBuf<Any>').
///
/// Invariant: No invariant.
pub type AnyPathBuf = PathBuf<Any>;

impl<Flavor> PathBuf<Flavor>
where
    Flavor: PathFlavor,
{
    /// Create a new [`PathBuf<Flavor>`] from a `std::path::PathBuf` without validating the invariant.
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
    /// // Example with a specific flavor (Absolute)
    /// let abs_buf = AbsPathBuf::try_from("/etc/passwd").unwrap();
    /// let abs_slice: &AbsPath = abs_buf.as_path();
    /// assert_eq!(AbsPath::try_new("/etc/passwd").unwrap(), abs_slice);
    ///
    /// // Example with the default flavor (Any)
    /// let any_path = PathBuf::from("/test");
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
    /// Using an **Absolute** path (cannot pop root):
    ///
    /// ```
    /// use relabs::{AbsPath, AbsPathBuf};
    ///
    /// let mut p = AbsPathBuf::try_from("/usr/bin").unwrap();
    ///
    /// assert!(p.pop());
    /// assert_eq!(AbsPath::try_new("/usr").unwrap(), p);
    ///
    /// assert!(p.pop());
    /// assert_eq!(AbsPath::try_new("/").unwrap(), p);
    ///
    /// // Cannot pop the root of an absolute path
    /// assert!(!p.pop());
    /// assert_eq!(AbsPath::try_new("/").unwrap(), p);
    /// ```
    ///
    /// Using a **Relative** path:
    ///
    /// ```
    /// use relabs::{RelPath, RelPathBuf};
    ///
    /// let mut p = RelPathBuf::try_from("usr/bin").unwrap();
    /// assert!(p.pop());
    /// assert_eq!(RelPath::try_new("usr").unwrap(), p);
    /// ```
    pub fn pop(&mut self) -> bool {
        self.inner.pop()
    }

    /// Updates [`self.file_name`] to `file_name`.
    ///
    /// This method is specialized for [`RelPathBuf`] and **requires** the input
    /// `file_name` to be a valid relative path component (`Path<Relative>`).
    ///
    /// This strict typing guarantees that the path flavor invariant is **maintained**
    /// at compile time, eliminating the need for runtime checks.
    ///
    /// If [`self.file_name`] was [`None`], this is equivalent to pushing
    /// `file_name`.
    ///
    /// Otherwise it is equivalent to calling [`pop`] and then pushing
    /// `file_name`. The new path will be a sibling of the original path.
    /// (That is, it will have the same parent.)
    ///
    /// [`self.file_name`]: Path::file_name
    /// [`pop`]: PathBuf::pop
    ///
    /// # Examples
    ///
    /// ```
    /// use relabs::{RelPath, RelPathBuf};
    ///
    /// let mut buf = RelPathBuf::try_from("foo/bar.txt").unwrap();
    ///
    /// // The input must first be constructed as a relative path slice
    /// let new_name = RelPath::try_new("baz.txt").unwrap();
    ///
    /// buf.set_file_name(new_name);
    /// assert_eq!(buf, RelPathBuf::try_from("foo/baz.txt").unwrap());
    ///
    /// // Attempting to pass an absolute path will fail at compile time
    /// // (if using a proper path slice like AbsPath) or at the construction
    /// // phase (if using RelPath::try_new):
    ///
    /// // let absolute_name = AbsPath::try_new("/root.txt").unwrap();
    /// // buf.set_file_name(absolute_name); // <- Compile Error (Good!)
    /// ```
    pub fn set_file_name<S: AsRef<RelPath>>(&mut self, file_name: S) {
        self.inner.set_file_name(file_name.as_ref().as_os_str())
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
    /// use relabs::{AbsPath, AbsPathBuf};
    ///
    /// // Using AbsPathBuf to ensure extensions work on typed paths
    /// let mut p = AbsPathBuf::try_from("/feel/the").unwrap();
    ///
    /// p.set_extension("force");
    /// assert_eq!(AbsPath::try_new("/feel/the.force").unwrap(), p.as_path());
    ///
    /// p.set_extension("dark.side");
    /// assert_eq!(AbsPath::try_new("/feel/the.dark.side").unwrap(), p.as_path());
    ///
    /// p.set_extension("");
    /// assert_eq!(AbsPath::try_new("/feel/the.dark").unwrap(), p.as_path());
    /// ```
    pub fn set_extension<S: AsRef<OsStr>>(&mut self, extension: S) -> bool {
        self.inner.set_extension(extension)
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
        let boxed_std: Box<std::path::Path> = self.inner.into_boxed_path();
        internal::convert_box(boxed_std)
    }

    /// Invokes [`capacity`] on the underlying instance of [`OsString`].
    ///
    /// [`capacity`]: OsString::capacity
    #[must_use]
    #[inline]
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
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

    // Flavor-changing: consumes self and reuses its buffer (can reuse capacity).
    // Same as `set` but with changes flavor.
    #[inline]
    pub fn replace_with<T, P>(self, rhs: P) -> PathBuf<T>
    where
        T: PathFlavor,
        P: AsRef<Path<T>>,
    {
        let mut inner = self.into_inner();
        inner.clear();
        inner.push(rhs.as_ref().as_inner());
        debug_assert!(T::accepts(&inner));
        PathBuf::<T>::new_trusted(inner)
    }

    /// Appends a relative path segment to this buffer.
    #[inline]
    pub fn push<P: AsRef<RelPath>>(&mut self, rhs: P) {
        self.inner.push(rhs.as_ref().as_inner());
        debug_assert!(Flavor::accepts(&self.inner));
    }

    /// Untyped fallible version of [`push`].
    #[inline]
    pub fn try_push<P: AsRef<std::path::Path>>(&mut self, rhs: P) -> Result<(), PathFlavorError> {
        self.push(RelPath::try_new(&rhs)?);
        Ok(())
    }

    // Borrowed input. Reuses existing allocation. Does not change flavor.
    // Is a clear followed by std's push.
    // Use `replace_with` to change flavor.
    #[inline]
    pub fn set<P: AsRef<Path<Flavor>>>(&mut self, new: P) {
        let p = new.as_ref().as_inner();
        self.inner.clear();
        self.inner.push(p);
        debug_assert!(Absolute::accepts(&self.inner));
    }

    /// Untyped fallible version of [`set`].
    #[inline]
    pub fn try_set<P: AsRef<std::path::Path>>(&mut self, new: P) -> Result<(), PathFlavorError> {
        self.set(Path::<Flavor>::try_new(&new)?);
        Ok(())
    }
}

// Public per-flavor wrappers.

impl AnyPathBuf {
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
    /// use relabs::AnyPathBuf;
    ///
    /// let mut any_path = AnyPathBuf::with_capacity(10);
    /// let capacity = any_path.capacity();
    ///
    /// // This set is done without reallocating
    /// any_path.set(r"C:\");
    ///
    /// assert_eq!(capacity, any_path.capacity());
    /// ```
    #[inline]
    pub fn with_capacity(capacity: usize) -> PathBuf {
        Self::new_trusted(std::path::PathBuf::with_capacity(capacity))
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
    /// path.try_push("bar").unwrap();
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

    /// Invokes [`clear`] on the underlying instance of [`OsString`].
    ///
    /// [`clear`]: OsString::clear
    #[inline]
    pub fn clear(&mut self) {
        self.inner.clear()
    }
}

impl PathBuf<Relative> {}

impl PathBuf<Absolute> {}

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

impl TryFrom<&str> for AbsPathBuf {
    type Error = std::path::PathBuf;

    fn try_from(s: &str) -> Result<Self, Self::Error> {
        // TODO: We should probably just use `relabs::PathBuf::from(s)` directly.
        Self::try_from(std::path::PathBuf::from(s))
    }
}

impl TryFrom<&str> for RelPathBuf {
    type Error = std::path::PathBuf;

    fn try_from(s: &str) -> Result<Self, Self::Error> {
        // TODO: We should probably just use `relabs::PathBuf::from(s)` directly.
        Self::try_from(std::path::PathBuf::from(s))
    }
}

impl From<&str> for AnyPathBuf {
    fn from(value: &str) -> Self {
        Self::new_trusted(std::path::PathBuf::from(value))
    }
}

impl TryFrom<String> for AbsPathBuf {
    type Error = std::path::PathBuf;

    fn try_from(s: String) -> Result<Self, Self::Error> {
        // TODO: We should probably just use `relabs::PathBuf::from(s)` directly.
        Self::try_from(std::path::PathBuf::from(s))
    }
}

impl TryFrom<String> for RelPathBuf {
    type Error = std::path::PathBuf;

    fn try_from(s: String) -> Result<Self, Self::Error> {
        // TODO: We should probably just use `relabs::PathBuf::from(s)` directly.
        Self::try_from(std::path::PathBuf::from(s))
    }
}

impl From<String> for AnyPathBuf {
    fn from(value: String) -> Self {
        Self::new_trusted(std::path::PathBuf::from(value))
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
        self.as_path() == other.as_path()
    }
}

impl<Flavor: PathFlavor> Eq for PathBuf<Flavor> {}

impl<Flavor: PathFlavor> PartialEq<Path<Flavor>> for PathBuf<Flavor> {
    fn eq(&self, other: &Path<Flavor>) -> bool {
        self.as_path() == other
    }
}

impl<Flavor: PathFlavor> PartialEq<&Path<Flavor>> for PathBuf<Flavor> {
    fn eq(&self, other: &&Path<Flavor>) -> bool {
        self.as_path() == *other
    }
}
