use std::{
    borrow::{Borrow, Cow},
    collections::TryReserveError,
    convert::Infallible,
    ffi::{OsStr, OsString},
    fmt,
    hash::{Hash, Hasher},
    marker::PhantomData,
    ops::{Deref, DerefMut},
    rc::Rc,
    str::FromStr,
    sync::Arc,
};

use crate::{
    AnyPath,
    errors::PathFlavorError,
    flavors::{Absolute, Any, PathFlavor, Relative, StdPush},
    internal::{self, convert_mut},
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
    pub fn into_std(self) -> std::path::PathBuf {
        self.inner
    }

    #[must_use]
    #[inline]
    pub fn as_std_mut(&mut self) -> &mut std::path::PathBuf {
        &mut self.inner
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

    /// Append [`self.extension`] with `extension`.
    ///
    /// Returns `false` and does nothing if [`self.file_name`] is [`None`],
    /// returns `true` and updates the extension otherwise.
    ///
    /// # Panics
    ///
    /// Panics if the passed extension contains a path separator (see
    /// [`is_separator`]).
    ///
    /// # Caveats
    ///
    /// The appended `extension` may contain dots and will be used in its entirety,
    /// but only the part after the final dot will be reflected in
    /// [`self.extension`].
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
    ///
    /// let mut p = AbsPathBuf::try_from("/feel/the").unwrap();
    ///
    /// p.add_extension("formatted");
    /// assert_eq!(AbsPath::try_new("/feel/the.formatted").unwrap(), p.as_path());
    ///
    /// p.add_extension("dark.side");
    /// assert_eq!(AbsPath::try_new("/feel/the.formatted.dark.side").unwrap(), p.as_path());
    ///
    /// p.set_extension("cookie");
    /// assert_eq!(AbsPath::try_new("/feel/the.formatted.dark.cookie").unwrap(), p.as_path());
    ///
    /// p.set_extension("");
    /// assert_eq!(AbsPath::try_new("/feel/the.formatted.dark").unwrap(), p.as_path());
    ///
    /// p.add_extension("");
    /// assert_eq!(AbsPath::try_new("/feel/the.formatted.dark").unwrap(), p.as_path());
    /// ```
    pub fn add_extension<S: AsRef<OsStr>>(&mut self, extension: S) -> bool {
        self.inner.add_extension(extension)
    }

    /// Consumes the `PathBuf`, yielding its internal [`OsString`] storage.
    ///
    /// # Examples
    ///
    /// ```
    /// use relabs::AbsPathBuf;
    ///
    /// let p = AbsPathBuf::try_from("/the/head").unwrap();
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
    pub fn replace_with<T, P>(self, path: P) -> PathBuf<T>
    where
        T: PathFlavor,
        P: AsRef<Path<T>>,
    {
        let mut inner = self.into_std();
        inner.clear();
        inner.push(path.as_ref().as_std());
        debug_assert!(T::accepts(&inner));
        PathBuf::<T>::new_trusted(inner)
    }

    // Borrowed input. Reuses existing allocation. Does not change flavor.
    // Is a clear followed by std's push.
    // Use `replace_with` to change flavor.
    #[inline]
    pub fn set<P: AsRef<Path<Flavor>>>(&mut self, new: P) {
        let p = new.as_ref().as_std();
        self.inner.clear();
        self.inner.push(p);
        debug_assert!(Flavor::accepts(&self.inner));
    }

    /// Untyped fallible version of [`set`].
    #[inline]
    pub fn try_set<P: AsRef<std::path::Path>>(&mut self, new: P) -> Result<(), PathFlavorError> {
        self.set(Path::<Flavor>::try_new(&new)?);
        Ok(())
    }

    /// Appends a relative path segment to this buffer.
    #[inline]
    pub fn push<P: AsRef<RelPath>>(&mut self, rhs: P) {
        self.inner.push(rhs.as_ref().as_std());
        debug_assert!(Flavor::accepts(&self.inner));
    }

    /// Untyped fallible version of [`push`].
    #[inline]
    pub fn try_push<P: AsRef<std::path::Path>>(&mut self, rhs: P) -> Result<(), PathFlavorError> {
        self.push(RelPath::try_new(&rhs)?);
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
    /// use relabs::AnyPathBuf;
    ///
    /// let path = AnyPathBuf::new();
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
    /// use relabs::{AnyPathBuf, AnyPath};
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
    /// Truncates the `OsString` to zero length.
    ///
    /// [`clear`]: OsString::clear
    #[inline]
    pub fn clear(&mut self) {
        self.inner.clear();
    }

    /// Consumes and leaks the `AnyPathBuf`, returning a mutable reference to the contents,
    /// `&'a mut AnyPath`.
    ///
    /// The caller has free choice over the returned lifetime, including 'static.
    /// Indeed, this function is ideally used for data that lives for the remainder of
    /// the program's life, as dropping the returned reference will cause a memory leak.
    ///
    /// It does not reallocate or shrink the `PathBuf`, so the leaked allocation may include
    /// unused capacity that is not part of the returned slice. If you want to discard excess
    /// capacity, call [`into_boxed_path`], and then [`Box::leak`] instead.
    /// However, keep in mind that trimming the capacity may result in a reallocation and copy.
    ///
    /// [`into_boxed_path`]: Self::into_boxed_path
    #[inline]
    pub fn leak<'a>(self) -> &'a mut AnyPath {
        convert_mut(self.inner.leak())
    }

    /// Consumes a [`AnyPathBuf`], returning an `Ok` [`AbsPathBuf`] if the [`AnyPathBuf`]
    /// is absolute. Otherwise, returns the original [`AnyPathBuf`] as an `Err`.
    ///
    /// # Examples
    ///
    /// ```
    /// use relabs::AnyPathBuf;
    ///
    /// assert!(AnyPathBuf::from("test.txt").try_into_absolute().is_err());
    /// ```
    #[inline]
    pub fn try_into_absolute(self) -> Result<AbsPathBuf, Self> {
        AbsPathBuf::try_from(self)
    }

    /// Consumes a [`AnyPathBuf`], returning an `Ok` [`RelPathBuf`] if the [`AnyPathBuf`]
    /// is absolute. Otherwise, returns the original [`AnyPathBuf`] as an `Err`.
    ///
    /// # Examples
    ///
    /// ```
    /// use relabs::AnyPathBuf;
    ///
    /// assert!(AnyPathBuf::from("test.txt").try_into_absolute().is_err());
    /// ```
    #[inline]
    pub fn try_into_relative(self) -> Result<RelPathBuf, Self> {
        RelPathBuf::try_from(self)
    }
}

impl PathBuf<Relative> {
    /// Allocates an empty [`RelPathBuf`].
    ///
    /// # Examples
    ///
    /// ```
    /// use relabs::RelPathBuf;
    ///
    /// let path = RelPathBuf::new();
    /// ```
    #[inline]
    pub fn new() -> Self {
        let new = Self::new_trusted(std::path::PathBuf::new());
        debug_assert!(Relative::accepts(&new.inner));
        new
    }

    /// Invokes [`clear`] on the underlying instance of [`OsString`].
    /// Truncates the `OsString` to zero length.
    ///
    /// [`clear`]: OsString::clear
    #[inline]
    pub fn clear(&mut self) {
        self.inner.clear();
        debug_assert!(Relative::accepts(&self.inner));
    }
}

impl PathBuf<Absolute> {}

impl<Flavor: StdPush> PathBuf<Flavor> {
    #[inline]
    pub fn push_std<P: AsRef<std::path::Path>>(&mut self, rhs: P) {
        self.inner.push(rhs.as_ref());
        debug_assert!(Flavor::accepts(&self.inner));
    }
}

//////////////////////////////////////////////////////////////
// Trait implementations
//////////////////////////////////////////////////////////////

impl Default for AnyPathBuf {
    fn default() -> Self {
        Self {
            _flavor: PhantomData,
            inner: std::path::PathBuf::default(),
        }
    }
}

impl<Flavor: PathFlavor> Deref for PathBuf<Flavor> {
    type Target = Path<Flavor>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_path()
    }
}

impl<Flavor: PathFlavor> DerefMut for PathBuf<Flavor> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Path<Flavor> {
        internal::convert_mut(&mut self.inner)
    }
}

impl<Flavor: PathFlavor> Clone for PathBuf<Flavor> {
    #[inline]
    fn clone(&self) -> Self {
        Self {
            _flavor: PhantomData,
            inner: self.inner.clone(),
        }
    }

    /// Clones the contents of `source` into `self`.
    ///
    /// This method is preferred over simply assigning `source.clone()` to `self`,
    /// as it avoids reallocation if possible.
    #[inline]
    fn clone_from(&mut self, source: &Self) {
        self.inner.clone_from(&source.inner)
    }
}

impl<P, Flavor> Extend<P> for PathBuf<Flavor>
where
    Flavor: PathFlavor,
    P: AsRef<RelPath>,
{
    /// Extends `self` with trusted [`RelPath`] elements from `iter`.
    ///
    /// This implementation requires inputs to be strictly typed as `AsRef<RelPath>`,
    /// ensuring at compile time that only valid relative paths are appended.
    ///
    /// To extend using untrusted types (like `&str`), use [`try_extend`](Self::try_extend) instead.
    ///
    /// # Examples
    ///
    /// ```
    /// use relabs::{AbsPathBuf, PathBuf, RelPath};
    ///
    /// let mut abs_path = AbsPathBuf::try_from("/tmp").unwrap();
    ///
    /// // Inputs must be strictly typed relative paths
    /// let components = ["foo", "bar", "file.txt"]
    ///     .map(|s| RelPath::try_new(s).unwrap());
    ///
    /// abs_path.extend(components);
    ///
    /// assert_eq!(abs_path, PathBuf::from("/tmp/foo/bar/file.txt"));
    /// ```
    fn extend<T: IntoIterator<Item = P>>(&mut self, iter: T) {
        iter.into_iter().for_each(move |p| self.push(p.as_ref()));
    }
}

impl<Flavor: PathFlavor> PathBuf<Flavor> {
    /// Extends `self` with path elements from `iter`, verifying at runtime that they are relative.
    ///
    /// Unlike [`Extend::extend`], this method accepts untrusted standard types (like `&str`,
    /// `String`, or `std::path::Path`) and validates that each component is a relative path.
    ///
    /// # Errors
    ///
    /// Returns a [`PathFlavorError`](crate::errors::PathFlavorError) if any element in `iter` is an absolute path.
    ///
    /// If an error occurs, the function returns immediately. **Note:** The buffer `self`
    /// will remain modified with any components that were successfully pushed *before*
    /// the error occurred.
    ///
    /// # Examples
    ///
    /// Successful extension using strings:
    ///
    /// ```
    /// use relabs::{AbsPathBuf, PathBuf};
    ///
    /// let mut abs_path = AbsPathBuf::try_from("/tmp").unwrap();
    ///
    /// // Safe to use raw strings here because they are checked at runtime
    /// abs_path.try_extend(["foo", "bar", "file.txt"]).unwrap();
    ///
    /// assert_eq!(abs_path, PathBuf::from("/tmp/foo/bar/file.txt"));
    /// ```
    ///
    /// Fails if an absolute path is encountered:
    ///
    /// ```
    /// use relabs::AbsPathBuf;
    ///
    /// let mut abs_path = AbsPathBuf::try_from("/tmp").unwrap();
    ///
    /// // The component "/bar" is absolute, so this returns an error
    /// assert!(abs_path.try_extend(["foo", "/bar"]).is_err());
    /// ```
    pub fn try_extend<I, P>(&mut self, iter: I) -> Result<(), crate::errors::PathFlavorError>
    where
        I: IntoIterator<Item = P>,
        P: AsRef<std::path::Path>,
    {
        for p in iter {
            let rel_segment = RelPath::try_new(p.as_ref())?;
            self.inner.push(rel_segment.as_std());
        }
        Ok(())
    }
}

impl<Flavor: PathFlavor> Borrow<Path<Flavor>> for PathBuf<Flavor> {
    #[inline]
    fn borrow(&self) -> &Path<Flavor> {
        self.deref()
    }
}

impl<Flavor: PathFlavor> Hash for PathBuf<Flavor> {
    fn hash<H: Hasher>(&self, h: &mut H) {
        self.inner.hash(h)
    }
}

impl FromStr for AnyPathBuf {
    type Err = Infallible;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(s.into())
    }
}

impl FromStr for AbsPathBuf {
    type Err = std::path::PathBuf;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        s.try_into()
    }
}

impl FromStr for RelPathBuf {
    type Err = std::path::PathBuf;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        s.try_into()
    }
}

//////////////////////////////////////////////////////////////
// Conversions
//////////////////////////////////////////////////////////////

impl<'a, Flavor: PathFlavor> From<&'a PathBuf<Flavor>> for Cow<'a, Path<Flavor>> {
    /// Creates a clone-on-write pointer from a reference to
    /// [`PathBuf<Flavor>`].
    ///
    /// This conversion does not clone or allocate.
    #[inline]
    fn from(p: &'a PathBuf<Flavor>) -> Cow<'a, Path<Flavor>> {
        Cow::Borrowed(p.as_path())
    }
}

impl<T: ?Sized + AsRef<RelPath>> From<&T> for RelPathBuf {
    #[inline]
    fn from(s: &T) -> Self {
        Self::new_trusted(s.as_ref().into())
    }
}

impl<T: ?Sized + AsRef<AbsPathBuf>> From<&T> for AbsPathBuf {
    #[inline]
    fn from(s: &T) -> Self {
        Self::new_trusted(s.as_ref().into())
    }
}

impl<T: ?Sized + AsRef<OsStr>> From<&T> for AnyPathBuf {
    #[inline]
    fn from(s: &T) -> Self {
        Self::new_trusted(s.as_ref().into())
    }
}

impl<Flavor: PathFlavor> From<Box<Path<Flavor>>> for PathBuf<Flavor> {
    /// Converts `Box<Path<Flavor>>` into a [`PathBuf<Flavor>`].
    ///
    /// This conversion does not allocate or copy memory.
    #[inline]
    fn from(boxed: Box<Path<Flavor>>) -> Self {
        boxed.into_path_buf()
    }
}

impl<'a, Flavor: PathFlavor> From<Cow<'a, Path<Flavor>>> for PathBuf<Flavor> {
    /// Converts a clone-on-write pointer to an owned path.
    ///
    /// Converting from a `Cow::Owned` does not clone or allocate.
    #[inline]
    fn from(p: Cow<'a, Path<Flavor>>) -> Self {
        p.into_owned()
    }
}

impl<Flavor: PathFlavor> From<OsString> for PathBuf<Flavor> {
    /// Converts an [`OsString`] into a [`PathBuf`].
    ///
    /// This conversion does not allocate or copy memory.
    #[inline]
    fn from(s: OsString) -> Self {
        Self {
            _flavor: PhantomData,
            inner: s.into(),
        }
    }
}

impl<Flavor: PathFlavor> From<PathBuf<Flavor>> for Arc<Path<Flavor>> {
    /// Converts a [`PathBuf<Flavor>`] into an [`Arc`]`<`[`Path<Flavor>`]`>` by moving the
    /// [`PathBuf<Flavor>`] data into a new [`Arc`] buffer.
    #[inline]
    fn from(s: PathBuf<Flavor>) -> Arc<Path<Flavor>> {
        Arc::from(s.into_boxed_path())
    }
}

impl<Flavor: PathFlavor> From<PathBuf<Flavor>> for Box<Path<Flavor>> {
    /// Converts a [`PathBuf<Flavor>`] into a [`Box`]`<`[`Path<Flavor>`]`>`.
    ///
    /// This conversion currently should not allocate memory,
    /// but this behavior is not guaranteed on all platforms or in all future versions.
    #[inline]
    fn from(p: PathBuf<Flavor>) -> Box<Path<Flavor>> {
        p.into_boxed_path()
    }
}

impl<'a, Flavor: PathFlavor> From<PathBuf<Flavor>> for Cow<'a, Path<Flavor>> {
    /// Creates a clone-on-write pointer from an owned
    /// instance of [`PathBuf<Flavor>`].
    ///
    /// This conversion does not clone or allocate.
    #[inline]
    fn from(s: PathBuf<Flavor>) -> Cow<'a, Path<Flavor>> {
        Cow::Owned(s)
    }
}

impl<Flavor: PathFlavor> From<PathBuf<Flavor>> for OsString {
    /// Converts a [`PathBuf<Flavor>`] into an [`OsString`]
    ///
    /// This conversion does not allocate or copy memory.
    #[inline]
    fn from(path_buf: PathBuf<Flavor>) -> OsString {
        path_buf.inner.into_os_string()
    }
}

impl<Flavor: PathFlavor> From<PathBuf<Flavor>> for Rc<Path<Flavor>> {
    /// Converts a [`PathBuf<Flavor>`] into an [`Rc`]`<`[`Path<Flavor>`]`>` by moving the
    /// [`PathBuf<Flavor>`] data into a new [`Rc`] buffer.
    #[inline]
    fn from(s: PathBuf<Flavor>) -> Rc<Path<Flavor>> {
        Rc::from(s.into_boxed_path())
    }
}

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

impl TryFrom<&std::path::Path> for AbsPathBuf {
    type Error = std::path::PathBuf;

    fn try_from(path: &std::path::Path) -> Result<Self, Self::Error> {
        Self::try_from(path.to_path_buf())
    }
}

impl TryFrom<&std::path::Path> for RelPathBuf {
    type Error = std::path::PathBuf;

    fn try_from(path: &std::path::Path) -> Result<Self, Self::Error> {
        Self::try_from(path.to_path_buf())
    }
}

impl TryFrom<&str> for AbsPathBuf {
    type Error = std::path::PathBuf;

    fn try_from(s: &str) -> Result<Self, Self::Error> {
        let path = std::path::Path::new(s);
        if Absolute::accepts(path) {
            Ok(Self::new_trusted(path.to_path_buf()))
        } else {
            Err(path.to_path_buf())
        }
    }
}

impl TryFrom<String> for AbsPathBuf {
    type Error = std::path::PathBuf;

    fn try_from(s: String) -> Result<Self, Self::Error> {
        let inner = std::path::PathBuf::from(s);
        if <Absolute as PathFlavor>::accepts(&inner) {
            Ok(Self::new_trusted(inner))
        } else {
            Err(inner)
        }
    }
}

impl TryFrom<&str> for RelPathBuf {
    type Error = std::path::PathBuf;

    fn try_from(s: &str) -> Result<Self, Self::Error> {
        let path = std::path::Path::new(s);
        if <Relative as PathFlavor>::accepts(path) {
            Ok(Self::new_trusted(path.to_path_buf()))
        } else {
            Err(path.to_path_buf())
        }
    }
}

impl TryFrom<String> for RelPathBuf {
    type Error = std::path::PathBuf;

    fn try_from(s: String) -> Result<Self, Self::Error> {
        let inner = std::path::PathBuf::from(s);
        if <Relative as PathFlavor>::accepts(&inner) {
            Ok(Self::new_trusted(inner))
        } else {
            Err(inner)
        }
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

//////////////////////////////////////////////////////////////
// Comparisons
//////////////////////////////////////////////////////////////

impl<L, R> PartialEq<PathBuf<R>> for PathBuf<L>
where
    L: PathFlavor,
    R: PathFlavor,
{
    fn eq(&self, other: &PathBuf<R>) -> bool {
        self.inner == other.inner
    }
}

impl<Flavor: PathFlavor> Eq for PathBuf<Flavor> {}

impl<L, R> PartialEq<Path<R>> for PathBuf<L>
where
    L: PathFlavor,
    R: PathFlavor,
{
    fn eq(&self, other: &Path<R>) -> bool {
        self.inner.as_path() == other.as_std()
    }
}

impl<L, R> PartialEq<&Path<R>> for PathBuf<L>
where
    L: PathFlavor,
    R: PathFlavor,
{
    fn eq(&self, other: &&Path<R>) -> bool {
        self.inner.as_path() == other.as_std()
    }
}

impl<P> FromIterator<P> for RelPathBuf
where
    P: AsRef<RelPath>,
{
    /// Constructs a [`RelPathBuf`] from trusted relative path components.
    ///
    /// Because the input types are strictly bound to `AsRef<RelPath>`, we guarantee
    /// at compile time that the resulting path is relative. No runtime checks or
    /// panics are required.
    ///
    /// # Examples
    ///
    /// ```
    /// use relabs::{RelPathBuf, RelPath, PathBuf};
    ///
    /// // Inputs must be strictly typed `RelPath`s.
    /// // (If you have raw strings, use `try_new` first or use `try_extend`).
    /// let parts = [
    ///     RelPath::try_new("src").unwrap(),
    ///     RelPath::try_new("main.rs").unwrap(),
    /// ];
    ///
    /// let path: RelPathBuf = parts.into_iter().collect();
    /// assert_eq!(path, PathBuf::from("src/main.rs"));
    /// ```
    fn from_iter<T: IntoIterator<Item = P>>(iter: T) -> Self {
        let mut inner = std::path::PathBuf::new();
        // Since we only accept RelPath, we know 'inner' will never become Absolute.
        iter.into_iter()
            .for_each(|p| inner.push(p.as_ref().as_std()));
        Self::new_trusted(inner)
    }
}

impl<P> FromIterator<P> for AnyPathBuf
where
    P: AsRef<std::path::Path>,
{
    /// Constructs an [`AnyPathBuf`] from any path components.
    fn from_iter<T: IntoIterator<Item = P>>(iter: T) -> Self {
        let mut inner = std::path::PathBuf::new();
        inner.extend(iter);
        Self::new_trusted(inner)
    }
}

// We intentionally DO NOT implement FromIterator for AbsPathBuf.
//
// Reason: `collect()` assumes valid output from homogenous inputs.
// - If inputs are Relative: Result is Relative (Invalid AbsPathBuf).
// - If inputs are Absolute: Result is valid, but this is a rare edge case.
//
// To build an AbsPathBuf, users should start with a valid root and extend:
// `let p = AbsPathBuf::try_from("/usr").unwrap();`
// `p.extend(relative_parts);`

impl<'a, Flavor: PathFlavor> IntoIterator for &'a PathBuf<Flavor> {
    type Item = &'a OsStr;

    type IntoIter = std::path::Iter<'a>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
