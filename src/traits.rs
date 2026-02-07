// ============================================================================
// Core Standard Traits (Clone, Default, ToOwned, Deref)
// ============================================================================

use std::{
    borrow::{Borrow, Cow},
    cmp::Ordering,
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
    AbsPathBuf, Absolute, Any, AnyPathBuf, Path, PathBuf, PathFlavor, RelPath, RelPathBuf,
    Relative, internal,
};

impl Default for AnyPathBuf {
    fn default() -> Self {
        Self::new_trusted(std::path::PathBuf::default())
    }
}

impl Default for RelPathBuf {
    fn default() -> Self {
        Self::new_trusted(std::path::PathBuf::default())
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
        self.inner.clone_from(&source.inner);
    }
}

impl<P, Flavor> Extend<P> for PathBuf<Flavor>
where
    Flavor: PathFlavor,
    P: AsRef<RelPath>,
{
    /// Extends the path with trusted relative segments.
    ///
    /// This is a compile-time safe version of extension.
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

impl<Flavor: PathFlavor> Borrow<Path<Flavor>> for PathBuf<Flavor> {
    #[inline]
    fn borrow(&self) -> &Path<Flavor> {
        self.as_path()
    }
}

impl<Flavor: PathFlavor> Hash for PathBuf<Flavor> {
    fn hash<H: Hasher>(&self, h: &mut H) {
        self.inner.hash(h);
    }
}

impl<Flavor: PathFlavor> std::hash::Hash for Path<Flavor> {
    #[inline]
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.inner.hash(state);
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

impl<Flavor> fmt::Debug for Path<Flavor>
where
    Flavor: PathFlavor,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_std_path().fmt(f)
    }
}

// ============================================================================
// Conversions (AsRef, From, TryFrom)
// ============================================================================

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

impl<'a, Flavor: PathFlavor> From<&'a PathBuf<Flavor>> for Cow<'a, Path<Flavor>> {
    /// Creates a clone-on-write pointer from a reference to
    /// [`PathBuf<Flavor>`].
    ///
    /// This conversion does not clone or allocate.
    #[inline]
    fn from(p: &'a PathBuf<Flavor>) -> Self {
        Cow::Borrowed(p.as_path())
    }
}

impl<T: ?Sized + AsRef<RelPath>> From<&T> for RelPathBuf {
    #[inline]
    fn from(s: &T) -> Self {
        Self::new_trusted(s.as_ref().into())
    }
}

impl<T: ?Sized + AsRef<Self>> From<&T> for AbsPathBuf {
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

impl<Flavor: PathFlavor> From<PathBuf<Flavor>> for OsString {
    /// Converts a [`PathBuf<Flavor>`] into an [`OsString`]
    ///
    /// This conversion does not allocate or copy memory.
    #[inline]
    fn from(path_buf: PathBuf<Flavor>) -> Self {
        path_buf.inner.into_os_string()
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

impl TryFrom<AnyPathBuf> for RelPathBuf {
    type Error = AnyPathBuf;
    fn try_from(path: AnyPathBuf) -> Result<Self, Self::Error> {
        Self::try_from(path.inner).map_err(AnyPathBuf::new_trusted)
    }
}

impl TryFrom<AnyPathBuf> for AbsPathBuf {
    type Error = AnyPathBuf;
    fn try_from(path: AnyPathBuf) -> Result<Self, Self::Error> {
        Self::try_from(path.inner).map_err(AnyPathBuf::new_trusted)
    }
}

impl From<String> for AnyPathBuf {
    fn from(value: String) -> Self {
        Self::new_trusted(std::path::PathBuf::from(value))
    }
}

// =============================================================================
// Smart Pointers (Box, Arc, Rc, Cow)
// =============================================================================

macro_rules! impl_smart_ptrs {
    ($Flavor:ty) => {
        // PathBuf<F> -> Box<Path<F>>
        impl From<PathBuf<$Flavor>> for Box<Path<$Flavor>> {
            #[inline]
            fn from(p: PathBuf<$Flavor>) -> Self {
                p.into_boxed_path()
            }
        }

        // Box<Path<F>> -> PathBuf<F>
        impl From<Box<Path<$Flavor>>> for PathBuf<$Flavor> {
            #[inline]
            fn from(b: Box<Path<$Flavor>>) -> Self {
                b.into_path_buf()
            }
        }

        impl Clone for Box<Path<$Flavor>> {
            fn clone(&self) -> Self {
                self.to_path_buf().into_boxed_path()
            }
        }

        // &Path<F> -> Box<Path<F>>
        impl From<&Path<$Flavor>> for Box<Path<$Flavor>> {
            #[inline]
            fn from(p: &Path<$Flavor>) -> Self {
                p.to_path_buf().into_boxed_path()
            }
        }

        // Box<Path<F>> -> Box<std::path::Path>
        impl From<Box<Path<$Flavor>>> for Box<std::path::Path> {
            #[inline]
            fn from(b: Box<Path<$Flavor>>) -> Self {
                let raw = Box::into_raw(b) as *mut std::path::Path;
                unsafe { Box::from_raw(raw) }
            }
        }

        // PathBuf<F> -> Cow<'a, Path<F>>
        impl<'a> From<PathBuf<$Flavor>> for Cow<'a, Path<$Flavor>> {
            #[inline]
            fn from(p: PathBuf<$Flavor>) -> Self {
                Cow::Owned(p)
            }
        }

        // &Path<F> -> Cow<'a, Path<F>>
        impl<'a> From<&'a Path<$Flavor>> for Cow<'a, Path<$Flavor>> {
            #[inline]
            fn from(p: &'a Path<$Flavor>) -> Self {
                Cow::Borrowed(p)
            }
        }

        // Cow<'a, Path<F>> -> PathBuf<F>
        impl<'a> From<Cow<'a, Path<$Flavor>>> for PathBuf<$Flavor> {
            #[inline]
            fn from(c: Cow<'a, Path<$Flavor>>) -> Self {
                c.into_owned()
            }
        }

        // Cow<'a, Path<F>> -> Box<Path<F>>
        impl<'a> From<Cow<'a, Path<$Flavor>>> for Box<Path<$Flavor>> {
            #[inline]
            fn from(c: Cow<'a, Path<$Flavor>>) -> Self {
                c.into_owned().into_boxed_path()
            }
        }

        // PathBuf<F> -> Arc<Path<F>>
        impl From<PathBuf<$Flavor>> for Arc<Path<$Flavor>> {
            #[inline]
            fn from(p: PathBuf<$Flavor>) -> Self {
                Arc::from(p.into_boxed_path())
            }
        }

        // &Path<F> -> Arc<Path<F>>
        impl From<&Path<$Flavor>> for Arc<Path<$Flavor>> {
            #[inline]
            fn from(p: &Path<$Flavor>) -> Self {
                Arc::from(p.to_path_buf().into_boxed_path())
            }
        }

        // PathBuf<F> -> Rc<Path<F>>
        impl From<PathBuf<$Flavor>> for Rc<Path<$Flavor>> {
            #[inline]
            fn from(p: PathBuf<$Flavor>) -> Self {
                Rc::from(p.into_boxed_path())
            }
        }

        // &Path<F> -> Rc<Path<F>>
        impl From<&Path<$Flavor>> for Rc<Path<$Flavor>> {
            #[inline]
            fn from(p: &Path<$Flavor>) -> Self {
                Rc::from(p.to_path_buf().into_boxed_path())
            }
        }
    };
}

impl_smart_ptrs!(Any);
impl_smart_ptrs!(Absolute);
impl_smart_ptrs!(Relative);

// =============================================================================
//  Comparisons (PartialEq, Ord, Hash)
// =============================================================================

impl<L, R> PartialEq<PathBuf<R>> for PathBuf<L>
where
    L: PathFlavor,
    R: PathFlavor,
{
    /// Checks if two paths are equal, regardless of their type-level flavors.
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
        self.inner.as_path() == other.as_std_path()
    }
}

impl<L, R> PartialEq<&Path<R>> for PathBuf<L>
where
    L: PathFlavor,
    R: PathFlavor,
{
    fn eq(&self, other: &&Path<R>) -> bool {
        self.inner.as_path() == other.as_std_path()
    }
}

impl<Flavor: PathFlavor> PartialEq for Path<Flavor> {
    fn eq(&self, other: &Self) -> bool {
        self.inner == other.inner
    }
}

impl<Flavor: PathFlavor> Eq for Path<Flavor> {}

impl<L, R> PartialEq<PathBuf<R>> for Path<L>
where
    L: PathFlavor,
    R: PathFlavor,
{
    fn eq(&self, other: &PathBuf<R>) -> bool {
        self.as_std_path() == other.as_std_path()
    }
}

impl<Flavor: PathFlavor> PartialEq<PathBuf<Flavor>> for &Path<Flavor> {
    fn eq(&self, other: &PathBuf<Flavor>) -> bool {
        *self == other.as_path()
    }
}

// Cross-type comparison
impl<Flavor: PathFlavor> PartialEq<std::path::PathBuf> for Path<Flavor> {
    #[inline]
    fn eq(&self, other: &std::path::PathBuf) -> bool {
        &self.inner == other.as_path()
    }
}

impl<Flavor: PathFlavor> PartialEq<Path<Flavor>> for std::path::PathBuf {
    #[inline]
    fn eq(&self, other: &Path<Flavor>) -> bool {
        self.as_path() == &other.inner
    }
}

impl<Flavor: PathFlavor> PartialEq<std::path::Path> for Path<Flavor> {
    #[inline]
    fn eq(&self, other: &std::path::Path) -> bool {
        &self.inner == other
    }
}

impl<Flavor: PathFlavor> PartialEq<Path<Flavor>> for std::path::Path {
    #[inline]
    fn eq(&self, other: &Path<Flavor>) -> bool {
        self == &other.inner
    }
}

impl<Flavor: PathFlavor> PartialEq<std::path::PathBuf> for PathBuf<Flavor> {
    #[inline]
    fn eq(&self, other: &std::path::PathBuf) -> bool {
        self.inner == *other
    }
}

impl<Flavor: PathFlavor> PartialEq<PathBuf<Flavor>> for std::path::PathBuf {
    #[inline]
    fn eq(&self, other: &PathBuf<Flavor>) -> bool {
        *self == other.inner
    }
}

impl<Flavor: PathFlavor> PartialEq<std::path::Path> for PathBuf<Flavor> {
    #[inline]
    fn eq(&self, other: &std::path::Path) -> bool {
        self.inner == other
    }
}

impl<Flavor: PathFlavor> PartialEq<PathBuf<Flavor>> for std::path::Path {
    #[inline]
    fn eq(&self, other: &PathBuf<Flavor>) -> bool {
        self == other.inner
    }
}

impl<Flavor: PathFlavor> PartialOrd for Path<Flavor> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<Flavor: PathFlavor> Ord for Path<Flavor> {
    #[inline]
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.inner.cmp(&other.inner)
    }
}

impl<Flavor: PathFlavor> PartialOrd for PathBuf<Flavor> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<Flavor: PathFlavor> Ord for PathBuf<Flavor> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.inner.cmp(&other.inner)
    }
}

macro_rules! impl_eq_utf8 {
    ($($Type:ty),+) => {
        $(
            impl<Flavor: PathFlavor> PartialEq<$Type> for PathBuf<Flavor> {
                #[inline]
                fn eq(&self, other: &$Type) -> bool {
                    self.inner.as_path() == std::path::Path::new(other)
                }
            }

            impl<Flavor: PathFlavor> PartialEq<PathBuf<Flavor>> for $Type {
                #[inline]
                fn eq(&self, other: &PathBuf<Flavor>) -> bool {
                    std::path::Path::new(self) == other.inner.as_path()
                }
            }
        )+
    };
}

impl<Flavor: PathFlavor> ToOwned for Path<Flavor> {
    type Owned = PathBuf<Flavor>;

    #[inline]
    fn to_owned(&self) -> Self::Owned {
        self.to_path_buf()
    }

    #[inline]
    fn clone_into(&self, target: &mut PathBuf<Flavor>) {
        self.inner.clone_into(target.unsafe_inner_mut());
    }
}

impl_eq_utf8! {
    str,
    &str,
    String
}

macro_rules! impl_cmp {
    ($($Type:ty),+) => {
        $(
            impl<Flavor: PathFlavor> PartialEq<$Type> for Path<Flavor> {
                #[inline]
                fn eq(&self, other: &$Type) -> bool {
                    &self.inner == std::path::Path::new(other)
                }
            }

            impl<Flavor: PathFlavor> PartialEq<Path<Flavor>> for $Type {
                #[inline]
                fn eq(&self, other: &Path<Flavor>) -> bool {
                    std::path::Path::new(self) == &other.inner
                }
            }
        )+
    };
}

impl_cmp!(
    str,
    &str,
    String,
    OsStr,
    &OsStr,
    std::ffi::OsString,
    Cow<'_, OsStr>
);
