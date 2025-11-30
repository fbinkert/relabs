use crate::{
    flavors::{CanJoin, PathFlavor},
    path::Path,
    pathbuf::PathBuf,
};

// Generic join core restricted to flavor-compatible LHS and RHS.
#[must_use]
#[inline]
pub(crate) fn join_impl<L, R>(lhs: &Path<L>, rhs: &Path<R>) -> PathBuf<<L as CanJoin<R>>::Output>
where
    L: CanJoin<R>,
    R: PathFlavor,
{
    let joined = lhs.as_inner().join(rhs.as_inner());
    // Safety: allowed pairs guarantee the resulting flavor matches CanJoin::Output
    debug_assert!(L::accepts(&joined));
    PathBuf::new_trusted(joined)
}
