use std::path::{Path, PathBuf as StdPathBuf};

use relabs::{AbsPathBuf, AnyPathBuf, RelPath, RelPathBuf};

fn get_absolute_str() -> &'static str {
    if cfg!(windows) { r"C:\Windows" } else { "/usr" }
}

fn get_relative_str() -> &'static str {
    if cfg!(windows) {
        r"Users\Test"
    } else {
        "users/test"
    }
}

fn get_root_str() -> &'static str {
    if cfg!(windows) { r"C:\" } else { "/" }
}

// Invariant Construction Tests

#[test]
fn test_absolute_construction() {
    let abs_str = get_absolute_str();
    let rel_str = get_relative_str();

    // Should succeed
    let abs = AbsPathBuf::try_from(abs_str);
    assert!(abs.is_ok(), "Valid absolute path rejected");

    // Should fail
    let fail = AbsPathBuf::try_from(rel_str);
    assert!(fail.is_err(), "Invalid relative path accepted as Absolute");
}

#[test]
fn test_relative_construction() {
    let abs_str = get_absolute_str();
    let rel_str = get_relative_str();

    // Should succeed
    let rel = RelPathBuf::try_from(rel_str);
    assert!(rel.is_ok(), "Valid relative path rejected");

    // Should fail
    let fail = RelPathBuf::try_from(abs_str);
    assert!(fail.is_err(), "Invalid absolute path accepted as Relative");
}

// Push vs Push_Std Behavior

#[test]
fn test_relpath_push_strictness() {
    let mut p = RelPathBuf::try_from("a").unwrap();
    let part = RelPath::try_new("b").unwrap();

    // Strict push (Always Appends)
    p.push(part);

    let expected = if cfg!(windows) { r"a\b" } else { "a/b" };
    assert_eq!(p.as_std(), Path::new(expected));
}

#[test]
fn test_abspath_push_std_replacement() {
    // Test strict `push` (append)
    let mut p = AbsPathBuf::try_from(get_absolute_str()).unwrap();
    p.push(RelPath::try_new("bin").unwrap()); // Appends

    // Test `push_std` (std behavior: replace if absolute)
    let new_root = get_root_str();
    p.push_std(new_root); // Should replace the whole path with root

    assert_eq!(p.as_std(), Path::new(new_root));
}

#[test]
fn test_anypath_push_std() {
    let mut p = AnyPathBuf::from("start");

    // `push_std` with absolute path should replace
    let abs = get_absolute_str();
    p.push_std(abs);

    assert_eq!(p.as_std(), Path::new(abs));
}

#[test]
fn test_try_extend_validation() {
    let mut p = RelPathBuf::try_from("a").unwrap();

    // Attempt to extend with an absolute path (should fail)
    let parts = vec![get_absolute_str()];
    let res = p.try_extend(parts);

    assert!(res.is_err());
    // Verify state did not change
    assert_eq!(p.as_std(), Path::new("a"));
}

// Pop Behavior (Invariant Protection)

#[test]
fn test_absolute_pop_safety() {
    let root = get_root_str();
    let mut p = AbsPathBuf::try_from(root).unwrap();

    // Should return false and NOT empty the string
    assert!(!p.pop());
    assert_eq!(p.as_std(), Path::new(root));

    // Ensure strictly typed wrapper didn't become empty
    assert_eq!(p.into_std().as_os_str().len(), root.len());
}

#[test]
fn test_relative_pop_safety() {
    let mut p = RelPathBuf::try_from("a").unwrap();

    assert!(p.pop()); // Becomes empty
    assert_eq!(p.as_std(), Path::new(""));

    // Pop on empty
    assert!(!p.pop());
}

// Zero-Cost & Allocation Tests

#[test]
fn test_replace_with_capacity_reuse() {
    let mut p = AnyPathBuf::with_capacity(1024);
    p.set("short");

    let cap_before = p.capacity();
    assert!(cap_before >= 1024);

    // Replace with a Relative path using the same allocation
    let rel_inputs = RelPath::try_new("longer/path/to/test").unwrap();
    let p_rel: RelPathBuf = p.replace_with(rel_inputs);

    let cap_after = p_rel.capacity();

    // The allocation should be preserved
    assert_eq!(cap_before, cap_after);
    assert_eq!(p_rel.as_std(), rel_inputs.as_std());
}

#[test]
fn test_transparent_representation() {
    use std::mem;

    assert_eq!(mem::size_of::<AbsPathBuf>(), mem::size_of::<StdPathBuf>());
    assert_eq!(mem::align_of::<AbsPathBuf>(), mem::align_of::<StdPathBuf>());

    assert_eq!(mem::size_of::<&relabs::AbsPath>(), mem::size_of::<&Path>());
}

// Flavor Conversions

#[test]
fn test_any_conversions() {
    let abs_str = get_absolute_str();
    let rel_str = get_relative_str();

    // Any -> Rel (Success)
    let any_rel = AnyPathBuf::from(rel_str);
    assert!(any_rel.clone().try_into_relative().is_ok());
    assert!(any_rel.try_into_absolute().is_err());

    // Any -> Abs (Success)
    let any_abs = AnyPathBuf::from(abs_str);
    assert!(any_abs.clone().try_into_absolute().is_ok());
    assert!(any_abs.try_into_relative().is_err());
}

// Setters

#[test]
fn test_set_file_name_typed() {
    let mut p = RelPathBuf::try_from("dir/old.txt").unwrap();
    let new_name = RelPath::try_new("new.md").unwrap();

    p.set_file_name(new_name);

    let expected = if cfg!(windows) {
        r"dir\new.md"
    } else {
        "dir/new.md"
    };
    assert_eq!(p.as_std(), Path::new(expected));
}

// This test ensures the `RelPath` trait bound prevents compiling logic that
// would attempt to set an absolute path as a filename.
// Uncommenting the lines below should fail to compile.
/*
#[test]
fn test_compile_fail_set_file_name() {
     let mut p = RelPathBuf::new();
     let abs = AbsPathBuf::try_from("/tmp").unwrap();
     p.set_file_name(&abs); // ERROR: AbsPath does not implement AsRef<RelPath>
}
*/
