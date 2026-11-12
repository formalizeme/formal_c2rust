use fs_c::fs::*;

use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU32, Ordering};

static ALPHA: &str = "abcdefghijklmnopqrstuvwxyz\n";
static COUNTER: AtomicU32 = AtomicU32::new(0);

/// Create an isolated temp directory for a single test, pre-populated with
/// a "file" (containing "hello") and a "file.link" symlink, matching the C
/// test's assumption that ./tmp/file and ./tmp/file.link already exist.
struct TestDir {
    path: PathBuf,
}

impl TestDir {
    fn new(label: &str) -> Self {
        let id = COUNTER.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "fs_c_test_{}_{}_{}",
            label,
            std::process::id(),
            id
        ));
        let _ = fs::remove_dir_all(&path);
        fs::create_dir_all(&path).expect("create test dir");

        // Pre-create "file" (C test assumes ./tmp/file exists)
        fs::write(path.join("file"), "hello").expect("create fixture file");

        // Pre-create "file.link" symlink (C test assumes ./tmp/file.link exists)
        std::os::unix::fs::symlink(
            path.join("file"),
            path.join("file.link"),
        )
        .expect("create fixture symlink");

        TestDir { path }
    }

    fn file(&self, name: &str) -> String {
        self.path.join(name).to_string_lossy().to_string()
    }
}

impl Drop for TestDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

#[test]
fn test_fs_open() {
    let t = TestDir::new("open");

    let fd = fs_open(&t.file("file"), FS_OPEN_READWRITE);
    assert!(fd.is_some());
    fs_close(fd.unwrap()).unwrap();

    let bad_fd = fs_open("/root/foo", FS_OPEN_WRITE);
    assert!(bad_fd.is_none());
}

#[test]
fn test_fs_close() {
    let t = TestDir::new("close");

    let fd = fs_open(&t.file("file"), FS_OPEN_READWRITE);
    assert!(fs_close(fd.unwrap()).is_ok());
}

#[test]
fn test_fs_mkdir() {
    let t = TestDir::new("mkdir");

    let dir_path = t.file("dir");
    let _ = fs_rmdir(&dir_path);
    assert!(fs_mkdir(&dir_path, 0o777).is_ok());
    assert!(fs_exists(&dir_path));
    assert!(fs_rmdir(&dir_path).is_ok());
}

#[test]
fn test_fs_exists() {
    let t = TestDir::new("exists");

    assert!(fs_exists(&t.file("file")));
    assert!(fs_exists(&t.file("file.link")));
    assert!(!fs_exists(&t.file("a file that doesn't exist")));
}

#[test]
fn test_fs_stat() {
    let t = TestDir::new("stat");

    let metadata = fs_stat(&t.file("file"));
    assert!(metadata.is_ok());

    let bad_metadata = fs_stat(&t.file("a file that doesn't exist"));
    assert!(bad_metadata.is_err());
}

#[test]
fn test_fs_fstat() {
    let t = TestDir::new("fstat");

    let fd = fs_open(&t.file("file"), FS_OPEN_READ).unwrap();
    let metadata = fs_fstat(&fd);
    assert!(metadata.is_ok());
    fs_close(fd).unwrap();
}

#[test]
fn test_fs_lstat() {
    let t = TestDir::new("lstat");

    let metadata = fs_lstat(&t.file("file.link"));
    assert!(metadata.is_ok());
}

#[test]
fn test_fs_truncate() {
    let t = TestDir::new("truncate");
    let alpha_path = t.file("alpha");

    fs_write(&alpha_path, ALPHA.as_bytes()).unwrap();
    assert!(fs_truncate(&alpha_path, 9).is_ok());

    let buf = fs_read(&alpha_path).unwrap();
    assert_eq!(buf, b"abcdefghi");
}

#[test]
fn test_fs_read() {
    let t = TestDir::new("read");

    // Read file and its symlink — contents should match
    let f1 = fs_read(&t.file("file")).unwrap();
    let f2 = fs_read(&t.file("file.link")).unwrap();
    assert_eq!(f1, f2);

    // GH-14
    let alpha_path = t.file("alpha");
    fs_write(&alpha_path, ALPHA.as_bytes()).unwrap();
    let buf = fs_read(&alpha_path).unwrap();
    assert_eq!(buf, ALPHA.as_bytes());
}

#[test]
fn test_fs_nread() {
    let t = TestDir::new("nread");
    let alpha_path = t.file("alpha");

    fs_write(&alpha_path, ALPHA.as_bytes()).unwrap();
    let buf = fs_nread(&alpha_path, 9).unwrap();
    assert_eq!(buf, b"abcdefghi");
}

#[test]
fn test_fs_fread() {
    let t = TestDir::new("fread");
    let alpha_path = t.file("alpha");

    fs_write(&alpha_path, ALPHA.as_bytes()).unwrap();
    let fd = fs_open(&alpha_path, FS_OPEN_READ).unwrap();
    let buf = fs_fread(&fd).unwrap();
    assert_eq!(buf, ALPHA.as_bytes());
    fs_close(fd).unwrap();
}

#[test]
fn test_fs_rename() {
    let t = TestDir::new("rename");
    let from_path = t.file("alpha");
    let to_path = t.file("foo");

    fs_write(&from_path, ALPHA.as_bytes()).unwrap();
    assert!(fs_rename(&from_path, &to_path).is_ok());
    assert!(!fs_exists(&from_path));

    let buf = fs_read(&to_path).unwrap();
    assert_eq!(buf, ALPHA.as_bytes());

    fs::remove_file(&to_path).unwrap();
}

#[test]
fn test_fs_rmdir() {
    let t = TestDir::new("rmdir");
    let dir_path = t.file("dir");

    assert!(fs_mkdir(&dir_path, 0o777).is_ok());
    assert!(fs_rmdir(&dir_path).is_ok());
    assert!(!fs_exists(&dir_path));
}

#[test]
fn test_fs_write() {
    let t = TestDir::new("write");
    let alpha_path = t.file("alpha");

    fs_write(&alpha_path, ALPHA.as_bytes()).unwrap();
    let buf = fs_read(&alpha_path).unwrap();
    assert_eq!(buf, ALPHA.as_bytes());
}

#[test]
fn test_fs_nwrite() {
    let t = TestDir::new("nwrite");
    let alpha_path = t.file("alpha");

    fs_nwrite(&alpha_path, ALPHA.as_bytes(), 9).unwrap();
    let buf = fs_read(&alpha_path).unwrap();
    assert_eq!(buf, b"abcdefghi");
}

#[test]
fn test_fs_fwrite() {
    let t = TestDir::new("fwrite");
    let alpha_path = t.file("alpha");

    let fd = fs_open(&alpha_path, FS_OPEN_WRITE).unwrap();
    fs_fwrite(&fd, ALPHA.as_bytes()).unwrap();
    fs_close(fd).unwrap();

    let buf = fs_read(&alpha_path).unwrap();
    assert_eq!(buf, ALPHA.as_bytes());
}

#[test]
fn test_fs_fnwrite() {
    let t = TestDir::new("fnwrite");
    let alpha_path = t.file("alpha");

    let fd = fs_open(&alpha_path, FS_OPEN_WRITE).unwrap();
    fs_fnwrite(&fd, ALPHA.as_bytes(), 9).unwrap();
    fs_close(fd).unwrap();

    let buf = fs_read(&alpha_path).unwrap();
    assert_eq!(buf, b"abcdefghi");
}
fn main(){}
