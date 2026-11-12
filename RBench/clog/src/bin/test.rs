use clog::clog;
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Write};
use std::time::{SystemTime, UNIX_EPOCH};
use std::fmt;
use std::path::{Path, PathBuf};
use std::env;

const THIS_FILE: &str = "clog_test_c.c";
const LOG_FMT: &str = "%f: %l: %m\n";
const LINE: i32 = 0;

fn error(args: std::fmt::Arguments) {
    eprintln!("{}", fmt::format(args));
}

/// Delete a test output file, matching C's unlink(TEST_FILE) before each sub-test.
fn cleanup_file(path: &Path) {
    let _ = fs::remove_file(path);
}

/// Reset all logger slots, matching C's _clog_loggers[j] = NULL (line 378-379).
fn reset_loggers() {
    for j in 0..clog::CLOG_MAX_LOGGERS {
        clog::clog_free(j);
    }
}

/// Create a writable temp file suitable for fd-based logger init.
/// Uses truncate (not append) so the file starts empty each time.
fn open_writable_file(path: &Path) -> File {
    OpenOptions::new()
        .create(true)
        .truncate(true)
        .write(true)
        .open(path)
        .expect("failed to create temp log file")
}

fn read_file(path: &Path) -> String {
    fs::read_to_string(path).expect("failed to read log file")
}

fn temp_path(stem: &str) -> PathBuf {
    env::temp_dir().join(format!("clog_test_{}_{}.out", stem, std::process::id()))
}

fn test_double_init() -> Result<(), &'static str> {
    let path = temp_path("double_init");
    let path_str = path.to_string_lossy().to_string();
    if clog::clog_init_path(0, &path_str).is_err() {
        return Err("First init failed");
    }
    if clog::clog_init_path(0, &path_str).is_ok() {
        return Err("Logger initialized twice");
    }
    clog::clog_free(0);
    cleanup_file(&path);
    Ok(())
}

fn test_file_write() -> Result<(), &'static str> {
    let path = temp_path("file_write");
    cleanup_file(&path);
    let path_str = path.to_string_lossy().to_string();

    clog::clog_init_path(0, &path_str);
    clog::clog_set_fmt(0, LOG_FMT);
    clog::clog_debug(THIS_FILE, LINE, 0, format_args!("Hello, {}!", "world"));
    clog::clog_free(0);

    let contents = read_file(&path);
    assert_eq!(contents, format!("{}: DEBUG: Hello, world!\n", THIS_FILE));
    cleanup_file(&path);
    Ok(())
}

fn test_file_write_nonexistent() -> Result<(), &'static str> {
    if clog::clog_init_path(0, "path-doesnt-exist/log.out").is_ok() {
        return Err("Logger initialized with nonexistent path");
    }
    Ok(())
}

fn test_fd_write() -> Result<(), &'static str> {
    let path = temp_path("fd_write");
    cleanup_file(&path);
    let file = open_writable_file(&path);

    clog::clog_init_fd(0, file);
    clog::clog_set_fmt(0, LOG_FMT);
    clog::clog_debug(THIS_FILE, LINE, 0, format_args!("Hello, {}!", "world"));
    clog::clog_free(0);

    let contents = read_file(&path);
    assert_eq!(contents, format!("{}: DEBUG: Hello, world!\n", THIS_FILE));
    cleanup_file(&path);
    Ok(())
}

fn test_all_levels() -> Result<(), &'static str> {
    let path = temp_path("all_levels");
    cleanup_file(&path);
    let file = open_writable_file(&path);

    clog::clog_init_fd(0, file);
    clog::clog_set_fmt(0, LOG_FMT);
    clog::clog_debug(THIS_FILE, LINE, 0, format_args!("Hello, {}!", "world"));
    clog::clog_info(THIS_FILE, LINE, 0, format_args!("Hello, {}!", "world"));
    clog::clog_warn(THIS_FILE, LINE, 0, format_args!("Hello, {}!", "world"));
    clog::clog_error(THIS_FILE, LINE, 0, format_args!("Hello, {}!", "world"));
    clog::clog_free(0);

    let contents = read_file(&path);
    assert_eq!(contents, format!(
    "{0}: DEBUG: Hello, world!\n\
    {0}: INFO: Hello, world!\n\
    {0}: WARN: Hello, world!\n\
    {0}: ERROR: Hello, world!\n",
    THIS_FILE
    ));
    cleanup_file(&path);
    Ok(())
}

fn test_level_filtering() -> Result<(), &'static str> {
    let path = temp_path("level_filtering");
    cleanup_file(&path);
    let file = open_writable_file(&path);

    clog::clog_init_fd(0, file);
    clog::clog_set_fmt(0, LOG_FMT);
    clog::clog_set_level(0, clog::ClogLevel::Warn);
    clog::clog_debug(THIS_FILE, LINE, 0, format_args!("Hello, {}!", "world"));
    clog::clog_info(THIS_FILE, LINE, 0, format_args!("Hello, {}!", "world"));
    clog::clog_warn(THIS_FILE, LINE, 0, format_args!("Hello, {}!", "world"));
    clog::clog_error(THIS_FILE, LINE, 0, format_args!("Hello, {}!", "world"));
    clog::clog_free(0);

    let contents = read_file(&path);
    assert_eq!(contents, format!(
    "{0}: WARN: Hello, world!\n\
    {0}: ERROR: Hello, world!\n",
    THIS_FILE
    ));
    cleanup_file(&path);
    Ok(())
}

fn test_multiple_loggers() -> Result<(), &'static str> {
    let mut paths = Vec::new();
    for id in 0..clog::CLOG_MAX_LOGGERS {
        let path = temp_path(&format!("multi_{}", id));
        cleanup_file(&path);
        let file = open_writable_file(&path);

        clog::clog_init_fd(id, file);
        clog::clog_set_fmt(id, LOG_FMT);
        clog::clog_debug(THIS_FILE, LINE, id, format_args!("Hello, {}!", id));
        paths.push(path);
    }
    for id in 0..clog::CLOG_MAX_LOGGERS {
        clog::clog_free(id);
    }
    for (id, path) in paths.iter().enumerate() {
        let contents = read_file(path);
        assert_eq!(contents, format!("{}: DEBUG: Hello, {}!\n", THIS_FILE, id));
        cleanup_file(path);
    }
    Ok(())
}

fn test_bad_format() -> Result<(), &'static str> {
    let too_long = "a".repeat(299);
    let path = temp_path("bad_format");
    cleanup_file(&path);
    let path_str = path.to_string_lossy().to_string();

    clog::clog_init_path(0, &path_str);
    if clog::clog_set_fmt(0, &too_long).is_ok() {
        return Err("Accepted too long format");
    }
    clog::clog_free(0);
    cleanup_file(&path);
    Ok(())
}

fn test_long_message() -> Result<(), &'static str> {
    let message = "b".repeat(49999);
    let path = temp_path("long_message");
    cleanup_file(&path);
    let path_str = path.to_string_lossy().to_string();

    clog::clog_init_path(0, &path_str);
    clog::clog_set_fmt(0, LOG_FMT);
    clog::clog_debug(THIS_FILE, LINE, 0, format_args!("{}", &message));
    clog::clog_free(0);

    let contents = read_file(&path);
    assert_eq!(contents, format!("{}: DEBUG: {}\n", THIS_FILE, message));
    cleanup_file(&path);
    Ok(())
}

fn test_performance() -> Result<(), &'static str> {
    const NUM_MESSAGES: usize = 200_000;
    let path = temp_path("performance");
    cleanup_file(&path);
    let path_str = path.to_string_lossy().to_string();

    clog::clog_init_path(0, &path_str);

    let start_time = SystemTime::now();
    for _ in 0..NUM_MESSAGES {
        clog::clog_debug(THIS_FILE, LINE, 0, format_args!("Hello, high-performing world!"));
    }
    let end_time = SystemTime::now();
    clog::clog_free(0);

    let duration = end_time.duration_since(start_time).unwrap();
    let run_time = duration.as_secs_f64();
    let messages_per_second = NUM_MESSAGES as f64 / run_time;
    error(format_args!("  Target 100000 msgs/sec, got {}.\n", messages_per_second));
    if messages_per_second < 100_000.0 {
        return Err("Performance below target");
    }
    cleanup_file(&path);
    Ok(())
}

fn test_reuse_logger_id() -> Result<(), &'static str> {
    for i in 0..2 {
        let path = temp_path(&format!("reuse_{}", i));
        cleanup_file(&path);
        let file = open_writable_file(&path);

        clog::clog_init_fd(0, file);
        clog::clog_set_fmt(0, LOG_FMT);
        clog::clog_debug(THIS_FILE, LINE, 0, format_args!("Hello, world!"));
        clog::clog_free(0);

        let contents = read_file(&path);
        assert_eq!(contents, format!("{}: DEBUG: Hello, world!\n", THIS_FILE));
        cleanup_file(&path);
    }
    Ok(())
}

#[test]
fn test_all() {
    let tests: Vec<(&str, fn() -> Result<(), &'static str>)> = vec![
    ("test_double_init", test_double_init),
    ("test_file_write", test_file_write),
    ("test_file_write_nonexistent", test_file_write_nonexistent),
    ("test_fd_write", test_fd_write),
    ("test_all_levels", test_all_levels),
    ("test_level_filtering", test_level_filtering),
    ("test_multiple_loggers", test_multiple_loggers),
    ("test_bad_format", test_bad_format),
    ("test_long_message", test_long_message),
    ("test_reuse_logger_id", test_reuse_logger_id),
    ("test_performance", test_performance),
    ];

    let mut pass = 0;
    let mut fail = 0;

    for (name, test) in tests {
    print!("{}: ", name);
    match test() {
    Ok(_) => {
    println!("OK");
    pass += 1;
    }
    Err(err) => {
    println!("FAIL ({})", err);
    fail += 1;
    }
    }

    // C test runner: _clog_loggers[j] = NULL for all j (lines 378-379)
    reset_loggers();
    }

    println!("\n{} successes, {} failures.", pass, fail);
    assert_eq!(fail, 0, "Some tests failed");
}
pub fn main(){}
