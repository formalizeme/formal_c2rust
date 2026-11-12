use std::env;
use std::fs;
use std::path::{Path, PathBuf};

use VaultSync::vm::{add_changes, init_repo, make_commit, Author, Commit, Repository};

/// Create a temporary directory and set it as the current working directory.
/// Returns (original_cwd, temp_dir_path).
fn setup_temp_repo(label: &str) -> (PathBuf, PathBuf) {
    let original_cwd = env::current_dir().expect("failed to get cwd");
    let temp_dir = env::temp_dir().join(format!(
        "vaultsync_test_{}_{}",
        label,
        std::process::id()
    ));
    let _ = fs::remove_dir_all(&temp_dir);
    fs::create_dir_all(&temp_dir).expect("failed to create temp dir");
    env::set_current_dir(&temp_dir).expect("failed to chdir to temp dir");
    (original_cwd, temp_dir)
}

fn teardown_temp_repo(original_cwd: PathBuf, temp_dir: PathBuf) {
    let _ = env::set_current_dir(&original_cwd);
    let _ = fs::remove_dir_all(&temp_dir);
}

fn init_repository() {
    let author = Box::new(Author {
        mail: "john@example.com".to_string(),
        username: "john".to_string(),
    });

    let repo = init_repo(&author);
    if repo.is_ok() {
        println!("Init done");
    }
    assert!(repo.is_ok());
}

fn adding_changes(repo_dir: &str) {
    let author = Author {
        mail: "john@example.com".to_string(),
        username: "john".to_string(),
    };

    let repo = Repository {
        name: "foo".to_string(),
        author: author,
        last_commit: None,
        dir: repo_dir.to_string(),
    };

    let hello_path_buf = Path::new(repo_dir).join("hello.txt");
    let res = add_changes(
        &repo,
        &vec![hello_path_buf.as_path()],
    );
    if res.is_ok() {
        println!("Changes added");
    }
    assert!(res.is_ok());
}

fn made_commit(repo_dir: &str) {
    let author = Author {
        mail: "john@example.com".to_string(),
        username: "john".to_string(),
    };

    let mut repo = Repository {
        author: author.clone(),
        dir: repo_dir.to_string(),
        name: "foo".to_string(),
        last_commit: Some(Commit {
            author: author.clone(),
            hash: "0".to_string(),
            parent_hash: "-".to_string(),
        }),
    };

    let mut commit = Commit {
        hash: "".to_string(),
        author: author.clone(),
        parent_hash: "".to_string(),
    };
    let res = make_commit(&repo, &author, &commit);
    if res.is_ok() {
        println!("Commit done");
    }
    assert!(res.is_ok());
}

#[test]
pub fn test() {
    let (original_cwd, temp_dir) = setup_temp_repo("main");

    // Create a test file so init_repo has something to track
    // (mirrors the C test's assumption that files exist at the repo path)
    fs::write(temp_dir.join("hello.txt"), "hello").expect("failed to create test file");

    let repo_dir = temp_dir.to_string_lossy().to_string();

    init_repository();
    adding_changes(&repo_dir);
    made_commit(&repo_dir);

    teardown_temp_repo(original_cwd, temp_dir);
}
fn main(){}
