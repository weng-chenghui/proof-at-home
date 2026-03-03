use assert_cmd::Command;
use predicates::prelude::*;

#[test]
fn test_pool_help() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["pool", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("clone"))
        .stdout(predicate::str::contains("pull"))
        .stdout(predicate::str::contains("push"))
        .stdout(predicate::str::contains("status"));
}

#[test]
fn test_pool_clone_help() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["pool", "clone", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("--dir"));
}

#[test]
fn test_pool_status_no_pool() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    // Point to a non-existent pool dir via a config that won't exist
    cmd.env("HOME", "/tmp/pah-test-nonexistent-home")
        .args(["pool", "status"])
        .assert()
        .failure()
        .stderr(predicate::str::contains("Pool not found"));
}

#[test]
fn test_pool_pull_no_pool() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.env("HOME", "/tmp/pah-test-nonexistent-home")
        .args(["pool", "pull"])
        .assert()
        .failure()
        .stderr(predicate::str::contains("Pool not found"));
}

#[test]
fn test_pool_push_no_pool() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.env("HOME", "/tmp/pah-test-nonexistent-home")
        .args(["pool", "push"])
        .assert()
        .failure()
        .stderr(predicate::str::contains("Pool not found"));
}
