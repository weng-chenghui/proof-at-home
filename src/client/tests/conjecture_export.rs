use assert_cmd::Command;
use predicates::prelude::*;

#[test]
fn test_conjecture_export_help() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["conjecture", "export", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("Export a conjecture"));
}

#[test]
fn test_conjecture_export_no_args() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["conjecture", "export"])
        .assert()
        .failure()
        .stderr(predicate::str::contains("required"));
}

#[test]
fn test_conjecture_export_invalid_format() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.env("HOME", "/tmp/pah-test-nonexistent-home")
        .args(["conjecture", "export", "prob_001", "--format", "invalid"])
        .assert()
        .failure()
        .stderr(predicate::str::contains("Invalid format"));
}

#[test]
fn test_conjecture_export_prompt_format() {
    // Verify it gets past arg parsing — may succeed (welcome message) or fail (server)
    let mut cmd = Command::cargo_bin("pah").unwrap();
    let assert = cmd
        .env("HOME", "/tmp/pah-test-nonexistent-home")
        .args(["conjecture", "export", "prob_001"])
        .assert();
    // No clap error means arg parsing succeeded
    assert.stderr(predicate::str::contains("required").not());
}
