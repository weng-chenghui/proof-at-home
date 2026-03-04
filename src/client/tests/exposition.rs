use assert_cmd::Command;
use predicates::prelude::*;

#[test]
fn test_exposition_create_help() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["exposition", "create", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("--for"))
        .stdout(predicate::str::contains("--domain"))
        .stdout(predicate::str::contains("--by"));
}

#[test]
fn test_exposition_create_missing_for() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["exposition", "create"])
        .assert()
        .failure()
        .stderr(predicate::str::contains("required"));
}

#[test]
fn test_exposition_list_help() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["exposition", "list", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("List"));
}

#[test]
fn test_exposition_get_help() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["exposition", "get", "--help"]).assert().success();
}

#[test]
fn test_exposition_get_missing_id() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["exposition", "get"])
        .assert()
        .failure()
        .stderr(predicate::str::contains("required"));
}

#[test]
fn test_exposition_create_with_conjecture_id() {
    // Verify arg parsing works — gets past clap to runtime (welcome/auth)
    let mut cmd = Command::cargo_bin("pah").unwrap();
    let assert = cmd
        .env("HOME", "/tmp/pah-test-nonexistent-home")
        .args(["exposition", "create", "--for", "prob_001"])
        .assert();
    assert.stderr(predicate::str::contains("required").not());
}

#[test]
fn test_exposition_create_with_contribution_id() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    let assert = cmd
        .env("HOME", "/tmp/pah-test-nonexistent-home")
        .args([
            "exposition",
            "create",
            "--for",
            "contrib_001",
            "--domain",
            "algebra",
        ])
        .assert();
    assert.stderr(predicate::str::contains("required").not());
}

#[test]
fn test_exposition_export_help() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["exposition", "export", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("--for"));
}

#[test]
fn test_exposition_export_missing_for() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["exposition", "export"])
        .assert()
        .failure()
        .stderr(predicate::str::contains("required"));
}

#[test]
fn test_exposition_export_with_id() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    let assert = cmd
        .env("HOME", "/tmp/pah-test-nonexistent-home")
        .args(["exposition", "export", "--for", "prob_001"])
        .assert();
    assert.stderr(predicate::str::contains("required").not());
}

#[test]
fn test_exposition_create_stdin_pair_proved() {
    // Pair prover mode: read JSON from stdin
    let mut cmd = Command::cargo_bin("pah").unwrap();
    let assert = cmd
        .env("HOME", "/tmp/pah-test-nonexistent-home")
        .args([
            "exposition",
            "create",
            "--for",
            "prob_001",
            "--stdin",
            "--method",
            "pair-proved",
        ])
        .write_stdin(r#"{"title":"Test","visualizations":[]}"#)
        .assert();
    assert.stderr(predicate::str::contains("required").not());
}

#[test]
fn test_exposition_create_invalid_method() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.env("HOME", "/tmp/pah-test-nonexistent-home")
        .args([
            "exposition",
            "create",
            "--for",
            "prob_001",
            "--method",
            "bogus",
        ])
        .assert()
        .failure()
        .stderr(predicate::str::contains("Invalid method"));
}

#[test]
fn test_exposition_list_no_auth() {
    // Without auth, shows welcome and exits 0
    let mut cmd = Command::cargo_bin("pah").unwrap();
    let assert = cmd
        .env("HOME", "/tmp/pah-test-nonexistent-home")
        .args(["exposition", "list"])
        .assert();
    assert.stderr(predicate::str::contains("required").not());
}
