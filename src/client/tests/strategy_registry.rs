use assert_cmd::Command;
use predicates::prelude::*;

// ── Strategy Search ──

#[test]
fn test_strategy_search_help() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["strategy", "search", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("--kind"))
        .stdout(predicate::str::contains("--prover"));
}

#[test]
fn test_strategy_search_missing_query() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["strategy", "search"])
        .assert()
        .failure()
        .stderr(predicate::str::contains("required"));
}

// ── Strategy Publish ──

#[test]
fn test_strategy_publish_help() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["strategy", "publish", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("--registry"));
}

#[test]
fn test_strategy_publish_missing_name() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["strategy", "publish"])
        .assert()
        .failure()
        .stderr(predicate::str::contains("required"));
}

// ── Strategy Registry ──

#[test]
fn test_strategy_registry_help() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["strategy", "registry", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("list"))
        .stdout(predicate::str::contains("add"))
        .stdout(predicate::str::contains("remove"));
}

#[test]
fn test_strategy_registry_list() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    let assert = cmd
        .env("HOME", "/tmp/pah-test-nonexistent-home")
        .args(["strategy", "registry", "list"])
        .assert();
    // Passes clap parsing
    assert.stderr(predicate::str::contains("required").not());
}

#[test]
fn test_strategy_registry_add_help() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["strategy", "registry", "add", "--help"])
        .assert()
        .success();
}

#[test]
fn test_strategy_registry_add_missing_args() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["strategy", "registry", "add"])
        .assert()
        .failure()
        .stderr(predicate::str::contains("required"));
}

#[test]
fn test_strategy_registry_remove_missing_name() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["strategy", "registry", "remove"])
        .assert()
        .failure()
        .stderr(predicate::str::contains("required"));
}

// ── Strategy help shows new commands ──

#[test]
fn test_strategy_help_shows_new_commands() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["strategy", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("search"))
        .stdout(predicate::str::contains("publish"))
        .stdout(predicate::str::contains("registry"))
        .stdout(predicate::str::contains("list"))
        .stdout(predicate::str::contains("get"))
        .stdout(predicate::str::contains("import"))
        .stdout(predicate::str::contains("memory"));
}
