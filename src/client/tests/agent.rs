use assert_cmd::Command;
use predicates::prelude::*;

// ── Strategy top-level ──

#[test]
fn test_strategy_help() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["strategy", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("list"))
        .stdout(predicate::str::contains("get"))
        .stdout(predicate::str::contains("import"))
        .stdout(predicate::str::contains("memory"));
}

#[test]
fn test_strategy_list_help() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["strategy", "list", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("--kind"));
}

#[test]
fn test_strategy_list_with_kind() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    let assert = cmd
        .env("HOME", "/tmp/pah-test-nonexistent-home")
        .args(["strategy", "list", "--kind", "prove"])
        .assert();
    // Passes clap parsing (no "required" error); may fail at runtime due to no auth
    assert.stderr(predicate::str::contains("required").not());
}

// ── Strategy Memory (moved from agent) ──

#[test]
fn test_strategy_memory_list_help() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["strategy", "memory", "list", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("--kind"))
        .stdout(predicate::str::contains("--agent"));
}

#[test]
fn test_strategy_memory_list_no_args() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    let assert = cmd
        .env("HOME", "/tmp/pah-test-nonexistent-home")
        .args(["strategy", "memory", "list"])
        .assert();
    assert.stderr(predicate::str::contains("required").not());
}

#[test]
fn test_strategy_memory_get_help() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["strategy", "memory", "get", "--help"])
        .assert()
        .success();
}

#[test]
fn test_strategy_memory_get_missing_name() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["strategy", "memory", "get"])
        .assert()
        .failure()
        .stderr(predicate::str::contains("required"));
}

#[test]
fn test_strategy_memory_create_help() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["strategy", "memory", "create", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("--kind"))
        .stdout(predicate::str::contains("--body"))
        .stdout(predicate::str::contains("--tags"));
}

#[test]
fn test_strategy_memory_create_missing_kind() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["strategy", "memory", "create", "--body", "test"])
        .assert()
        .failure()
        .stderr(predicate::str::contains("required"));
}

#[test]
fn test_strategy_memory_create_missing_body() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["strategy", "memory", "create", "--kind", "memory-lesson"])
        .assert()
        .failure()
        .stderr(predicate::str::contains("required"));
}

#[test]
fn test_strategy_memory_forget_help() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["strategy", "memory", "forget", "--help"])
        .assert()
        .success();
}

#[test]
fn test_strategy_memory_forget_missing_name() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["strategy", "memory", "forget"])
        .assert()
        .failure()
        .stderr(predicate::str::contains("required"));
}

// ── Agent (slimmed) ──

#[test]
fn test_agent_help() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["agent", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("run"))
        .stdout(predicate::str::contains("status"))
        .stdout(predicate::str::contains("memory").not());
}

#[test]
fn test_agent_run_lesson_help() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["agent", "run", "lesson", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("--topic"))
        .stdout(predicate::str::contains("--conjectures"))
        .stdout(predicate::str::contains("--difficulty"))
        .stdout(predicate::str::contains("--output"));
}

#[test]
fn test_agent_run_lesson_no_args() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    let assert = cmd
        .env("HOME", "/tmp/pah-test-nonexistent-home")
        .args(["agent", "run", "lesson"])
        .assert();
    // All args optional — passes clap
    assert.stderr(predicate::str::contains("required").not());
}

#[test]
fn test_agent_run_lesson_with_args() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    let assert = cmd
        .env("HOME", "/tmp/pah-test-nonexistent-home")
        .args([
            "agent",
            "run",
            "lesson",
            "--topic",
            "algebra",
            "--conjectures",
            "a,b",
        ])
        .assert();
    assert.stderr(predicate::str::contains("required").not());
}

#[test]
fn test_agent_status_help() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["agent", "status", "--help"]).assert().success();
}

#[test]
fn test_agent_status_no_args() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    let assert = cmd
        .env("HOME", "/tmp/pah-test-nonexistent-home")
        .args(["agent", "status"])
        .assert();
    assert.stderr(predicate::str::contains("required").not());
}

// ── Agent Pipeline ──

#[test]
fn test_agent_run_pipeline_help() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["agent", "run", "pipeline", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("--pipeline"));
}

#[test]
fn test_agent_run_pipeline_missing_pipeline() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["agent", "run", "pipeline"])
        .assert()
        .failure()
        .stderr(predicate::str::contains("required"));
}

#[test]
fn test_agent_run_pipeline_with_args() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    let assert = cmd
        .env("HOME", "/tmp/pah-test-nonexistent-home")
        .args([
            "agent",
            "run",
            "pipeline",
            "--pipeline",
            "lesson-default",
            "--topic",
            "test",
        ])
        .assert();
    // Passes clap parsing (may fail at runtime without AI provider, but arg parsing succeeds)
    assert.stderr(predicate::str::contains("required").not());
}

#[test]
fn test_agent_help_shows_pipeline() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["agent", "run", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("pipeline"))
        .stdout(predicate::str::contains("lesson"));
}

// ── Verify old path removed ──

#[test]
fn test_agent_memory_removed() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["agent", "memory", "list"]).assert().failure();
}
