use assert_cmd::Command;
use predicates::prelude::*;

// ── Series list ──

#[test]
fn test_series_list_help() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["series", "list", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("List all series"));
}

#[test]
fn test_series_list_no_auth() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    let assert = cmd
        .env("HOME", "/tmp/pah-test-nonexistent-home")
        .args(["series", "list"])
        .assert();
    assert.stderr(predicate::str::contains("required").not());
}

// ── Series get ──

#[test]
fn test_series_get_help() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["series", "get", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("Series ID"));
}

#[test]
fn test_series_get_missing_id() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["series", "get"])
        .assert()
        .failure()
        .stderr(predicate::str::contains("required"));
}

// ── Series create ──

#[test]
fn test_series_create_help() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["series", "create", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("--lessons"))
        .stdout(predicate::str::contains("--method"))
        .stdout(predicate::str::contains("--stdin"));
}

#[test]
fn test_series_create_invalid_method() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.env("HOME", "/tmp/pah-test-nonexistent-home")
        .args(["series", "create", "--method", "bogus"])
        .assert()
        .failure()
        .stderr(predicate::str::contains("Invalid method"));
}

// ── Series export ──

#[test]
fn test_series_export_help() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["series", "export", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("--lessons"));
}

// ── Series plan (new) ──

#[test]
fn test_series_plan_help() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["series", "plan", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("--topic"))
        .stdout(predicate::str::contains("--depth"))
        .stdout(predicate::str::contains("--difficulty"))
        .stdout(predicate::str::contains("--budget"));
}

#[test]
fn test_series_plan_missing_topic() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["series", "plan"])
        .assert()
        .failure()
        .stderr(predicate::str::contains("required"));
}

#[test]
fn test_series_plan_with_topic() {
    // Should get past clap argument parsing
    let mut cmd = Command::cargo_bin("pah").unwrap();
    let assert = cmd
        .env("HOME", "/tmp/pah-test-nonexistent-home")
        .args(["series", "plan", "--topic", "group theory"])
        .assert();
    assert.stderr(predicate::str::contains("required").not());
}

#[test]
fn test_series_plan_with_all_args() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    let assert = cmd
        .env("HOME", "/tmp/pah-test-nonexistent-home")
        .args([
            "series",
            "plan",
            "--topic",
            "sorting algorithms",
            "--depth",
            "5",
            "--difficulty",
            "medium-hard",
            "--budget",
            "1.50",
            "-o",
            "/tmp/pah-test-plan.json",
        ])
        .assert();
    // Should get past clap to runtime
    assert.stderr(predicate::str::contains("required").not());
}

// ── Series generate (new) ──

#[test]
fn test_series_generate_help() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["series", "generate", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("--from"))
        .stdout(predicate::str::contains("--budget"));
}

#[test]
fn test_series_generate_missing_from() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["series", "generate"])
        .assert()
        .failure()
        .stderr(predicate::str::contains("required"));
}

#[test]
fn test_series_generate_with_from() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    let assert = cmd
        .env("HOME", "/tmp/pah-test-nonexistent-home")
        .args(["series", "generate", "--from", "plan.json"])
        .assert();
    // Should get past clap — fails at runtime (file not found or auth)
    assert.stderr(predicate::str::contains("required").not());
}

#[test]
fn test_series_generate_stdin() {
    // Verify --from - (stdin) is accepted by clap
    let mut cmd = Command::cargo_bin("pah").unwrap();
    let assert = cmd
        .env("HOME", "/tmp/pah-test-nonexistent-home")
        .args(["series", "generate", "--from", "-"])
        .write_stdin(r#"{"topic":"test","plan":{}}"#)
        .assert();
    assert.stderr(predicate::str::contains("required").not());
}

// ── Series audit (new) ──

#[test]
fn test_series_audit_help() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["series", "audit", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("Series ID"))
        .stdout(predicate::str::contains("--output"));
}

#[test]
fn test_series_audit_missing_id() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["series", "audit"])
        .assert()
        .failure()
        .stderr(predicate::str::contains("required"));
}

#[test]
fn test_series_audit_with_id() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    let assert = cmd
        .env("HOME", "/tmp/pah-test-nonexistent-home")
        .args(["series", "audit", "series-test-001"])
        .assert();
    assert.stderr(predicate::str::contains("required").not());
}

#[test]
fn test_series_audit_with_output() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    let assert = cmd
        .env("HOME", "/tmp/pah-test-nonexistent-home")
        .args([
            "series",
            "audit",
            "series-test-001",
            "-o",
            "/tmp/pah-test-audit.json",
        ])
        .assert();
    assert.stderr(predicate::str::contains("required").not());
}

// ── Series subcommand hierarchy ──

#[test]
fn test_series_help() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["series", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("list"))
        .stdout(predicate::str::contains("get"))
        .stdout(predicate::str::contains("create"))
        .stdout(predicate::str::contains("export"))
        .stdout(predicate::str::contains("plan"))
        .stdout(predicate::str::contains("generate"))
        .stdout(predicate::str::contains("audit"));
}

#[test]
fn test_series_no_subcommand() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["series"])
        .assert()
        .failure()
        .stderr(predicate::str::contains("Usage"));
}
