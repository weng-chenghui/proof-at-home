use assert_cmd::Command;
use predicates::prelude::*;

// ── Lesson edition bump ──

#[test]
fn test_lesson_edition_bump_help() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["lesson", "edition", "bump", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("Lesson ID"))
        .stdout(predicate::str::contains("--summary"));
}

#[test]
fn test_lesson_edition_bump_missing_id() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["lesson", "edition", "bump"])
        .assert()
        .failure()
        .stderr(predicate::str::contains("required"));
}

#[test]
fn test_lesson_edition_bump_missing_summary() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["lesson", "edition", "bump", "some-lesson-id"])
        .assert()
        .failure()
        .stderr(predicate::str::contains("required"));
}

#[test]
fn test_lesson_edition_bump_no_auth() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    let assert = cmd
        .env("HOME", "/tmp/pah-test-nonexistent-home")
        .args([
            "lesson",
            "edition",
            "bump",
            "some-lesson-id",
            "--summary",
            "Added exercises",
        ])
        .assert();
    // Gets past clap argument parsing, fails at auth
    assert.stderr(predicate::str::contains("required").not());
}

// ── Series edition bump ──

#[test]
fn test_series_edition_bump_help() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["series", "edition", "bump", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("Series ID"))
        .stdout(predicate::str::contains("--summary"));
}

#[test]
fn test_series_edition_bump_missing_id() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["series", "edition", "bump"])
        .assert()
        .failure()
        .stderr(predicate::str::contains("required"));
}

#[test]
fn test_series_edition_bump_missing_summary() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["series", "edition", "bump", "some-series-id"])
        .assert()
        .failure()
        .stderr(predicate::str::contains("required"));
}

#[test]
fn test_series_edition_bump_no_auth() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    let assert = cmd
        .env("HOME", "/tmp/pah-test-nonexistent-home")
        .args([
            "series",
            "edition",
            "bump",
            "some-series-id",
            "--summary",
            "Added module 5",
        ])
        .assert();
    assert.stderr(predicate::str::contains("required").not());
}

// ── Lesson edition subcommand hierarchy ──

#[test]
fn test_lesson_edition_help() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["lesson", "edition", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("bump"));
}

#[test]
fn test_series_edition_help() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["series", "edition", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("bump"));
}

// ── Lesson help shows edition subcommand ──

#[test]
fn test_lesson_help_shows_edition() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["lesson", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("edition"));
}

#[test]
fn test_series_help_shows_edition() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["series", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("edition"));
}
