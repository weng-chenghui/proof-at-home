use assert_cmd::Command;
use predicates::prelude::*;

#[test]
fn test_lesson_notes_list_help() {
    Command::cargo_bin("pah")
        .unwrap()
        .args(["lesson", "notes", "list", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("Lesson ID"));
}

#[test]
fn test_lesson_notes_list_missing_id() {
    Command::cargo_bin("pah")
        .unwrap()
        .args(["lesson", "notes", "list"])
        .assert()
        .failure()
        .stderr(predicate::str::contains("required"));
}

#[test]
fn test_lesson_notes_revise_help() {
    Command::cargo_bin("pah")
        .unwrap()
        .args(["lesson", "notes", "revise", "--help"])
        .assert()
        .success();
}

#[test]
fn test_lesson_notes_revise_missing_id() {
    Command::cargo_bin("pah")
        .unwrap()
        .args(["lesson", "notes", "revise"])
        .assert()
        .failure()
        .stderr(predicate::str::contains("required"));
}

#[test]
fn test_lesson_notes_merge_help() {
    Command::cargo_bin("pah")
        .unwrap()
        .args(["lesson", "notes", "merge", "--help"])
        .assert()
        .success();
}

#[test]
fn test_lesson_notes_merge_missing_id() {
    Command::cargo_bin("pah")
        .unwrap()
        .args(["lesson", "notes", "merge"])
        .assert()
        .failure()
        .stderr(predicate::str::contains("required"));
}

#[test]
fn test_lesson_notes_list_no_auth() {
    Command::cargo_bin("pah")
        .unwrap()
        .env("HOME", "/tmp/pah-test-nonexistent-home")
        .args(["lesson", "notes", "list", "some-lesson-id"])
        .assert()
        .stderr(predicate::str::contains("required").not());
}
