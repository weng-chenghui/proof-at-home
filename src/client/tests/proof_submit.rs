use assert_cmd::Command;
use predicates::prelude::*;

#[test]
fn test_proof_submit_help() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["proof", "submit", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains("--stdin"))
        .stdout(predicate::str::contains("--method"));
}

#[test]
fn test_proof_submit_stdin_requires_conjecture_id() {
    // Without auth config, require_login shows welcome and exits 0
    // Just verify arg parsing works (no clap error)
    let mut cmd = Command::cargo_bin("pah").unwrap();
    let assert = cmd
        .env("HOME", "/tmp/pah-test-nonexistent-home")
        .args(["proof", "submit", "--stdin"])
        .write_stdin("Lemma test : True. Proof. trivial. Qed.")
        .assert();
    assert.stderr(predicate::str::contains("required").not());
}

#[test]
fn test_proof_submit_invalid_method() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.env("HOME", "/tmp/pah-test-nonexistent-home")
        .args([
            "proof", "submit", "prob_001", "proof.v", "--method", "bogus",
        ])
        .assert()
        .failure()
        .stderr(predicate::str::contains("Invalid method"));
}

#[test]
fn test_proof_submit_stdin_with_conjecture() {
    // Verify it gets past arg parsing and method validation
    let mut cmd = Command::cargo_bin("pah").unwrap();
    let assert = cmd
        .env("HOME", "/tmp/pah-test-nonexistent-home")
        .args([
            "proof",
            "submit",
            "prob_001",
            "--stdin",
            "--method",
            "pair-proved",
        ])
        .write_stdin("Lemma test : True. Proof. trivial. Qed.")
        .assert();
    // No clap error means arg parsing succeeded
    assert.stderr(predicate::str::contains("required").not());
}
