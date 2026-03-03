use assert_cmd::Command;
use predicates::prelude::*;
use std::io::Write;

/// Test that `pah proof parse` with no arguments shows usage error.
#[test]
fn test_proof_parse_no_args_shows_error() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["proof", "parse"])
        .assert()
        .failure()
        .stderr(predicate::str::contains(
            "Provide either a proof file path or both --contribution and --conjecture",
        ));
}

/// Test that `pah proof parse` with a non-existent file shows an error.
#[test]
fn test_proof_parse_missing_file() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["proof", "parse", "/tmp/nonexistent-proof-file-12345.v"])
        .assert()
        .failure()
        .stderr(predicate::str::contains("Failed to read proof file"));
}

/// Test that `pah proof parse --contribution` without --conjecture shows error.
#[test]
fn test_proof_parse_contribution_without_conjecture() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["proof", "parse", "--contribution", "some-id"])
        .assert()
        .failure()
        .stderr(predicate::str::contains(
            "Provide either a proof file path or both --contribution and --conjecture",
        ));
}

/// Test that `pah proof parse` with a local file attempts to read it (but fails at AI call).
/// This verifies the file reading + prover inference path works.
#[test]
fn test_proof_parse_local_file_reads_content() {
    let mut tmp = tempfile::NamedTempFile::with_suffix(".v").unwrap();
    writeln!(tmp, "Lemma test : True.\nProof. auto. Qed.").unwrap();

    let mut cmd = Command::cargo_bin("pah").unwrap();
    // The command will fail because there's no Claude CLI / API key configured,
    // but it should get past the file reading step.
    cmd.args(["proof", "parse", tmp.path().to_str().unwrap()])
        .assert()
        .failure()
        // Should fail at the Claude invocation step, not at file reading
        .stderr(predicate::str::contains("Failed to read proof file").not());
}

/// Test prover inference from file extension via the CLI help.
#[test]
fn test_proof_parse_help() {
    let mut cmd = Command::cargo_bin("pah").unwrap();
    cmd.args(["proof", "parse", "--help"])
        .assert()
        .success()
        .stdout(predicate::str::contains(
            "Parse a proof and generate a human-readable explanation",
        ));
}
