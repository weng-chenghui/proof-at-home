use anyhow::Result;
use std::path::Path;
use std::process::Command;
use std::time::Duration;

use crate::prover::env_manager::ResolvedEnv;

#[derive(Debug)]
pub struct VerifyResult {
    pub success: bool,
    pub output: String,
}

/// Verify a proof file using the resolved environment.
/// Copies the file into the project's theories dir and runs the build command.
pub fn verify_with_env(
    env: &ResolvedEnv,
    source_file: &Path,
    is_lean: bool,
) -> Result<VerifyResult> {
    // Copy the proof file into the project's theories directory
    let file_name = source_file
        .file_name()
        .unwrap_or_default()
        .to_string_lossy()
        .to_string();
    let dest = env.theories_dir.join(&file_name);
    std::fs::copy(source_file, &dest)?;

    // For Lean, we need to ensure the file is importable by adding it to the module
    // The file should already be a valid .lean file in PaH/

    // Run the build command
    let build_args = &env.build_cmd;
    if build_args.is_empty() {
        anyhow::bail!("Empty build command in ResolvedEnv");
    }

    let mut cmd = Command::new(&build_args[0]);
    for arg in &build_args[1..] {
        cmd.arg(arg);
    }
    cmd.current_dir(&env.project_dir);

    let output = run_with_timeout(cmd, Duration::from_secs(300))?;
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let combined = format!("{}{}", stdout, stderr);

    if is_lean {
        let has_errors = combined.contains("error:");
        Ok(VerifyResult {
            success: output.status.success() && !has_errors,
            output: combined,
        })
    } else {
        Ok(VerifyResult {
            success: output.status.success(),
            output: combined,
        })
    }
}

fn run_with_timeout(
    mut cmd: Command,
    timeout: Duration,
) -> Result<std::process::Output> {
    let child = cmd.stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()?;

    let start = std::time::Instant::now();
    let output = child.wait_with_output()?;

    if start.elapsed() > timeout {
        anyhow::bail!("Verification timed out after {:?}", timeout);
    }

    Ok(output)
}
