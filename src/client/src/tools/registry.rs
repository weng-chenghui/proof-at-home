use anyhow::{bail, Context, Result};
use colored::Colorize;
use std::io::IsTerminal;
use std::path::PathBuf;
use std::process::Command;

use super::cache;

/// Static specification for a tool that pah depends on.
pub struct ToolSpec {
    pub name: &'static str,
    pub binary_name: &'static str,
    pub version_command: &'static [&'static str],
    pub install_hint: &'static str,
    pub install_command: Option<&'static str>,
    pub required_by: &'static str,
}

/// Information about a detected tool.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct ToolInfo {
    pub name: String,
    pub path: PathBuf,
    pub version: String,
    pub detected_at: String,
}

/// Result of checking for a tool.
pub enum ToolStatus {
    Found(ToolInfo),
    NotFound {
        name: String,
        install_hint: String,
        required_by: String,
    },
}

/// All known tools.
pub static TOOL_REGISTRY: &[ToolSpec] = &[
    ToolSpec {
        name: "opam",
        binary_name: "opam",
        version_command: &["opam", "--version"],
        install_hint: "Install opam: https://opam.ocaml.org/doc/Install.html",
        install_command: None,
        required_by: "contribution run (Rocq)",
    },
    ToolSpec {
        name: "dune",
        binary_name: "dune",
        version_command: &["dune", "--version"],
        install_hint: "Install via opam: opam install dune",
        install_command: None,
        required_by: "contribution run (Rocq)",
    },
    ToolSpec {
        name: "elan",
        binary_name: "elan",
        version_command: &["elan", "--version"],
        install_hint: "Install elan: curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y",
        install_command: Some("curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y"),
        required_by: "contribution run (Lean)",
    },
    ToolSpec {
        name: "lean",
        binary_name: "lean",
        version_command: &["lean", "--version"],
        install_hint: "Install via elan: curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y",
        install_command: None,
        required_by: "contribution run (Lean)",
    },
    ToolSpec {
        name: "lake",
        binary_name: "lake",
        version_command: &["lake", "--version"],
        install_hint: "lake is installed with elan. Install elan first.",
        install_command: None,
        required_by: "contribution run (Lean)",
    },
    ToolSpec {
        name: "claude",
        binary_name: "claude",
        version_command: &["claude", "--version"],
        install_hint: "Install: npm install -g @anthropic-ai/claude-code",
        install_command: Some("npm install -g @anthropic-ai/claude-code"),
        required_by: "contribution run (optional, API fallback available)",
    },
    ToolSpec {
        name: "lean_conjecturer",
        binary_name: "lean_conjecturer",
        version_command: &["lean_conjecturer", "--version"],
        install_hint: "Install from https://github.com/auto-res/LeanConjecturer",
        install_command: None,
        required_by: "conjecture generate",
    },
];

/// Look up a tool spec by name.
pub fn get_spec(name: &str) -> Option<&'static ToolSpec> {
    TOOL_REGISTRY.iter().find(|s| s.name == name)
}

/// Detect whether a tool is available, returning its info if found.
pub fn detect_tool(spec: &ToolSpec) -> Option<ToolInfo> {
    // Check for PAH_TOOL_<NAME> env var override
    let env_key = format!("PAH_TOOL_{}", spec.name.to_uppercase());
    if let Ok(override_path) = std::env::var(&env_key) {
        let path = PathBuf::from(&override_path);
        if path.exists() {
            return Some(ToolInfo {
                name: spec.name.to_string(),
                path,
                version: "custom".to_string(),
                detected_at: chrono::Utc::now().to_rfc3339(),
            });
        }
    }

    // Run version command
    let cmd = spec.version_command;
    if cmd.is_empty() {
        return None;
    }

    let output = Command::new(cmd[0]).args(&cmd[1..]).output().ok()?;

    if !output.status.success() {
        return None;
    }

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let combined = format!("{}{}", stdout, stderr);
    let version = extract_version(&combined);

    // Resolve path via `which`
    let path = resolve_path(spec.binary_name);

    Some(ToolInfo {
        name: spec.name.to_string(),
        path,
        version,
        detected_at: chrono::Utc::now().to_rfc3339(),
    })
}

/// Main entry point: require a tool, using cache, detection, and interactive prompts.
pub fn require_tool(name: &str) -> Result<ToolInfo> {
    let spec = get_spec(name).with_context(|| format!("Unknown tool: {}", name))?;

    // Check PAH_TOOL_<NAME> env var override
    let env_key = format!("PAH_TOOL_{}", spec.name.to_uppercase());
    if let Ok(override_path) = std::env::var(&env_key) {
        let path = PathBuf::from(&override_path);
        if path.exists() {
            return Ok(ToolInfo {
                name: spec.name.to_string(),
                path,
                version: "custom".to_string(),
                detected_at: chrono::Utc::now().to_rfc3339(),
            });
        }
    }

    // Check cache (unless PAH_NO_TOOL_CACHE is set)
    let skip_cache = std::env::var("PAH_NO_TOOL_CACHE").is_ok();
    if !skip_cache {
        if let Some(cached) = cache::load_cached_tool(name) {
            // Verify cached path still exists
            if cached.path.exists() {
                return Ok(cached);
            }
            // Cached path gone — evict
            let _ = cache::remove_cached_tool(name);
        }
    }

    // Fresh detection
    if let Some(info) = detect_tool(spec) {
        if !skip_cache {
            let _ = cache::save_cached_tool(&info);
        }
        return Ok(info);
    }

    // Tool not found — interactive prompt if TTY
    if std::io::stdin().is_terminal() && std::io::stderr().is_terminal() {
        eprintln!(
            "\n{} Required tool '{}' not found.",
            "Missing:".yellow().bold(),
            spec.name
        );
        eprintln!("  Needed for: {}", spec.required_by);
        eprintln!("  {}", spec.install_hint);

        if let Some(install_cmd) = spec.install_command {
            let confirm = dialoguer::Confirm::new()
                .with_prompt(format!("Install {} now?", spec.name))
                .default(true)
                .interact()
                .unwrap_or(false);

            if confirm {
                eprintln!("  Installing {}...", spec.name);
                let status = Command::new("sh")
                    .args(["-c", install_cmd])
                    .status()
                    .context("Failed to run install command")?;

                if status.success() {
                    // Re-detect after install
                    if let Some(info) = detect_tool(spec) {
                        if !skip_cache {
                            let _ = cache::save_cached_tool(&info);
                        }
                        eprintln!("  {} {} installed successfully", "✓".green(), spec.name);
                        return Ok(info);
                    }
                }
                eprintln!(
                    "  {} Installation may have failed. Check your PATH.",
                    "✗".red()
                );
            }
        }
    }

    bail!(
        "Required tool '{}' is not installed.\n  Needed for: {}\n  {}",
        spec.name,
        spec.required_by,
        spec.install_hint
    )
}

/// Check all tools and return their status.
pub fn check_all_tools() -> Vec<ToolStatus> {
    TOOL_REGISTRY
        .iter()
        .map(|spec| match detect_tool(spec) {
            Some(info) => ToolStatus::Found(info),
            None => ToolStatus::NotFound {
                name: spec.name.to_string(),
                install_hint: spec.install_hint.to_string(),
                required_by: spec.required_by.to_string(),
            },
        })
        .collect()
}

/// Extract a version string (X.Y.Z pattern) from output text.
fn extract_version(text: &str) -> String {
    let mut start = None;
    let chars: Vec<char> = text.chars().collect();

    for i in 0..chars.len() {
        if chars[i].is_ascii_digit() {
            if start.is_none() {
                start = Some(i);
            }
        } else if chars[i] == '.' {
            // Allow dots within version
        } else if start.is_some() {
            let candidate: String = chars[start.unwrap()..i].iter().collect();
            if candidate.contains('.') {
                return candidate.trim_end_matches('.').to_string();
            }
            start = None;
        }
    }

    // Check tail
    if let Some(s) = start {
        let candidate: String = chars[s..].iter().collect();
        if candidate.contains('.') {
            return candidate.trim_end_matches('.').to_string();
        }
    }

    text.lines().next().unwrap_or("").trim().to_string()
}

/// Resolve the full path of a binary.
fn resolve_path(binary: &str) -> PathBuf {
    Command::new("which")
        .arg(binary)
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| PathBuf::from(String::from_utf8_lossy(&o.stdout).trim()))
        .unwrap_or_else(|| PathBuf::from(binary))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_extract_version() {
        assert_eq!(extract_version("opam 2.1.5"), "2.1.5");
        assert_eq!(extract_version("elan 3.1.1"), "3.1.1");
        assert_eq!(extract_version("Lean (version 4.16.0, ...)"), "4.16.0");
        assert_eq!(extract_version("dune 3.16.0"), "3.16.0");
    }

    #[test]
    fn test_get_spec() {
        assert!(get_spec("opam").is_some());
        assert!(get_spec("lake").is_some());
        assert!(get_spec("nonexistent").is_none());
    }

    #[test]
    fn test_registry_completeness() {
        let names = [
            "opam",
            "dune",
            "elan",
            "lean",
            "lake",
            "claude",
            "lean_conjecturer",
        ];
        for name in &names {
            assert!(get_spec(name).is_some(), "Missing spec for {}", name);
        }
    }
}
