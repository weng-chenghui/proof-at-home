use anyhow::{Context, Result};
use colored::Colorize;
use std::path::Path;

use crate::strategy_store::frontmatter::parse_command_file;
use crate::strategy_store::loader::strategies_dir;

/// Import command files from various sources into ~/.proof-at-home/commands/.
pub fn import_commands(sources: &[String]) -> Result<()> {
    let dest_dir = strategies_dir()?;
    std::fs::create_dir_all(&dest_dir)?;

    for source in sources {
        if source.ends_with(".tar.gz") || source.ends_with(".tgz") {
            import_tar_gz(source, &dest_dir)?;
        } else if source.starts_with("https://github.com/") || source.starts_with("github:") {
            import_github(source, &dest_dir)?;
        } else {
            let path = Path::new(source);
            if path.is_dir() {
                import_directory(path, &dest_dir)?;
            } else if path.is_file() {
                import_file(path, &dest_dir)?;
            } else {
                eprintln!("{}: Source not found: {}", "Warning".yellow(), source);
            }
        }
    }

    Ok(())
}

/// Import a single .md file.
fn import_file(path: &Path, dest_dir: &Path) -> Result<()> {
    let content = std::fs::read_to_string(path)
        .with_context(|| format!("Failed to read {}", path.display()))?;

    // Validate frontmatter
    let (meta, _) = parse_command_file(&content)
        .with_context(|| format!("Invalid command file: {}", path.display()))?;

    let dest = dest_dir.join(format!("{}.md", meta.name));
    std::fs::write(&dest, &content)?;

    println!(
        "  {} Imported '{}' ({})",
        "✓".green(),
        meta.name,
        meta.description
    );
    Ok(())
}

/// Import all .md files from a directory.
fn import_directory(dir: &Path, dest_dir: &Path) -> Result<()> {
    let entries = std::fs::read_dir(dir)
        .with_context(|| format!("Failed to read directory {}", dir.display()))?;

    let mut count = 0;
    for entry in entries.flatten() {
        let path = entry.path();
        if path.extension().and_then(|e| e.to_str()) == Some("md") {
            match import_file(&path, dest_dir) {
                Ok(()) => count += 1,
                Err(e) => eprintln!(
                    "  {}: Skipping {}: {}",
                    "Warning".yellow(),
                    path.display(),
                    e
                ),
            }
        }
    }

    println!("  Imported {} command(s) from {}", count, dir.display());
    Ok(())
}

/// Import commands from a .tar.gz archive.
fn import_tar_gz(path: &str, dest_dir: &Path) -> Result<()> {
    let file = std::fs::File::open(path).with_context(|| format!("Failed to open {}", path))?;
    let decoder = flate2::read::GzDecoder::new(file);
    let mut archive = tar::Archive::new(decoder);

    let mut count = 0;
    for entry in archive.entries()? {
        let mut entry = entry?;
        let entry_path = entry.path()?.into_owned();

        if entry_path.extension().and_then(|e| e.to_str()) == Some("md") {
            let mut content = String::new();
            std::io::Read::read_to_string(&mut entry, &mut content)?;

            match parse_command_file(&content) {
                Ok((meta, _)) => {
                    let dest = dest_dir.join(format!("{}.md", meta.name));
                    std::fs::write(&dest, &content)?;
                    println!("  {} Imported '{}' from archive", "✓".green(), meta.name);
                    count += 1;
                }
                Err(e) => {
                    eprintln!(
                        "  {}: Skipping {}: {}",
                        "Warning".yellow(),
                        entry_path.display(),
                        e
                    );
                }
            }
        }
    }

    println!("  Imported {} command(s) from {}", count, path);
    Ok(())
}

/// Import commands from a GitHub URL.
/// Supports: https://github.com/user/repo or github:user/repo
/// Clones to a temp dir, imports all .md files, cleans up.
fn import_github(source: &str, dest_dir: &Path) -> Result<()> {
    let url = if let Some(rest) = source.strip_prefix("github:") {
        format!("https://github.com/{}.git", rest)
    } else if !source.ends_with(".git") {
        format!("{}.git", source)
    } else {
        source.to_string()
    };

    let tmp_dir = std::env::temp_dir().join(format!("pah-import-{}", uuid::Uuid::new_v4()));
    println!("  Cloning {}...", url);

    let output = std::process::Command::new("git")
        .args(["clone", "--depth", "1", &url, &tmp_dir.to_string_lossy()])
        .output()
        .context("Failed to run git clone")?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        anyhow::bail!("git clone failed: {}", stderr);
    }

    let result = import_directory(&tmp_dir, dest_dir);

    // Clean up
    let _ = std::fs::remove_dir_all(&tmp_dir);

    result
}
