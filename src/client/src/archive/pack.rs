use anyhow::{Context, Result};
use flate2::write::GzEncoder;
use flate2::Compression;
use sha2::{Digest, Sha256};
use std::fs;
use std::io::Read;
use std::path::{Path, PathBuf};

/// Create a tar.gz archive of all proof files in `source_dir` and return (archive_path, sha256_hex)
pub fn create_archive(source_dir: &Path, output_dir: &Path) -> Result<(PathBuf, String)> {
    fs::create_dir_all(output_dir)?;
    let archive_path = output_dir.join("proofs.tar.gz");

    // Create tar.gz
    let tar_gz = fs::File::create(&archive_path)?;
    let enc = GzEncoder::new(tar_gz, Compression::default());
    let mut tar = tar::Builder::new(enc);

    // Add all .v and .lean files from the source directory
    if source_dir.exists() {
        for entry in fs::read_dir(source_dir)? {
            let entry = entry?;
            let path = entry.path();
            if let Some(ext) = path.extension() {
                if ext == "v" || ext == "lean" {
                    let file_name = path
                        .file_name()
                        .context("No filename")?
                        .to_string_lossy()
                        .to_string();
                    tar.append_path_with_name(&path, &file_name)?;
                }
            }
        }
    }

    tar.into_inner()?.finish()?;

    // Compute SHA-256
    let sha256 = compute_sha256(&archive_path)?;

    Ok((archive_path, sha256))
}

pub fn compute_sha256(file_path: &Path) -> Result<String> {
    let mut file = fs::File::open(file_path)?;
    let mut hasher = Sha256::new();
    let mut buffer = [0u8; 8192];

    loop {
        let bytes_read = file.read(&mut buffer)?;
        if bytes_read == 0 {
            break;
        }
        hasher.update(&buffer[..bytes_read]);
    }

    Ok(hex::encode(hasher.finalize()))
}
