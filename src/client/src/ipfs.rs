use anyhow::{Context, Result};
use serde_json::Value;
use std::path::Path;

/// Pin a file to IPFS via a pinning service API. Returns the CID.
pub async fn pin_to_ipfs(file_path: &Path, api_url: &str, api_key: &str) -> Result<String> {
    let client = reqwest::Client::new();
    let file_bytes = std::fs::read(file_path)
        .with_context(|| format!("Failed to read {}", file_path.display()))?;

    let file_name = file_path
        .file_name()
        .and_then(|n| n.to_str())
        .unwrap_or("file");

    let part = reqwest::multipart::Part::bytes(file_bytes).file_name(file_name.to_string());
    let form = reqwest::multipart::Form::new().part("file", part);

    let url = format!("{}/pinning/pinFileToIPFS", api_url.trim_end_matches('/'));
    let resp = client
        .post(&url)
        .header("Authorization", format!("Bearer {}", api_key))
        .multipart(form)
        .send()
        .await
        .context("Failed to pin file to IPFS")?;

    if !resp.status().is_success() {
        let body = resp.text().await.unwrap_or_default();
        anyhow::bail!("IPFS pinning failed: {}", body);
    }

    let result: Value = resp.json().await?;
    let cid = result["IpfsHash"]
        .as_str()
        .context("No IpfsHash in pinning response")?
        .to_string();

    Ok(cid)
}

/// Pin JSON metadata to IPFS. Returns the CID.
pub async fn pin_json_to_ipfs(json: &Value, api_url: &str, api_key: &str) -> Result<String> {
    let client = reqwest::Client::new();

    let url = format!("{}/pinning/pinJSONToIPFS", api_url.trim_end_matches('/'));
    let resp = client
        .post(&url)
        .header("Authorization", format!("Bearer {}", api_key))
        .header("Content-Type", "application/json")
        .json(&serde_json::json!({
            "pinataContent": json,
        }))
        .send()
        .await
        .context("Failed to pin JSON to IPFS")?;

    if !resp.status().is_success() {
        let body = resp.text().await.unwrap_or_default();
        anyhow::bail!("IPFS JSON pinning failed: {}", body);
    }

    let result: Value = resp.json().await?;
    let cid = result["IpfsHash"]
        .as_str()
        .context("No IpfsHash in pinning response")?
        .to_string();

    Ok(cid)
}
