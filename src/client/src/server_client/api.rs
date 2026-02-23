use anyhow::{Context, Result};
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone)]
pub struct ServerClient {
    client: reqwest::Client,
    base_url: String,
    auth_token: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct RocqDeps {
    pub rocq_version: String,
    #[serde(default)]
    pub opam_packages: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct LeanDeps {
    pub lean_toolchain: String,
    #[serde(default)]
    pub lake_packages: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
#[serde(untagged)]
pub enum Dependencies {
    Rocq(RocqDeps),
    Lean(LeanDeps),
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct Conjecture {
    pub id: String,
    pub title: String,
    pub difficulty: String,
    pub prover: String,
    #[serde(default)]
    pub status: String,
    #[serde(default)]
    pub preamble: String,
    #[serde(default)]
    pub lemma_statement: String,
    #[serde(default)]
    pub hints: Vec<String>,
    #[serde(default)]
    pub skeleton: String,
    pub dependencies: Option<Dependencies>,
}

#[derive(Debug, Serialize, JsonSchema)]
pub struct Certificate {
    pub conjecture_id: String,
    pub username: String,
    pub success: bool,
    pub proof_script: String,
    pub cost_usd: f64,
    pub attempts: u32,
    pub error_output: String,
}

#[derive(Debug, Serialize, JsonSchema)]
pub struct ContributionSummary {
    pub username: String,
    pub contribution_id: String,
    pub conjectures_attempted: u32,
    pub conjectures_proved: u32,
    pub total_cost_usd: f64,
    pub archive_sha256: String,
    pub nft_metadata: serde_json::Value,
    pub proof_status: String,
}

#[derive(Debug, Deserialize)]
pub struct HealthResponse {
    pub status: String,
}

impl ServerClient {
    pub fn new(base_url: &str, auth_token: &str) -> Self {
        Self {
            client: reqwest::Client::new(),
            base_url: base_url.trim_end_matches('/').to_string(),
            auth_token: auth_token.to_string(),
        }
    }

    fn authed(&self, req: reqwest::RequestBuilder) -> reqwest::RequestBuilder {
        if self.auth_token.is_empty() {
            req
        } else {
            req.header("Authorization", format!("Bearer {}", self.auth_token))
        }
    }

    pub async fn health_check(&self) -> Result<bool> {
        let resp: HealthResponse = self
            .client
            .get(format!("{}/health", self.base_url))
            .send()
            .await
            .context("Failed to reach server")?
            .json()
            .await?;
        Ok(resp.status == "ok")
    }

    pub async fn fetch_conjectures(&self) -> Result<Vec<Conjecture>> {
        let conjectures: Vec<Conjecture> = self
            .client
            .get(format!("{}/conjectures", self.base_url))
            .send()
            .await
            .context("Failed to fetch conjectures")?
            .json()
            .await?;
        Ok(conjectures)
    }

    pub async fn fetch_conjecture(&self, id: &str) -> Result<Conjecture> {
        let conjecture: Conjecture = self
            .client
            .get(format!("{}/conjectures/{}", self.base_url, id))
            .send()
            .await
            .context("Failed to fetch conjecture")?
            .json()
            .await?;
        Ok(conjecture)
    }

    pub async fn submit_certificate(&self, result: &Certificate) -> Result<()> {
        let resp = self
            .authed(self.client.post(format!("{}/certificates", self.base_url)))
            .json(result)
            .send()
            .await
            .context("Failed to submit certificate")?;
        if !resp.status().is_success() {
            let body = resp.text().await.unwrap_or_default();
            anyhow::bail!("Server returned error: {}", body);
        }
        Ok(())
    }

    pub async fn submit_contribution(&self, summary: &ContributionSummary) -> Result<()> {
        let resp = self
            .authed(
                self.client
                    .post(format!("{}/certificates/batch", self.base_url)),
            )
            .json(summary)
            .send()
            .await
            .context("Failed to submit contribution")?;
        if !resp.status().is_success() {
            let body = resp.text().await.unwrap_or_default();
            anyhow::bail!("Server returned error: {}", body);
        }
        Ok(())
    }

    // ── Review endpoints ──

    /// Fetch available proof packages for review
    pub async fn fetch_review_packages(&self) -> Result<Vec<ReviewPackageInfo>> {
        let packages: Vec<ReviewPackageInfo> = self
            .client
            .get(format!("{}/review-packages", self.base_url))
            .send()
            .await
            .context("Failed to fetch review packages")?
            .json()
            .await?;
        Ok(packages)
    }

    /// Download a prover's archive to a local path
    pub async fn download_package(&self, session_id: &str, dest: &std::path::Path) -> Result<()> {
        let resp = self
            .client
            .get(format!(
                "{}/review-packages/{}/archive",
                self.base_url, session_id
            ))
            .send()
            .await
            .context("Failed to download package archive")?;

        if !resp.status().is_success() {
            let body = resp.text().await.unwrap_or_default();
            anyhow::bail!("Server returned error downloading archive: {}", body);
        }

        let bytes = resp.bytes().await?;
        std::fs::write(dest, &bytes)
            .with_context(|| format!("Failed to write archive to {}", dest.display()))?;
        Ok(())
    }

    /// Submit a review summary to the server
    pub async fn submit_review(&self, summary: &ReviewSummary) -> Result<()> {
        let resp = self
            .authed(self.client.post(format!("{}/reviews", self.base_url)))
            .json(summary)
            .send()
            .await
            .context("Failed to submit review")?;
        if !resp.status().is_success() {
            let body = resp.text().await.unwrap_or_default();
            anyhow::bail!("Server returned error: {}", body);
        }
        Ok(())
    }
}

// ── Package submission endpoints ──

#[derive(Debug, Clone, Deserialize)]
pub struct PackageSubmitResponse {
    #[allow(dead_code)]
    pub status: String,
    pub added_conjecture_ids: Vec<String>,
    pub count: u32,
}

impl ServerClient {
    /// Submit a tar.gz archive of conjecture JSON files
    pub async fn submit_package_tar(&self, tar_bytes: Vec<u8>) -> Result<PackageSubmitResponse> {
        let resp = self
            .authed(
                self.client
                    .post(format!("{}/conjectures/packages", self.base_url)),
            )
            .header("Content-Type", "application/gzip")
            .body(tar_bytes)
            .send()
            .await
            .context("Failed to submit package")?;
        if !resp.status().is_success() {
            let body = resp.text().await.unwrap_or_default();
            anyhow::bail!("Server returned error: {}", body);
        }
        let result: PackageSubmitResponse = resp.json().await?;
        Ok(result)
    }

    /// Submit a git URL for the server to clone
    pub async fn submit_package_git_url(&self, git_url: &str) -> Result<PackageSubmitResponse> {
        let resp = self
            .authed(
                self.client
                    .post(format!("{}/conjectures/packages", self.base_url)),
            )
            .json(&serde_json::json!({ "git_url": git_url }))
            .send()
            .await
            .context("Failed to submit package")?;
        if !resp.status().is_success() {
            let body = resp.text().await.unwrap_or_default();
            anyhow::bail!("Server returned error: {}", body);
        }
        let result: PackageSubmitResponse = resp.json().await?;
        Ok(result)
    }
}

// ── Review-related API types ──

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct ReviewPackageInfo {
    pub prover_contribution_id: String,
    pub prover_username: String,
    pub prover: String,
    pub conjecture_ids: Vec<String>,
    pub archive_url: String,
    pub archive_sha256: String,
    #[serde(default)]
    pub proof_status: String,
    #[serde(default)]
    pub reviewed_by: Vec<String>,
}

#[derive(Debug, Serialize, JsonSchema)]
pub struct ReviewSummary {
    pub reviewer_username: String,
    pub review_id: String,
    pub packages_reviewed: u32,
    pub conjectures_compared: u32,
    pub package_rankings: Vec<PackageRankingSummary>,
    pub recommendation: String,
    pub archive_sha256: String,
    pub nft_metadata: serde_json::Value,
}

#[derive(Debug, Serialize, JsonSchema)]
pub struct PackageRankingSummary {
    pub prover_contribution_id: String,
    pub rank: u32,
    pub overall_score: f64,
}
