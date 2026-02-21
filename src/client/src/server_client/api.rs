use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone)]
pub struct ServerClient {
    client: reqwest::Client,
    base_url: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RocqDeps {
    pub rocq_version: String,
    #[serde(default)]
    pub opam_packages: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LeanDeps {
    pub lean_toolchain: String,
    #[serde(default)]
    pub lake_packages: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(untagged)]
pub enum Dependencies {
    Rocq(RocqDeps),
    Lean(LeanDeps),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Problem {
    pub id: String,
    pub title: String,
    pub difficulty: String,
    pub proof_assistant: String,
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

#[derive(Debug, Serialize)]
pub struct ProofResult {
    pub problem_id: String,
    pub username: String,
    pub success: bool,
    pub proof_script: String,
    pub cost_usd: f64,
    pub attempts: u32,
    pub error_output: String,
}

#[derive(Debug, Serialize)]
pub struct SessionSummary {
    pub username: String,
    pub session_id: String,
    pub problems_attempted: u32,
    pub problems_proved: u32,
    pub total_cost_usd: f64,
    pub archive_sha256: String,
    pub nft_metadata: serde_json::Value,
}

#[derive(Debug, Deserialize)]
pub struct HealthResponse {
    pub status: String,
}

impl ServerClient {
    pub fn new(base_url: &str) -> Self {
        Self {
            client: reqwest::Client::new(),
            base_url: base_url.trim_end_matches('/').to_string(),
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

    pub async fn fetch_problems(&self) -> Result<Vec<Problem>> {
        let problems: Vec<Problem> = self
            .client
            .get(format!("{}/problems", self.base_url))
            .send()
            .await
            .context("Failed to fetch problems")?
            .json()
            .await?;
        Ok(problems)
    }

    pub async fn fetch_problem(&self, id: &str) -> Result<Problem> {
        let problem: Problem = self
            .client
            .get(format!("{}/problems/{}", self.base_url, id))
            .send()
            .await
            .context("Failed to fetch problem")?
            .json()
            .await?;
        Ok(problem)
    }

    pub async fn submit_result(&self, result: &ProofResult) -> Result<()> {
        let resp = self
            .client
            .post(format!("{}/results", self.base_url))
            .json(result)
            .send()
            .await
            .context("Failed to submit result")?;
        if !resp.status().is_success() {
            let body = resp.text().await.unwrap_or_default();
            anyhow::bail!("Server returned error: {}", body);
        }
        Ok(())
    }

    pub async fn submit_session(&self, summary: &SessionSummary) -> Result<()> {
        let resp = self
            .client
            .post(format!("{}/results/batch", self.base_url))
            .json(summary)
            .send()
            .await
            .context("Failed to submit session")?;
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
            .client
            .post(format!("{}/reviews", self.base_url))
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

// ── Review-related API types ──

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReviewPackageInfo {
    pub prover_session_id: String,
    pub prover_username: String,
    pub proof_assistant: String,
    pub problem_ids: Vec<String>,
    pub archive_url: String,
    pub archive_sha256: String,
}

#[derive(Debug, Serialize)]
pub struct ReviewSummary {
    pub reviewer_username: String,
    pub review_id: String,
    pub packages_reviewed: u32,
    pub problems_compared: u32,
    pub package_rankings: Vec<PackageRankingSummary>,
    pub recommendation: String,
    pub archive_sha256: String,
    pub nft_metadata: serde_json::Value,
}

#[derive(Debug, Serialize)]
pub struct PackageRankingSummary {
    pub prover_session_id: String,
    pub rank: u32,
    pub overall_score: f64,
}
