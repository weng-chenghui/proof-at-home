// "prover" = machine/software (proof assistant, e.g. rocq/lean4);
// "contributor" = the human person who submitted or ran the proof.
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
pub struct Proof {
    pub conjecture_id: String,
    pub username: String,
    pub success: bool,
    pub proof_script: String,
    pub cost_usd: f64,
    pub attempts: u32,
    pub error_output: String,
}

#[derive(Debug, Serialize, JsonSchema)]
pub struct Contribution {
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

/// Response from PATCH /contributions/{id} (finalize)
#[derive(Debug, Deserialize)]
pub struct FinalizeResponse {
    pub commit_sha: String,
    #[allow(dead_code)]
    pub status: String,
}

/// Response from POST /contributions/{id}/seal or POST /certificates/{id}/seal
#[derive(Debug, Deserialize)]
pub struct SealResponse {
    pub pr_url: String,
    #[allow(dead_code)]
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

    pub async fn create_contribution(
        &self,
        contribution_id: &str,
        username: &str,
        prover: &str,
    ) -> Result<()> {
        let resp = self
            .authed(self.client.post(format!("{}/contributions", self.base_url)))
            .json(&serde_json::json!({
                "contribution_id": contribution_id,
                "username": username,
                "prover": prover,
            }))
            .send()
            .await
            .context("Failed to create contribution")?;
        if !resp.status().is_success() {
            let body = resp.text().await.unwrap_or_default();
            anyhow::bail!("Server returned error: {}", body);
        }
        Ok(())
    }

    pub async fn submit_proof(&self, contribution_id: &str, result: &Proof) -> Result<()> {
        let resp = self
            .authed(self.client.post(format!(
                "{}/contributions/{}/proofs",
                self.base_url, contribution_id
            )))
            .json(result)
            .send()
            .await
            .context("Failed to submit contribution result")?;
        if !resp.status().is_success() {
            let body = resp.text().await.unwrap_or_default();
            anyhow::bail!("Server returned error: {}", body);
        }
        Ok(())
    }

    /// Finalize a contribution (cost totals, proof_status).
    /// Returns the git commit SHA for signing.
    pub async fn update_contribution(
        &self,
        contribution_id: &str,
        summary: &Contribution,
    ) -> Result<FinalizeResponse> {
        let resp = self
            .authed(self.client.patch(format!(
                "{}/contributions/{}",
                self.base_url, contribution_id
            )))
            .json(summary)
            .send()
            .await
            .context("Failed to update contribution")?;
        if !resp.status().is_success() {
            let body = resp.text().await.unwrap_or_default();
            anyhow::bail!("Server returned error: {}", body);
        }
        let result: FinalizeResponse = resp.json().await?;
        Ok(result)
    }

    /// Seal a contribution with NFT metadata. Creates a PR in the data repo.
    pub async fn seal_contribution(
        &self,
        contribution_id: &str,
        nft_metadata: &serde_json::Value,
    ) -> Result<SealResponse> {
        let resp = self
            .authed(self.client.post(format!(
                "{}/contributions/{}/seal",
                self.base_url, contribution_id
            )))
            .json(nft_metadata)
            .send()
            .await
            .context("Failed to seal contribution")?;
        if !resp.status().is_success() {
            let body = resp.text().await.unwrap_or_default();
            anyhow::bail!("Server returned error: {}", body);
        }
        let result: SealResponse = resp.json().await?;
        Ok(result)
    }

    // ── Certificate endpoints ──

    /// Fetch available proof packages for certification
    pub async fn fetch_contribution_reviews(&self) -> Result<Vec<ContributionReview>> {
        let packages: Vec<ContributionReview> = self
            .client
            .get(format!("{}/contribution-reviews", self.base_url))
            .send()
            .await
            .context("Failed to fetch certificate packages")?
            .json()
            .await?;
        Ok(packages)
    }

    /// Download a prover's archive to a local path
    pub async fn download_package(&self, session_id: &str, dest: &std::path::Path) -> Result<()> {
        let resp = self
            .client
            .get(format!(
                "{}/contributions/{}/archive",
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

    /// Submit a certificate summary to the server. Returns commit SHA.
    pub async fn submit_certificate(&self, summary: &Certificate) -> Result<FinalizeResponse> {
        let resp = self
            .authed(self.client.post(format!("{}/certificates", self.base_url)))
            .json(summary)
            .send()
            .await
            .context("Failed to submit certificate")?;
        if !resp.status().is_success() {
            let body = resp.text().await.unwrap_or_default();
            anyhow::bail!("Server returned error: {}", body);
        }
        let result: FinalizeResponse = resp.json().await?;
        Ok(result)
    }

    /// Seal a certificate with NFT metadata. Creates a PR in the data repo.
    pub async fn seal_certificate(
        &self,
        certificate_id: &str,
        nft_metadata: &serde_json::Value,
    ) -> Result<SealResponse> {
        let resp = self
            .authed(self.client.post(format!(
                "{}/certificates/{}/seal",
                self.base_url, certificate_id
            )))
            .json(nft_metadata)
            .send()
            .await
            .context("Failed to seal certificate")?;
        if !resp.status().is_success() {
            let body = resp.text().await.unwrap_or_default();
            anyhow::bail!("Server returned error: {}", body);
        }
        let result: SealResponse = resp.json().await?;
        Ok(result)
    }
}

// ── Package submission endpoints ──

#[derive(Debug, Clone, Deserialize)]
pub struct ConjectureCreateResponse {
    #[allow(dead_code)]
    pub status: String,
    pub added_conjecture_ids: Vec<String>,
    pub count: u32,
    pub batch_id: String,
    pub commit_sha: String,
    #[allow(dead_code)]
    pub pr_url: String,
    #[serde(default)]
    pub difficulties: Vec<String>,
    #[serde(default)]
    pub proof_assistants: Vec<String>,
}

impl ServerClient {
    /// Submit a tar.gz archive of conjecture JSON files
    pub async fn create_conjecture_tar(
        &self,
        tar_bytes: Vec<u8>,
    ) -> Result<ConjectureCreateResponse> {
        let resp = self
            .authed(self.client.post(format!("{}/conjectures", self.base_url)))
            .header("Content-Type", "application/gzip")
            .body(tar_bytes)
            .send()
            .await
            .context("Failed to submit package")?;
        if !resp.status().is_success() {
            let body = resp.text().await.unwrap_or_default();
            anyhow::bail!("Server returned error: {}", body);
        }
        let result: ConjectureCreateResponse = resp.json().await?;
        Ok(result)
    }

    /// Submit a git URL for the server to clone
    pub async fn create_conjecture_git_url(
        &self,
        git_url: &str,
    ) -> Result<ConjectureCreateResponse> {
        let resp = self
            .authed(self.client.post(format!("{}/conjectures", self.base_url)))
            .json(&serde_json::json!({ "git_url": git_url }))
            .send()
            .await
            .context("Failed to submit package")?;
        if !resp.status().is_success() {
            let body = resp.text().await.unwrap_or_default();
            anyhow::bail!("Server returned error: {}", body);
        }
        let result: ConjectureCreateResponse = resp.json().await?;
        Ok(result)
    }

    /// Seal a conjecture package with NFT metadata. Returns the PR URL.
    pub async fn seal_conjecture_batch(
        &self,
        batch_id: &str,
        nft_metadata: &serde_json::Value,
    ) -> Result<SealResponse> {
        let resp = self
            .authed(self.client.post(format!(
                "{}/conjectures/batches/{}/seal",
                self.base_url, batch_id
            )))
            .json(nft_metadata)
            .send()
            .await
            .context("Failed to seal conjecture package")?;
        if !resp.status().is_success() {
            let body = resp.text().await.unwrap_or_default();
            anyhow::bail!("Server returned error: {}", body);
        }
        let result: SealResponse = resp.json().await?;
        Ok(result)
    }
}

// ── Certificate-related API types ──

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct ContributionReview {
    pub contributor_contribution_id: String,
    pub contributor_username: String,
    /// The proof assistant software (e.g. "rocq", "lean4") — not the human.
    pub prover: String,
    pub conjecture_ids: Vec<String>,
    pub archive_url: String,
    pub archive_sha256: String,
    #[serde(default)]
    pub proof_status: String,
    #[serde(default)]
    pub certified_by: Vec<String>,
}

#[derive(Debug, Serialize, JsonSchema)]
pub struct Certificate {
    pub certifier_username: String,
    pub certificate_id: String,
    pub packages_certified: u32,
    pub conjectures_compared: u32,
    pub package_rankings: Vec<ContributionRanking>,
    pub recommendation: String,
    pub archive_sha256: String,
    pub nft_metadata: serde_json::Value,
}

#[derive(Debug, Serialize, JsonSchema)]
pub struct ContributionRanking {
    pub contributor_contribution_id: String,
    pub rank: u32,
    pub overall_score: f64,
}
