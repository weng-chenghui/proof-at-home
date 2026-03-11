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

#[derive(Debug, Serialize, Deserialize, JsonSchema)]
pub struct Proof {
    pub conjecture_id: String,
    pub username: String,
    pub success: bool,
    pub proof_script: String,
    pub cost_usd: f64,
    pub attempts: u32,
    pub error_output: String,
    #[serde(default)]
    pub contribution_id: String,
}

#[derive(Debug, Serialize, Deserialize, JsonSchema)]
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

    /// Fetch a PocketBase user record by ID (for extracting username/email during login).
    pub async fn get_pocketbase_user(&self, user_id: &str) -> Result<serde_json::Value> {
        let url = format!(
            "{}/api/collections/users/records/{}",
            self.base_url, user_id
        );
        let resp: serde_json::Value = self
            .client
            .get(&url)
            .header("Authorization", &self.auth_token)
            .send()
            .await
            .context("Failed to fetch user record")?
            .json()
            .await?;
        Ok(resp)
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

#[derive(Debug, Serialize, Deserialize, JsonSchema)]
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

#[derive(Debug, Serialize, Deserialize, JsonSchema)]
pub struct ContributionRanking {
    pub contributor_contribution_id: String,
    pub rank: u32,
    pub overall_score: f64,
}

#[derive(Debug, Clone, Deserialize)]
#[allow(dead_code)]
pub struct Strategy {
    pub name: String,
    #[serde(default)]
    pub kind: String,
    #[serde(default)]
    pub prover: String,
    #[serde(default)]
    pub description: String,
    #[serde(default)]
    pub priority: i32,
    #[serde(default)]
    pub body: String,
    #[serde(default)]
    pub version: Option<String>,
    #[serde(default)]
    pub author: Option<String>,
    #[serde(default)]
    pub license: Option<String>,
    #[serde(default)]
    pub source: Option<String>,
}

impl ServerClient {
    pub async fn fetch_contributions(&self) -> Result<Vec<Contribution>> {
        let items: Vec<Contribution> = self
            .authed(self.client.get(format!("{}/contributions", self.base_url)))
            .send()
            .await
            .context("Failed to fetch contributions")?
            .json()
            .await?;
        Ok(items)
    }

    pub async fn fetch_contribution(&self, id: &str) -> Result<Contribution> {
        let item: Contribution = self
            .authed(
                self.client
                    .get(format!("{}/contributions/{}", self.base_url, id)),
            )
            .send()
            .await
            .context("Failed to fetch contribution")?
            .json()
            .await?;
        Ok(item)
    }

    pub async fn fetch_proofs(&self, contribution_id: &str) -> Result<Vec<Proof>> {
        let items: Vec<Proof> = self
            .authed(self.client.get(format!(
                "{}/contributions/{}/proofs",
                self.base_url, contribution_id
            )))
            .send()
            .await
            .context("Failed to fetch proofs")?
            .json()
            .await?;
        Ok(items)
    }

    pub async fn fetch_certificates(&self) -> Result<Vec<Certificate>> {
        let items: Vec<Certificate> = self
            .authed(self.client.get(format!("{}/certificates", self.base_url)))
            .send()
            .await
            .context("Failed to fetch certificates")?
            .json()
            .await?;
        Ok(items)
    }

    pub async fn fetch_strategies(&self) -> Result<Vec<Strategy>> {
        let items: Vec<Strategy> = self
            .authed(self.client.get(format!("{}/strategies", self.base_url)))
            .send()
            .await
            .context("Failed to fetch strategies")?
            .json()
            .await?;
        Ok(items)
    }

    pub async fn fetch_strategy(&self, name: &str) -> Result<Strategy> {
        let item: Strategy = self
            .authed(
                self.client
                    .get(format!("{}/strategies/{}", self.base_url, name)),
            )
            .send()
            .await
            .context("Failed to fetch strategy")?
            .json()
            .await?;
        Ok(item)
    }

    pub async fn get_pool_url(&self) -> Result<String> {
        let resp: PoolUrlResponse = self
            .authed(self.client.get(format!("{}/api/pool-url", self.base_url)))
            .send()
            .await
            .context("Failed to fetch pool URL")?
            .json()
            .await?;
        Ok(resp.git_url)
    }
}

#[derive(Debug, Deserialize)]
struct PoolUrlResponse {
    git_url: String,
}

// ── Exposition endpoints ──

#[derive(Debug, Serialize, Deserialize)]
pub struct SubmitExpositionRequest {
    pub exposition_id: String,
    pub author_username: String,
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub contribution_id: String,
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub conjecture_id: String,
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub prover: String,
    pub proof_script: String,
    pub exposition_text: String,
    pub cost_usd: f64,
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub strategy_used: String,
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub domain: String,
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub title: String,
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub summary: String,
}

#[derive(Debug, Deserialize)]
#[allow(dead_code)]
pub struct ExpositionRecord {
    pub exposition_id: String,
    pub author_username: String,
    pub exposition_text: String,
    pub cost_usd: f64,
    #[serde(default)]
    pub conjecture_id: String,
    #[serde(default)]
    pub contribution_id: String,
    #[serde(default)]
    pub prover: String,
    #[serde(default)]
    pub strategy_used: String,
    #[serde(default)]
    pub domain: String,
    #[serde(default)]
    pub title: String,
    #[serde(default)]
    pub summary: String,
}

impl ServerClient {
    /// Submit an exposition to the server. Returns commit SHA.
    pub async fn submit_exposition(
        &self,
        req: &SubmitExpositionRequest,
    ) -> Result<FinalizeResponse> {
        let resp = self
            .authed(self.client.post(format!("{}/expositions", self.base_url)))
            .json(req)
            .send()
            .await
            .context("Failed to submit exposition")?;
        if !resp.status().is_success() {
            let body = resp.text().await.unwrap_or_default();
            anyhow::bail!("Server returned error: {}", body);
        }
        let result: FinalizeResponse = resp.json().await?;
        Ok(result)
    }

    /// Seal an exposition with NFT metadata. Creates a PR in the data repo.
    pub async fn seal_exposition(
        &self,
        exposition_id: &str,
        nft_metadata: &serde_json::Value,
    ) -> Result<SealResponse> {
        let resp = self
            .authed(self.client.post(format!(
                "{}/expositions/{}/seal",
                self.base_url, exposition_id
            )))
            .json(nft_metadata)
            .send()
            .await
            .context("Failed to seal exposition")?;
        if !resp.status().is_success() {
            let body = resp.text().await.unwrap_or_default();
            anyhow::bail!("Server returned error: {}", body);
        }
        let result: SealResponse = resp.json().await?;
        Ok(result)
    }

    /// Fetch all expositions from the server.
    pub async fn fetch_expositions(&self) -> Result<Vec<ExpositionRecord>> {
        let items: Vec<ExpositionRecord> = self
            .authed(self.client.get(format!("{}/expositions", self.base_url)))
            .send()
            .await
            .context("Failed to fetch expositions")?
            .json()
            .await?;
        Ok(items)
    }

    /// Fetch a single exposition by ID.
    pub async fn fetch_exposition(&self, id: &str) -> Result<ExpositionRecord> {
        let item: ExpositionRecord = self
            .authed(
                self.client
                    .get(format!("{}/expositions/{}", self.base_url, id)),
            )
            .send()
            .await
            .context("Failed to fetch exposition")?
            .json()
            .await?;
        Ok(item)
    }
}

// ── Lesson endpoints ──

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LessonRecord {
    pub lesson_id: String,
    #[serde(default)]
    pub author_username: String,
    #[serde(default)]
    pub title: String,
    #[serde(default)]
    pub topic: String,
    #[serde(default)]
    pub difficulty: String,
    #[serde(default)]
    pub description: String,
    #[serde(default)]
    pub prerequisites: String,
    #[serde(default)]
    pub conjecture_ids: Vec<String>,
    #[serde(default)]
    pub published: bool,
    #[serde(default)]
    pub created_at: String,
    #[serde(default)]
    pub content: String,
    #[serde(default)]
    pub ai_annotations: Vec<AIAnnotation>,
    #[serde(default)]
    pub references: Vec<serde_json::Value>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AIAnnotation {
    pub zone: String,
    #[serde(default)]
    pub context: String,
    #[serde(default)]
    pub suggestions: Vec<String>,
}

#[derive(Debug, Serialize)]
pub struct CreateLessonRequest {
    pub lesson_id: String,
    pub author_username: String,
    pub title: String,
    #[serde(skip_serializing_if = "String::is_empty")]
    pub topic: String,
    #[serde(skip_serializing_if = "String::is_empty")]
    pub difficulty: String,
    #[serde(skip_serializing_if = "String::is_empty")]
    pub description: String,
    #[serde(skip_serializing_if = "String::is_empty")]
    pub prerequisites: String,
    pub conjecture_ids: Vec<String>,
    pub published: bool,
    #[serde(skip_serializing_if = "String::is_empty")]
    pub content: String,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub ai_annotations: Vec<AIAnnotation>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub references: Vec<serde_json::Value>,
}

impl ServerClient {
    /// Fetch all lessons from the server.
    pub async fn fetch_lessons(&self) -> Result<Vec<LessonRecord>> {
        let items: Vec<LessonRecord> = self
            .client
            .get(format!("{}/lessons", self.base_url))
            .send()
            .await
            .context("Failed to fetch lessons")?
            .json()
            .await?;
        Ok(items)
    }

    /// Fetch a single lesson by ID.
    pub async fn fetch_lesson(&self, id: &str) -> Result<LessonRecord> {
        let item: LessonRecord = self
            .client
            .get(format!("{}/lessons/{}", self.base_url, id))
            .send()
            .await
            .context("Failed to fetch lesson")?
            .json()
            .await?;
        Ok(item)
    }

    /// Create a lesson on the server.
    pub async fn create_lesson(&self, req: &CreateLessonRequest) -> Result<FinalizeResponse> {
        let resp = self
            .authed(self.client.post(format!("{}/lessons", self.base_url)))
            .json(req)
            .send()
            .await
            .context("Failed to create lesson")?;
        if !resp.status().is_success() {
            let body = resp.text().await.unwrap_or_default();
            anyhow::bail!("Server returned error: {}", body);
        }
        let result: FinalizeResponse = resp.json().await?;
        Ok(result)
    }
}

// ── Series endpoints ──

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SeriesRecord {
    pub series_id: String,
    #[serde(default)]
    pub title: String,
    #[serde(default)]
    pub author_username: String,
    #[serde(default)]
    pub difficulty: String,
    #[serde(default)]
    pub description: String,
    #[serde(default)]
    pub lesson_ids: Vec<String>,
    #[serde(default)]
    pub published: bool,
    #[serde(default)]
    pub created_at: String,
    #[serde(default)]
    pub content: String,
}

#[derive(Debug, Serialize)]
pub struct CreateSeriesRequest {
    pub series_id: String,
    pub title: String,
    pub author_username: String,
    #[serde(skip_serializing_if = "String::is_empty")]
    pub difficulty: String,
    #[serde(skip_serializing_if = "String::is_empty")]
    pub description: String,
    pub lesson_ids: Vec<String>,
    pub published: bool,
    #[serde(skip_serializing_if = "String::is_empty")]
    pub content: String,
}

impl ServerClient {
    /// Fetch all series from the server.
    pub async fn fetch_all_series(&self) -> Result<Vec<SeriesRecord>> {
        let items: Vec<SeriesRecord> = self
            .client
            .get(format!("{}/series", self.base_url))
            .send()
            .await
            .context("Failed to fetch series")?
            .json()
            .await?;
        Ok(items)
    }

    /// Fetch a single series by ID.
    pub async fn fetch_series(&self, id: &str) -> Result<SeriesRecord> {
        let item: SeriesRecord = self
            .client
            .get(format!("{}/series/{}", self.base_url, id))
            .send()
            .await
            .context("Failed to fetch series")?
            .json()
            .await?;
        Ok(item)
    }

    /// Bump the edition for a lesson or series. POST /{kind}s/{id}/edition-bump
    pub async fn edition_bump(
        &self,
        kind: &str,
        id: &str,
        summary: &str,
    ) -> Result<FinalizeResponse> {
        let resource = if kind == "lesson" {
            "lessons"
        } else {
            "series"
        };
        let resp = self
            .authed(self.client.post(format!(
                "{}/{}/{}/edition-bump",
                self.base_url, resource, id
            )))
            .json(&serde_json::json!({"summary": summary}))
            .send()
            .await
            .context("Failed to bump edition")?;
        if !resp.status().is_success() {
            let body = resp.text().await.unwrap_or_default();
            anyhow::bail!("Server returned error: {}", body);
        }
        let result: FinalizeResponse = resp.json().await?;
        Ok(result)
    }

    /// Create a series on the server.
    pub async fn create_series(&self, req: &CreateSeriesRequest) -> Result<FinalizeResponse> {
        let resp = self
            .authed(self.client.post(format!("{}/series", self.base_url)))
            .json(req)
            .send()
            .await
            .context("Failed to create series")?;
        if !resp.status().is_success() {
            let body = resp.text().await.unwrap_or_default();
            anyhow::bail!("Server returned error: {}", body);
        }
        let result: FinalizeResponse = resp.json().await?;
        Ok(result)
    }
}

// ── Note endpoints ──

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NoteRecord {
    pub note_id: String,
    pub lesson_id: String,
    #[serde(default)]
    pub anchor_text: String,
    #[serde(default)]
    pub content: String,
    #[serde(default)]
    pub highlight_color: String,
    #[serde(default)]
    pub user_id: String,
    #[serde(default)]
    pub username: String,
    #[serde(default)]
    pub status: String,
    #[serde(default)]
    pub created_at: String,
    #[serde(default)]
    pub updated_at: String,
}

impl ServerClient {
    /// Fetch all notes for a lesson.
    pub async fn fetch_notes(&self, lesson_id: &str) -> Result<Vec<NoteRecord>> {
        let items: Vec<NoteRecord> = self
            .client
            .get(format!("{}/lessons/{}/notes", self.base_url, lesson_id))
            .send()
            .await
            .context("Failed to fetch notes")?
            .json()
            .await?;
        Ok(items)
    }

    /// Update a note's status (or other fields).
    pub async fn update_note_status(&self, note_id: &str, status: &str) -> Result<()> {
        let resp = self
            .authed(
                self.client
                    .patch(format!("{}/notes/{}", self.base_url, note_id)),
            )
            .json(&serde_json::json!({"status": status}))
            .send()
            .await
            .context("Failed to update note")?;
        if !resp.status().is_success() {
            let body = resp.text().await.unwrap_or_default();
            anyhow::bail!("Server returned error: {}", body);
        }
        Ok(())
    }
}
