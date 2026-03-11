// "prover" = machine/software (proof assistant, e.g. rocq/lean4);
// "contributor" = the human person who submitted or ran the proof.
use chrono::Utc;
use schemars::JsonSchema;
use serde::Serialize;
use serde_json::{json, Value};

#[derive(Debug, Serialize, JsonSchema)]
pub struct ContributionInfo {
    pub username: String,
    pub conjectures_proved: u32,
    pub conjectures_attempted: u32,
    pub cost_donated_usd: f64,
    /// The proof assistant software (e.g. "rocq", "lean4") — not the human contributor.
    pub prover: String,
    pub proof_status: String,
    pub git_commit: String,
    pub git_repository: String,
    pub public_key: String,
    pub commit_signature: String,
    /// "manual" or "ai-assisted"
    pub proof_mode: String,
    /// Optional ID of the contribution this work is based on (provenance chain)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub based_on_contribution_id: Option<String>,
}

/// Generate OpenSea-compatible NFT metadata JSON for a proof contribution
pub fn generate_nft_metadata(info: &ContributionInfo) -> Value {
    let date = Utc::now().format("%Y-%m-%d").to_string();

    let mut attributes = vec![
        json!({"trait_type": "Username", "value": info.username}),
        json!({"trait_type": "Conjectures Proved", "value": info.conjectures_proved}),
        json!({"trait_type": "Conjectures Attempted", "value": info.conjectures_attempted}),
        json!({"trait_type": "Cost Donated (USD)", "value": format!("{:.2}", info.cost_donated_usd)}),
        json!({"trait_type": "Prover", "value": info.prover}),
        json!({"trait_type": "Proof Status", "value": info.proof_status}),
        json!({"trait_type": "Git Commit", "value": info.git_commit}),
        json!({"trait_type": "Git Repository", "value": info.git_repository}),
        json!({"trait_type": "Public Key", "value": info.public_key}),
        json!({"trait_type": "Commit Signature", "value": info.commit_signature}),
        json!({"trait_type": "Proof Mode", "value": info.proof_mode}),
    ];

    if let Some(based_on) = &info.based_on_contribution_id {
        attributes.push(json!({"trait_type": "Based On Contribution", "value": based_on}));
    }

    json!({
        "name": format!("Proof@Home Contribution — {} — {}", info.username, date),
        "description": "Formally verified mathematical proofs for the public domain.",
        "external_url": "",
        "image": "",
        "attributes": attributes
    })
}

// ── Certificate NFT metadata ──

#[derive(Debug, Serialize, JsonSchema)]
pub struct CertificateInfo {
    pub certifier_username: String,
    pub certificate_id: String,
    pub packages_certified: u32,
    pub conjectures_compared: u32,
    pub top_contributor: String,
    pub recommendation: String,
    pub ai_comparison_cost_usd: f64,
    pub certified_contribution_ids: Vec<String>,
    pub git_commit: String,
    pub git_repository: String,
    pub certifier_public_key: String,
    pub commit_signature: String,
}

/// Generate OpenSea-compatible NFT metadata JSON for a certificate
pub fn generate_certificate_nft_metadata(info: &CertificateInfo) -> Value {
    let date = Utc::now().format("%Y-%m-%d").to_string();

    json!({
        "name": format!("Proof@Home Certificate — {} — {}", info.certifier_username, date),
        "description": "Certificate record: human evaluation of formally verified proofs.",
        "external_url": "",
        "image": "",
        "attributes": [
            {
                "trait_type": "Certifier",
                "value": info.certifier_username
            },
            {
                "trait_type": "Certificate ID",
                "value": info.certificate_id
            },
            {
                "trait_type": "Packages Certified",
                "value": info.packages_certified
            },
            {
                "trait_type": "Conjectures Compared",
                "value": info.conjectures_compared
            },
            {
                "trait_type": "Top Contributor",
                "value": info.top_contributor
            },
            {
                "trait_type": "Recommendation",
                "value": info.recommendation
            },
            {
                "trait_type": "Git Commit",
                "value": info.git_commit
            },
            {
                "trait_type": "Git Repository",
                "value": info.git_repository
            },
            {
                "trait_type": "Public Key",
                "value": info.certifier_public_key
            },
            {
                "trait_type": "Commit Signature",
                "value": info.commit_signature
            },
            {
                "trait_type": "AI Comparison Cost (USD)",
                "value": format!("{:.4}", info.ai_comparison_cost_usd)
            },
            {
                "trait_type": "Certified Contribution IDs",
                "value": info.certified_contribution_ids.join(", ")
            }
        ]
    })
}

// ── Conjecture Submitter NFT metadata ──

#[derive(Debug, Serialize, JsonSchema)]
pub struct ConjectureSubmitterInfo {
    pub submitter_username: String,
    pub batch_id: String,
    pub conjectures_submitted: u32,
    pub conjecture_ids: Vec<String>,
    pub difficulties: Vec<String>,
    pub proof_assistants: Vec<String>,
    pub git_commit: String,
    pub git_repository: String,
    pub public_key: String,
    pub commit_signature: String,
    #[serde(default)]
    pub source_attribution: Option<String>,
}

/// Generate OpenSea-compatible NFT metadata JSON for a conjecture submission
pub fn generate_submitter_nft_metadata(info: &ConjectureSubmitterInfo) -> Value {
    let date = Utc::now().format("%Y-%m-%d").to_string();

    let mut attributes = vec![
        json!({"trait_type": "Submitter", "value": info.submitter_username}),
        json!({"trait_type": "Batch ID", "value": info.batch_id}),
        json!({"trait_type": "Conjectures Submitted", "value": info.conjectures_submitted}),
        json!({"trait_type": "Conjecture IDs", "value": info.conjecture_ids.join(", ")}),
        json!({"trait_type": "Difficulties", "value": info.difficulties.join(", ")}),
        json!({"trait_type": "Proof Assistants", "value": info.proof_assistants.join(", ")}),
        json!({"trait_type": "Git Commit", "value": info.git_commit}),
        json!({"trait_type": "Git Repository", "value": info.git_repository}),
        json!({"trait_type": "Public Key", "value": info.public_key}),
        json!({"trait_type": "Commit Signature", "value": info.commit_signature}),
    ];

    if let Some(attr) = &info.source_attribution {
        attributes.push(json!({"trait_type": "Conjecture Source", "value": attr}));
    }

    json!({
        "name": format!("Proof@Home Conjecture Submission — {} — {}", info.submitter_username, date),
        "description": "Conjecture submission record: conjectures contributed for formal verification.",
        "external_url": "",
        "image": "",
        "attributes": attributes
    })
}

// ── Exposition NFT metadata ──

#[derive(Debug, Serialize, JsonSchema)]
pub struct ExpositionInfo {
    pub author_username: String,
    pub exposition_id: String,
    pub conjecture_id: String,
    pub contribution_id: String,
    /// The proof assistant software (e.g. "rocq", "lean4") — not the human.
    pub prover: String,
    pub cost_usd: f64,
    pub strategy_used: String,
    pub git_commit: String,
    pub git_repository: String,
    pub public_key: String,
    pub commit_signature: String,
}

/// Generate OpenSea-compatible NFT metadata JSON for an exposition
pub fn generate_exposition_nft_metadata(info: &ExpositionInfo) -> Value {
    let date = Utc::now().format("%Y-%m-%d").to_string();

    json!({
        "name": format!("Proof@Home Exposition — {} — {}", info.author_username, date),
        "description": "AI-generated proof exposition: a human-readable explanation of a formal proof.",
        "external_url": "",
        "image": "",
        "attributes": [
            {
                "trait_type": "Author Username",
                "value": info.author_username
            },
            {
                "trait_type": "Exposition ID",
                "value": info.exposition_id
            },
            {
                "trait_type": "Conjecture ID",
                "value": info.conjecture_id
            },
            {
                "trait_type": "Contribution ID",
                "value": info.contribution_id
            },
            {
                "trait_type": "Prover",
                "value": info.prover
            },
            {
                "trait_type": "AI Cost (USD)",
                "value": format!("{:.4}", info.cost_usd)
            },
            {
                "trait_type": "Strategy Used",
                "value": info.strategy_used
            },
            {
                "trait_type": "Git Commit",
                "value": info.git_commit
            },
            {
                "trait_type": "Git Repository",
                "value": info.git_repository
            },
            {
                "trait_type": "Public Key",
                "value": info.public_key
            },
            {
                "trait_type": "Commit Signature",
                "value": info.commit_signature
            }
        ]
    })
}

// ── Agent Memory NFT metadata ──

#[allow(dead_code)]
#[derive(Debug, Serialize, JsonSchema)]
pub struct AgentMemoryInfo {
    pub author_username: String,
    pub agent_id: String,
    pub run_id: String,
    pub memories_created: u32,
    pub memories_refined: u32,
    pub memory_kinds: Vec<String>,
    pub total_cost_usd: f64,
    pub content_hash: String,
    pub git_commit: String,
    pub git_repository: String,
    pub public_key: String,
    pub commit_signature: String,
}

/// Generate OpenSea-compatible NFT metadata JSON for agent memory contribution
#[allow(dead_code)]
pub fn generate_agent_memory_nft_metadata(info: &AgentMemoryInfo) -> Value {
    let date = Utc::now().format("%Y-%m-%d").to_string();

    json!({
        "name": format!("Proof@Home Agent Memory — {} — {}", info.author_username, date),
        "description": "Agent memory contribution: reusable knowledge extracted from lesson generation.",
        "external_url": "",
        "image": "",
        "attributes": [
            {"trait_type": "Author Username", "value": info.author_username},
            {"trait_type": "Agent ID", "value": info.agent_id},
            {"trait_type": "Run ID", "value": info.run_id},
            {"trait_type": "Memories Created", "value": info.memories_created},
            {"trait_type": "Memories Refined", "value": info.memories_refined},
            {"trait_type": "Memory Kinds", "value": info.memory_kinds.join(", ")},
            {"trait_type": "Total Cost (USD)", "value": format!("{:.4}", info.total_cost_usd)},
            {"trait_type": "Content Hash", "value": info.content_hash},
            {"trait_type": "Git Commit", "value": info.git_commit},
            {"trait_type": "Git Repository", "value": info.git_repository},
            {"trait_type": "Public Key", "value": info.public_key},
            {"trait_type": "Commit Signature", "value": info.commit_signature}
        ]
    })
}

// ── Series NFT metadata ──

#[allow(dead_code)]
#[derive(Debug, Serialize, JsonSchema)]
pub struct SeriesInfo {
    pub author_username: String,
    pub series_id: String,
    pub title: String,
    pub lesson_count: u32,
    pub topic: String,
    pub difficulty_range: String,
    pub total_conjectures: u32,
    pub package_sha256: String,
    pub git_commit: String,
    pub git_repository: String,
    pub public_key: String,
    pub commit_signature: String,
}

/// Generate OpenSea-compatible NFT metadata JSON for a sealed series
#[allow(dead_code)]
pub fn generate_series_nft_metadata(info: &SeriesInfo) -> Value {
    let date = Utc::now().format("%Y-%m-%d").to_string();

    json!({
        "name": format!("Proof@Home Series — {} — {}", info.title, date),
        "description": "Sealed lesson series: a complete curriculum of formally verified mathematics.",
        "external_url": "",
        "image": "",
        "attributes": [
            {"trait_type": "Author Username", "value": info.author_username},
            {"trait_type": "Series ID", "value": info.series_id},
            {"trait_type": "Title", "value": info.title},
            {"trait_type": "Lesson Count", "value": info.lesson_count},
            {"trait_type": "Topic", "value": info.topic},
            {"trait_type": "Difficulty Range", "value": info.difficulty_range},
            {"trait_type": "Total Conjectures", "value": info.total_conjectures},
            {"trait_type": "Package SHA256", "value": info.package_sha256},
            {"trait_type": "Git Commit", "value": info.git_commit},
            {"trait_type": "Git Repository", "value": info.git_repository},
            {"trait_type": "Public Key", "value": info.public_key},
            {"trait_type": "Commit Signature", "value": info.commit_signature}
        ]
    })
}

// ── Schema-only structs mirroring the NFT JSON output shape ──
// Used by gen-schemas binary; not constructed in the main binary.

#[allow(dead_code)]
#[derive(Debug, Serialize, JsonSchema)]
pub struct NftAttribute {
    pub trait_type: String,
    pub value: serde_json::Value,
}

#[allow(dead_code)]
#[derive(Debug, Serialize, JsonSchema)]
pub struct NftSessionMetadata {
    pub name: String,
    pub description: String,
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub external_url: String,
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub image: String,
    pub attributes: Vec<NftAttribute>,
}

#[allow(dead_code)]
#[derive(Debug, Serialize, JsonSchema)]
pub struct NftCertificateMetadata {
    pub name: String,
    pub description: String,
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub external_url: String,
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub image: String,
    pub attributes: Vec<NftAttribute>,
}

#[allow(dead_code)]
#[derive(Debug, Serialize, JsonSchema)]
pub struct NftSubmitterMetadata {
    pub name: String,
    pub description: String,
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub external_url: String,
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub image: String,
    pub attributes: Vec<NftAttribute>,
}
