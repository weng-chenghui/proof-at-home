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
    pub prover: String,
    pub prover_version: String,
    pub archive_sha256: String,
    pub proof_status: String,
    pub public_key: String,
    pub archive_signature: String,
}

/// Generate OpenSea-compatible NFT metadata JSON for a proof contribution
pub fn generate_nft_metadata(info: &ContributionInfo) -> Value {
    let date = Utc::now().format("%Y-%m-%d").to_string();

    json!({
        "name": format!("Proof@Home Contribution — {} — {}", info.username, date),
        "description": "Contribution record: formally verified mathematical lemmas for the public domain.",
        "external_url": "",
        "image": "",
        "attributes": [
            {
                "trait_type": "Username",
                "value": info.username
            },
            {
                "trait_type": "Conjectures Proved",
                "value": info.conjectures_proved
            },
            {
                "trait_type": "Conjectures Attempted",
                "value": info.conjectures_attempted
            },
            {
                "trait_type": "Cost Donated (USD)",
                "value": format!("{:.2}", info.cost_donated_usd)
            },
            {
                "trait_type": "Prover",
                "value": info.prover
            },
            {
                "trait_type": "Prover Version",
                "value": info.prover_version
            },
            {
                "trait_type": "Archive SHA-256",
                "value": info.archive_sha256
            },
            {
                "trait_type": "Public Key",
                "value": info.public_key
            },
            {
                "trait_type": "Archive Signature",
                "value": info.archive_signature
            },
            {
                "trait_type": "Proof Status",
                "value": info.proof_status
            }
        ]
    })
}

// ── Review NFT metadata ──

#[derive(Debug, Serialize, JsonSchema)]
pub struct ReviewInfo {
    pub reviewer_username: String,
    pub review_id: String,
    pub packages_reviewed: u32,
    pub conjectures_compared: u32,
    pub top_prover: String,
    pub recommendation: String,
    pub archive_sha256: String,
    pub ai_comparison_cost_usd: f64,
    pub reviewed_contribution_ids: Vec<String>,
    pub reviewer_public_key: String,
    pub archive_signature: String,
}

/// Generate OpenSea-compatible NFT metadata JSON for a review
pub fn generate_review_nft_metadata(info: &ReviewInfo) -> Value {
    let date = Utc::now().format("%Y-%m-%d").to_string();

    json!({
        "name": format!("Proof@Home Review — {} — {}", info.reviewer_username, date),
        "description": "Review record: human evaluation of formally verified proofs.",
        "external_url": "",
        "image": "",
        "attributes": [
            {
                "trait_type": "Reviewer",
                "value": info.reviewer_username
            },
            {
                "trait_type": "Review ID",
                "value": info.review_id
            },
            {
                "trait_type": "Packages Reviewed",
                "value": info.packages_reviewed
            },
            {
                "trait_type": "Conjectures Compared",
                "value": info.conjectures_compared
            },
            {
                "trait_type": "Top Prover",
                "value": info.top_prover
            },
            {
                "trait_type": "Recommendation",
                "value": info.recommendation
            },
            {
                "trait_type": "Archive SHA-256",
                "value": info.archive_sha256
            },
            {
                "trait_type": "Public Key",
                "value": info.reviewer_public_key
            },
            {
                "trait_type": "Archive Signature",
                "value": info.archive_signature
            },
            {
                "trait_type": "AI Comparison Cost (USD)",
                "value": format!("{:.4}", info.ai_comparison_cost_usd)
            },
            {
                "trait_type": "Reviewed Contribution IDs",
                "value": info.reviewed_contribution_ids.join(", ")
            }
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
pub struct NftReviewMetadata {
    pub name: String,
    pub description: String,
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub external_url: String,
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub image: String,
    pub attributes: Vec<NftAttribute>,
}
