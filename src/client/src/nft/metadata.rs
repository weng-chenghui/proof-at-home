use chrono::Utc;
use serde_json::{json, Value};

pub struct SessionInfo {
    pub username: String,
    pub problems_proved: u32,
    pub problems_attempted: u32,
    pub cost_donated_usd: f64,
    pub proof_assistant: String,
    pub archive_sha256: String,
}

/// Generate OpenSea-compatible NFT metadata JSON for a prover session
pub fn generate_nft_metadata(info: &SessionInfo) -> Value {
    let date = Utc::now().format("%Y-%m-%d").to_string();

    json!({
        "name": format!("Proof@Home Session — {} — {}", info.username, date),
        "description": "Contribution record: formally verified mathematical lemmas for the public domain.",
        "attributes": [
            {
                "trait_type": "Username",
                "value": info.username
            },
            {
                "trait_type": "Problems Proved",
                "value": info.problems_proved
            },
            {
                "trait_type": "Problems Attempted",
                "value": info.problems_attempted
            },
            {
                "trait_type": "Cost Donated (USD)",
                "value": format!("{:.2}", info.cost_donated_usd)
            },
            {
                "trait_type": "Proof Assistant",
                "value": info.proof_assistant
            },
            {
                "trait_type": "Archive SHA-256",
                "value": info.archive_sha256
            }
        ]
    })
}

// ── Review NFT metadata ──

pub struct ReviewInfo {
    pub reviewer_username: String,
    pub review_id: String,
    pub packages_reviewed: u32,
    pub problems_compared: u32,
    pub top_prover: String,
    pub recommendation: String,
    pub archive_sha256: String,
    pub ai_comparison_cost_usd: f64,
}

/// Generate OpenSea-compatible NFT metadata JSON for a review
pub fn generate_review_nft_metadata(info: &ReviewInfo) -> Value {
    let date = Utc::now().format("%Y-%m-%d").to_string();

    json!({
        "name": format!("Proof@Home Review — {} — {}", info.reviewer_username, date),
        "description": "Review record: human evaluation of formally verified proofs.",
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
                "trait_type": "Problems Compared",
                "value": info.problems_compared
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
                "trait_type": "AI Comparison Cost (USD)",
                "value": format!("{:.4}", info.ai_comparison_cost_usd)
            }
        ]
    })
}
