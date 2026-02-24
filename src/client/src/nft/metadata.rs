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
    pub proof_status: String,
    pub git_commit: String,
    pub git_repository: String,
    pub public_key: String,
    pub commit_signature: String,
}

/// Generate OpenSea-compatible NFT metadata JSON for a proof contribution
pub fn generate_nft_metadata(info: &ContributionInfo) -> Value {
    let date = Utc::now().format("%Y-%m-%d").to_string();

    json!({
        "name": format!("Proof@Home Contribution — {} — {}", info.username, date),
        "description": "Formally verified mathematical proofs for the public domain.",
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
                "trait_type": "Proof Status",
                "value": info.proof_status
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

// ── Certificate NFT metadata ──

#[derive(Debug, Serialize, JsonSchema)]
pub struct CertificateInfo {
    pub certifier_username: String,
    pub certificate_id: String,
    pub packages_certified: u32,
    pub conjectures_compared: u32,
    pub top_prover: String,
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
                "trait_type": "Top Prover",
                "value": info.top_prover
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
