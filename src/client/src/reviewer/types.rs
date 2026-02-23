use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct ReviewState {
    pub review_id: String,
    pub reviewer_username: String,
    pub created_at: String,
    pub packages: Vec<CertificatePackage>,
    pub status: ReviewStatus,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, JsonSchema)]
pub enum ReviewStatus {
    Open,
    Compared,
    Sealed,
}

impl std::fmt::Display for ReviewStatus {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ReviewStatus::Open => write!(f, "open"),
            ReviewStatus::Compared => write!(f, "compared"),
            ReviewStatus::Sealed => write!(f, "sealed"),
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct CertificatePackage {
    pub prover_contribution_id: String,
    pub prover_username: String,
    pub prover: String,
    pub conjecture_ids: Vec<String>,
    pub archive_sha256: String,
    pub import_source: String,
}

/// Per-conjecture comparison of proofs from different provers
#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct ConjectureComparison {
    pub conjecture_id: String,
    pub conjecture_title: String,
    pub rankings: Vec<CertificateRanking>,
    pub analysis: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct CertificateRanking {
    pub prover_contribution_id: String,
    pub prover_username: String,
    pub scores: CertificateScores,
    pub reasoning: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, Default, JsonSchema)]
pub struct CertificateScores {
    pub succinctness: u8,
    pub library_reuse: u8,
    pub generality: u8,
    pub modularity: u8,
    pub math_strategy: u8,
    pub overall: u8,
}

impl CertificateScores {
    pub fn average_with(scores: &[&CertificateScores]) -> CertificateScores {
        if scores.is_empty() {
            return CertificateScores::default();
        }
        let n = scores.len() as f64;
        CertificateScores {
            succinctness: (scores.iter().map(|s| s.succinctness as f64).sum::<f64>() / n).round()
                as u8,
            library_reuse: (scores.iter().map(|s| s.library_reuse as f64).sum::<f64>() / n).round()
                as u8,
            generality: (scores.iter().map(|s| s.generality as f64).sum::<f64>() / n).round() as u8,
            modularity: (scores.iter().map(|s| s.modularity as f64).sum::<f64>() / n).round() as u8,
            math_strategy: (scores.iter().map(|s| s.math_strategy as f64).sum::<f64>() / n).round()
                as u8,
            overall: (scores.iter().map(|s| s.overall as f64).sum::<f64>() / n).round() as u8,
        }
    }
}

/// Package-level rollup
#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct PackageRanking {
    pub prover_contribution_id: String,
    pub prover_username: String,
    pub avg_scores: CertificateScores,
    pub conjectures_compared: u32,
    pub rank: u32,
    pub summary: String,
}

/// Full comparison result
#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct ComparisonResult {
    pub timestamp: String,
    pub model: String,
    pub cost_usd: f64,
    pub conjecture_comparisons: Vec<ConjectureComparison>,
    pub package_rankings: Vec<PackageRanking>,
}

/// Parsed review report from TOML
#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct ReviewReport {
    pub reviewer: ReviewerInfo,
    pub summary: ReportSummary,
    pub package_reviews: Vec<PackageReview>,
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct ReviewerInfo {
    pub username: String,
    pub date: String,
    pub review_id: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct ReportSummary {
    pub overall_assessment: String,
    pub recommendation: String,
    pub confidence: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct PackageReview {
    pub prover_contribution_id: String,
    pub prover_username: String,
    pub rank: u32,
    pub strengths: String,
    pub weaknesses: String,
    #[serde(default)]
    pub notes: String,
}
