use schemars::schema_for;
use std::fs;
use std::path::Path;

// Re-use types from the main crate
use proof_at_home::nft::metadata::{
    ContributionInfo, NftReviewMetadata, NftSessionMetadata, ReviewInfo,
};
use proof_at_home::reviewer::types::{ComparisonResult, ReviewReport, ReviewState};
use proof_at_home::server_client::api::{
    Certificate, Conjecture, ContributionSummary, ReviewSummary,
};

fn write_schema<T: schemars::JsonSchema>(dir: &Path, filename: &str) {
    let schema = schema_for!(T);
    let json = serde_json::to_string_pretty(&schema).expect("Failed to serialize schema");
    let path = dir.join(filename);
    fs::write(&path, json).unwrap_or_else(|e| panic!("Failed to write {}: {}", path.display(), e));
    println!("  {}", filename);
}

fn main() {
    let out_dir = Path::new("docs/schemas");
    fs::create_dir_all(out_dir).expect("Failed to create docs/schemas/");

    println!("Generating JSON schemas...\n");

    write_schema::<ContributionInfo>(out_dir, "contribution-nft-metadata.schema.json");
    write_schema::<ReviewInfo>(out_dir, "review-nft-metadata.schema.json");
    write_schema::<NftSessionMetadata>(out_dir, "nft-session-output.schema.json");
    write_schema::<NftReviewMetadata>(out_dir, "nft-review-output.schema.json");
    write_schema::<Conjecture>(out_dir, "conjecture.schema.json");
    write_schema::<ContributionSummary>(out_dir, "contribution-summary.schema.json");
    write_schema::<ReviewState>(out_dir, "review-state.schema.json");
    write_schema::<ComparisonResult>(out_dir, "ai-comparison.schema.json");
    write_schema::<ReviewSummary>(out_dir, "review-summary.schema.json");
    write_schema::<ReviewReport>(out_dir, "review-report.schema.json");
    write_schema::<Certificate>(out_dir, "certificate.schema.json");

    println!("\nDone. {} schemas written to {}", 11, out_dir.display());
}
