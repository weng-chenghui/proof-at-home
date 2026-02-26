use schemars::schema_for;
use std::fs;
use std::path::Path;

// Re-use types from the main crate
use proof_at_home::certifier::types::{CertificationReport, CertificationState, ComparisonResult};
use proof_at_home::nft::metadata::{
    CertificateInfo, ConjectureSubmitterInfo, ContributionInfo, NftCertificateMetadata,
    NftSessionMetadata, NftSubmitterMetadata,
};
use proof_at_home::server_client::api::{Certificate, Conjecture, Contribution, Proof};

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
    write_schema::<CertificateInfo>(out_dir, "certificate-nft-metadata.schema.json");
    write_schema::<NftSessionMetadata>(out_dir, "nft-session-output.schema.json");
    write_schema::<NftCertificateMetadata>(out_dir, "nft-certificate-output.schema.json");
    write_schema::<Conjecture>(out_dir, "conjecture.schema.json");
    write_schema::<Contribution>(out_dir, "contribution-summary.schema.json");
    write_schema::<CertificationState>(out_dir, "certification-state.schema.json");
    write_schema::<ComparisonResult>(out_dir, "ai-comparison.schema.json");
    write_schema::<Certificate>(out_dir, "certificate-summary.schema.json");
    write_schema::<CertificationReport>(out_dir, "certification-report.schema.json");
    write_schema::<Proof>(out_dir, "contribution-result.schema.json");
    write_schema::<ConjectureSubmitterInfo>(out_dir, "submitter-nft-metadata.schema.json");
    write_schema::<NftSubmitterMetadata>(out_dir, "nft-submitter-output.schema.json");

    println!("\nDone. {} schemas written to {}", 13, out_dir.display());
}
