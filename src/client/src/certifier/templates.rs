use anyhow::{Context, Result};
use std::path::Path;

use crate::certifier::types::*;

/// Generate a certification report TOML template, pre-filled with session info and optional AI rankings
pub fn get_template(
    variant: &str,
    session: &CertificationState,
    comparison: Option<&ComparisonResult>,
) -> String {
    match variant {
        "minimal" => build_minimal_template(session, comparison),
        "detailed" => build_detailed_template(session, comparison),
        _ => build_default_template(session, comparison),
    }
}

fn build_default_template(
    session: &CertificationState,
    comparison: Option<&ComparisonResult>,
) -> String {
    let mut out = String::from(
        "# Proof@Home Certification Report\n\
         # Fill in the fields below. Fields marked [required] must be completed before sealing.\n\n",
    );

    out.push_str(&format!(
        "[certifier]\n\
         username = \"{}\"          # [required] Your username\n\
         date = \"{}\"              # [auto-filled]\n\
         certification_id = \"{}\"         # [auto-filled]\n\n",
        session.certifier_username, session.created_at, session.certification_id,
    ));

    out.push_str(
        "[summary]\n\
         overall_assessment = \"\"  # [required] 2-5 sentence overall assessment\n\
         recommendation = \"\"      # [required] One of: \"accept-all\", \"accept-top-N\", \"revise\", \"reject\"\n\
         confidence = \"\"          # [required] One of: \"high\", \"medium\", \"low\"\n\n",
    );

    // Package assessments — pre-fill with AI rankings if available
    for pkg in &session.packages {
        let (rank, strengths, weaknesses) = if let Some(comp) = comparison {
            let pr = comp
                .package_rankings
                .iter()
                .find(|r| r.contributor_contribution_id == pkg.contributor_contribution_id);
            match pr {
                Some(r) => (r.rank, r.summary.clone(), String::new()),
                None => (0, String::new(), String::new()),
            }
        } else {
            (0, String::new(), String::new())
        };

        out.push_str(&format!(
            "[[package_assessments]]\n\
             contributor_contribution_id = \"{}\"\n\
             contributor_username = \"{}\"\n\
             rank = {}               # [required] 1 = best\n\
             strengths = \"{}\"      # [required] Key strengths of this proof package\n\
             weaknesses = \"{}\"     # [required] Key weaknesses\n\
             notes = \"\"            # Optional additional notes\n\n",
            pkg.contributor_contribution_id, pkg.contributor_username, rank, strengths, weaknesses,
        ));
    }

    out
}

fn build_minimal_template(
    session: &CertificationState,
    comparison: Option<&ComparisonResult>,
) -> String {
    let mut out = String::from("# Proof@Home Certification Report (Minimal)\n\n");

    out.push_str(&format!(
        "[certifier]\n\
         username = \"{}\"\n\
         date = \"{}\"\n\
         certification_id = \"{}\"\n\n",
        session.certifier_username, session.created_at, session.certification_id,
    ));

    out.push_str(
        "[summary]\n\
         overall_assessment = \"\"\n\
         recommendation = \"\"\n\
         confidence = \"\"\n\n",
    );

    for pkg in &session.packages {
        let rank = comparison
            .and_then(|c| {
                c.package_rankings
                    .iter()
                    .find(|r| r.contributor_contribution_id == pkg.contributor_contribution_id)
            })
            .map(|r| r.rank)
            .unwrap_or(0);

        out.push_str(&format!(
            "[[package_assessments]]\n\
             contributor_contribution_id = \"{}\"\n\
             contributor_username = \"{}\"\n\
             rank = {}\n\
             strengths = \"\"\n\
             weaknesses = \"\"\n\
             notes = \"\"\n\n",
            pkg.contributor_contribution_id, pkg.contributor_username, rank,
        ));
    }

    out
}

fn build_detailed_template(
    session: &CertificationState,
    comparison: Option<&ComparisonResult>,
) -> String {
    let mut out = build_default_template(session, comparison);

    // Add per-conjecture commentary sections
    if let Some(comp) = comparison {
        out.push_str("# ── Per-conjecture commentary ──\n\n");
        for pc in &comp.conjecture_comparisons {
            out.push_str(&format!(
                "# Conjecture: {} ({})\n\
                 # AI analysis: {}\n",
                pc.conjecture_title, pc.conjecture_id, pc.analysis,
            ));
            for r in &pc.rankings {
                out.push_str(&format!(
                    "#   {} — overall: {}, reasoning: {}\n",
                    r.contributor_username, r.scores.overall, r.reasoning,
                ));
            }
            out.push_str(&format!(
                "# [[conjecture_commentary]]\n\
                 # conjecture_id = \"{}\"\n\
                 # your_notes = \"\"\n\n",
                pc.conjecture_id,
            ));
        }
    }

    out
}

/// Validate a certification report TOML file. Returns a list of validation errors (empty = valid).
pub fn validate_report(report_path: &Path) -> Result<Vec<String>> {
    let content = std::fs::read_to_string(report_path)
        .with_context(|| format!("Failed to read {}", report_path.display()))?;

    let report: CertificationReport =
        toml::from_str(&content).context("Failed to parse certification_report.toml")?;

    let mut errors = Vec::new();

    if report.certifier.username.is_empty() {
        errors.push("certifier.username is required".into());
    }

    if report.summary.overall_assessment.is_empty() {
        errors.push("summary.overall_assessment is required".into());
    }

    let valid_recommendations = ["accept-all", "accept-top-N", "revise", "reject"];
    if !valid_recommendations.contains(&report.summary.recommendation.as_str()) {
        errors.push(format!(
            "summary.recommendation must be one of: {}",
            valid_recommendations.join(", ")
        ));
    }

    let valid_confidences = ["high", "medium", "low"];
    if !valid_confidences.contains(&report.summary.confidence.as_str()) {
        errors.push(format!(
            "summary.confidence must be one of: {}",
            valid_confidences.join(", ")
        ));
    }

    for (i, pr) in report.package_assessments.iter().enumerate() {
        if pr.contributor_contribution_id.is_empty() {
            errors.push(format!(
                "package_assessments[{}].contributor_contribution_id is required",
                i
            ));
        }
        if pr.rank == 0 {
            errors.push(format!("package_assessments[{}].rank must be > 0", i));
        }
        if pr.strengths.is_empty() {
            errors.push(format!("package_assessments[{}].strengths is required", i));
        }
        if pr.weaknesses.is_empty() {
            errors.push(format!("package_assessments[{}].weaknesses is required", i));
        }
    }

    Ok(errors)
}

/// Parse a certification report TOML file into a CertificationReport struct
pub fn parse_report(report_path: &Path) -> Result<CertificationReport> {
    let content = std::fs::read_to_string(report_path)
        .with_context(|| format!("Failed to read {}", report_path.display()))?;
    let report: CertificationReport =
        toml::from_str(&content).context("Failed to parse certification_report.toml")?;
    Ok(report)
}
