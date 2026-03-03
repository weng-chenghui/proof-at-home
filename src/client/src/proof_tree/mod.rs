use anyhow::{Context, Result};
use std::path::Path;

const TEMPLATE_HTML: &str = include_str!("template.html");

/// Extract a JSON object from an LLM response that may contain markdown fences or preamble.
fn extract_json(response: &str) -> Result<String> {
    let trimmed = response.trim();

    // Try to find JSON inside markdown code fences
    if let Some(start) = trimmed.find("```json") {
        let after = &trimmed[start + 7..];
        if let Some(end) = after.find("```") {
            let json_str = after[..end].trim();
            // Validate it's parseable JSON
            serde_json::from_str::<serde_json::Value>(json_str)
                .context("JSON inside code fence is not valid")?;
            return Ok(json_str.to_string());
        }
    }

    // Try to find JSON inside generic code fences
    if let Some(start) = trimmed.find("```") {
        let after = &trimmed[start + 3..];
        // Skip optional language tag on the same line
        let after = if let Some(nl) = after.find('\n') {
            &after[nl + 1..]
        } else {
            after
        };
        if let Some(end) = after.find("```") {
            let json_str = after[..end].trim();
            if serde_json::from_str::<serde_json::Value>(json_str).is_ok() {
                return Ok(json_str.to_string());
            }
        }
    }

    // Try the raw text as JSON (find first { to last })
    if let Some(start) = trimmed.find('{') {
        if let Some(end) = trimmed.rfind('}') {
            let json_str = &trimmed[start..=end];
            serde_json::from_str::<serde_json::Value>(json_str)
                .context("Could not parse JSON from LLM response")?;
            return Ok(json_str.to_string());
        }
    }

    anyhow::bail!(
        "LLM response does not contain valid JSON.\nResponse preview: {}",
        &trimmed[..trimmed.len().min(200)]
    )
}

/// Generate a standalone HTML proof tree file from a JSON proof tree.
pub fn generate_html(proof_tree_json: &str, output_path: &Path) -> Result<()> {
    // Parse the JSON to extract title and prover for the template
    let tree: serde_json::Value =
        serde_json::from_str(proof_tree_json).context("Invalid proof tree JSON")?;

    let title = tree
        .get("title")
        .and_then(|v| v.as_str())
        .unwrap_or("Proof Tree");
    let prover = tree
        .get("prover")
        .and_then(|v| v.as_str())
        .unwrap_or("unknown");

    let html = TEMPLATE_HTML
        .replace("{{TITLE}}", &html_escape(title))
        .replace("{{PROVER}}", &html_escape(prover))
        .replace("{{PROOF_TREE_JSON}}", proof_tree_json);

    std::fs::write(output_path, html)
        .with_context(|| format!("Failed to write HTML to {}", output_path.display()))?;

    Ok(())
}

/// Build a proof tree HTML file from an LLM response.
/// Returns the cleaned JSON string and the output path.
pub fn build_from_response(response: &str, output_path: &Path) -> Result<String> {
    let json = extract_json(response)?;
    generate_html(&json, output_path)?;
    Ok(json)
}

fn html_escape(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_extract_json_raw() {
        let input = r#"{"title": "test", "root": {}}"#;
        let result = extract_json(input).unwrap();
        assert!(result.contains("\"title\""));
    }

    #[test]
    fn test_extract_json_with_fences() {
        let input = "Here is the tree:\n```json\n{\"title\": \"test\", \"root\": {}}\n```\n";
        let result = extract_json(input).unwrap();
        assert!(result.contains("\"title\""));
    }

    #[test]
    fn test_extract_json_with_preamble() {
        let input = "I analyzed the proof. Here is the JSON:\n{\"title\": \"test\", \"root\": {}}";
        let result = extract_json(input).unwrap();
        assert!(result.contains("\"title\""));
    }

    #[test]
    fn test_extract_json_invalid() {
        let input = "This is not JSON at all.";
        assert!(extract_json(input).is_err());
    }

    #[test]
    fn test_generate_html() {
        let json = r#"{"title":"Test Proof","prover":"rocq","root":{"id":"n0","tactic":"Goal","goal_before":"\\forall n, n = n","goal_after":"","annotation":"Initial goal","children":[]}}"#;
        let dir = std::env::temp_dir();
        let path = dir.join("test_proof_tree.html");
        generate_html(json, &path).unwrap();
        let content = std::fs::read_to_string(&path).unwrap();
        assert!(content.contains("Test Proof"));
        assert!(content.contains("rocq"));
        assert!(content.contains("d3.hierarchy"));
        std::fs::remove_file(&path).ok();
    }
}
