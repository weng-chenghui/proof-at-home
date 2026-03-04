use anyhow::{Context, Result};
use std::path::Path;

const TEMPLATE_HTML: &str = include_str!("template.html");

/// Extract a JSON object from an LLM response that may contain markdown fences or preamble.
pub fn extract_json(response: &str) -> Result<String> {
    let trimmed = response.trim();

    // Try to find JSON inside markdown code fences
    if let Some(start) = trimmed.find("```json") {
        let after = &trimmed[start + 7..];
        if let Some(end) = after.find("```") {
            let json_str = after[..end].trim();
            serde_json::from_str::<serde_json::Value>(json_str)
                .context("JSON inside code fence is not valid")?;
            return Ok(json_str.to_string());
        }
    }

    // Try to find JSON inside generic code fences
    if let Some(start) = trimmed.find("```") {
        let after = &trimmed[start + 3..];
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

/// Generate a standalone HTML visualization file from JSON visualization data.
pub fn generate_html(viz_json: &str, output_path: &Path) -> Result<()> {
    let data: serde_json::Value =
        serde_json::from_str(viz_json).context("Invalid visualization JSON")?;

    let title = data
        .get("title")
        .and_then(|v| v.as_str())
        .unwrap_or("Conjecture Visualization");
    let domain = data
        .get("domain")
        .and_then(|v| v.as_str())
        .unwrap_or("mathematics");

    let html = TEMPLATE_HTML
        .replace("{{TITLE}}", &html_escape(title))
        .replace("{{DOMAIN}}", &html_escape(domain))
        .replace("{{VIZ_JSON}}", viz_json);

    std::fs::write(output_path, html)
        .with_context(|| format!("Failed to write HTML to {}", output_path.display()))?;

    Ok(())
}

/// Build a visualization HTML file from an LLM response.
/// Returns the cleaned JSON string.
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
        let input =
            r#"{"title": "test", "domain": "algebra", "summary": "s", "visualizations": []}"#;
        let result = extract_json(input).unwrap();
        assert!(result.contains("\"title\""));
        assert!(result.contains("\"domain\""));
    }

    #[test]
    fn test_extract_json_with_fences() {
        let input = "Here:\n```json\n{\"title\": \"test\", \"visualizations\": []}\n```\n";
        let result = extract_json(input).unwrap();
        assert!(result.contains("\"title\""));
    }

    #[test]
    fn test_extract_json_with_preamble() {
        let input = "I analyzed the conjecture:\n{\"title\": \"test\", \"visualizations\": []}";
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
        let json = r#"{"title":"Test Viz","domain":"algebra","summary":"A test","visualizations":[{"type":"table","title":"Op Table","description":"desc","data":{"headers":["a","b"],"rows":[["1","2"]]}}]}"#;
        let dir = std::env::temp_dir();
        let path = dir.join("test_conjecture_viz.html");
        generate_html(json, &path).unwrap();
        let content = std::fs::read_to_string(&path).unwrap();
        assert!(content.contains("Test Viz"));
        assert!(content.contains("algebra"));
        assert!(content.contains("d3"));
        std::fs::remove_file(&path).ok();
    }

    #[test]
    fn test_html_escape() {
        assert_eq!(html_escape("<b>hi</b>"), "&lt;b&gt;hi&lt;/b&gt;");
        assert_eq!(html_escape("a & b"), "a &amp; b");
        assert_eq!(html_escape("\"quote\""), "&quot;quote&quot;");
    }

    #[test]
    fn test_build_from_response() {
        let response = r#"{"title":"T","domain":"d","summary":"s","visualizations":[]}"#;
        let dir = std::env::temp_dir();
        let path = dir.join("test_build_viz.html");
        let json = build_from_response(response, &path).unwrap();
        assert!(json.contains("\"title\""));
        let content = std::fs::read_to_string(&path).unwrap();
        assert!(content.contains("<html"));
        std::fs::remove_file(&path).ok();
    }
}
