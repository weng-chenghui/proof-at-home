use anyhow::{Context, Result};
use serde::Deserialize;
use std::collections::HashMap;

/// A declarative agent pipeline definition.
#[derive(Debug, Clone, Deserialize)]
#[allow(dead_code)]
pub struct PipelineDefinition {
    pub name: String,
    #[serde(default)]
    pub version: Option<String>,
    #[serde(default)]
    pub author: Option<String>,
    pub description: String,
    #[serde(default = "default_agent_id")]
    pub agent_id: String,
    #[serde(default)]
    pub budget_usd: Option<f64>,
    pub steps: Vec<PipelineStep>,
}

fn default_agent_id() -> String {
    "lesson-agent".to_string()
}

/// A single step in a pipeline.
#[derive(Debug, Clone, Deserialize)]
#[allow(dead_code)]
pub struct PipelineStep {
    pub name: String,
    pub strategy: String,
    #[serde(default)]
    pub max_iterations: Option<u32>,
    #[serde(default)]
    pub stop_condition: Option<StopCondition>,
    #[serde(default)]
    pub variables: HashMap<String, String>,
    #[serde(default)]
    pub tags: Vec<String>,
}

/// Condition to stop an iterative step early.
#[derive(Debug, Clone, Deserialize)]
pub struct StopCondition {
    pub json_field: String,
    pub operator: String,
    pub value: f64,
}

impl StopCondition {
    /// Evaluate the stop condition against a JSON value.
    pub fn evaluate(&self, json: &serde_json::Value) -> bool {
        let actual = json
            .get(&self.json_field)
            .and_then(|v| v.as_f64())
            .unwrap_or(0.0);

        match self.operator.as_str() {
            ">=" => actual >= self.value,
            "<=" => actual <= self.value,
            "==" => (actual - self.value).abs() < f64::EPSILON,
            ">" => actual > self.value,
            "<" => actual < self.value,
            "!=" => (actual - self.value).abs() >= f64::EPSILON,
            _ => false,
        }
    }
}

/// Load a pipeline from a file path, URL, or builtin name.
pub fn load_pipeline(path_or_name: &str) -> Result<PipelineDefinition> {
    // Try builtin names first
    match path_or_name {
        "lesson-default" => {
            let toml_str = include_str!("builtins/lesson-default.toml");
            let pipeline: PipelineDefinition = toml::from_str(toml_str)
                .context("Failed to parse builtin lesson-default pipeline")?;
            return Ok(pipeline);
        }
        "series-default" => {
            let toml_str = include_str!("builtins/series-default.toml");
            let pipeline: PipelineDefinition = toml::from_str(toml_str)
                .context("Failed to parse builtin series-default pipeline")?;
            return Ok(pipeline);
        }
        _ => {}
    }

    // Try as file path
    let path = std::path::Path::new(path_or_name);
    if path.exists() {
        let content = std::fs::read_to_string(path)
            .with_context(|| format!("Failed to read pipeline file: {}", path.display()))?;
        let pipeline: PipelineDefinition =
            toml::from_str(&content).context("Failed to parse pipeline TOML")?;
        return Ok(pipeline);
    }

    anyhow::bail!(
        "Pipeline '{}' not found. Use a builtin name (lesson-default, series-default) or a file path.",
        path_or_name
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_load_builtin_lesson_pipeline() {
        let pipeline = load_pipeline("lesson-default").unwrap();
        assert_eq!(pipeline.name, "lesson-default");
        assert!(!pipeline.steps.is_empty());
    }

    #[test]
    fn test_load_builtin_series_pipeline() {
        let pipeline = load_pipeline("series-default").unwrap();
        assert_eq!(pipeline.name, "series-default");
        assert!(!pipeline.steps.is_empty());
    }

    #[test]
    fn test_load_nonexistent_pipeline() {
        assert!(load_pipeline("nonexistent-pipeline").is_err());
    }

    #[test]
    fn test_stop_condition_gte() {
        let cond = StopCondition {
            json_field: "score".to_string(),
            operator: ">=".to_string(),
            value: 7.0,
        };
        let json = serde_json::json!({"score": 8});
        assert!(cond.evaluate(&json));

        let json2 = serde_json::json!({"score": 6});
        assert!(!cond.evaluate(&json2));
    }

    #[test]
    fn test_stop_condition_eq() {
        let cond = StopCondition {
            json_field: "score".to_string(),
            operator: "==".to_string(),
            value: 7.0,
        };
        let json = serde_json::json!({"score": 7});
        assert!(cond.evaluate(&json));
    }

    #[test]
    fn test_stop_condition_missing_field() {
        let cond = StopCondition {
            json_field: "score".to_string(),
            operator: ">=".to_string(),
            value: 7.0,
        };
        let json = serde_json::json!({"other": 10});
        assert!(!cond.evaluate(&json));
    }

    #[test]
    fn test_deserialize_pipeline_toml() {
        let toml_str = r#"
name = "test-pipeline"
description = "A test pipeline"
agent_id = "test-agent"

[[steps]]
name = "plan"
strategy = "agent-lesson-plan"

[[steps]]
name = "iterate"
strategy = "agent-lesson-iterate"
max_iterations = 2

[steps.stop_condition]
json_field = "score"
operator = ">="
value = 7.0
"#;
        let pipeline: PipelineDefinition = toml::from_str(toml_str).unwrap();
        assert_eq!(pipeline.name, "test-pipeline");
        assert_eq!(pipeline.steps.len(), 2);
        assert_eq!(pipeline.steps[1].max_iterations, Some(2));
        assert!(pipeline.steps[1].stop_condition.is_some());
    }

    #[test]
    fn test_reject_invalid_stop_condition() {
        let toml_str = r#"
name = "bad"
description = "Bad pipeline"

[[steps]]
name = "step1"
strategy = "some-strategy"

[steps.stop_condition]
json_field = "score"
operator = ">="
"#;
        // Missing required 'value' field
        let result: Result<PipelineDefinition, _> = toml::from_str(toml_str);
        assert!(result.is_err());
    }
}
