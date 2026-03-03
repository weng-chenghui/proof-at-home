use anyhow::{Context, Result};
use async_trait::async_trait;
use serde::Deserialize;

use super::types::*;
use super::AiProvider;

/// Ollama local provider. Cost is always $0.00 since models run locally.
pub struct OllamaProvider {
    api_base_url: String,
}

impl OllamaProvider {
    pub fn new(api_base_url: String) -> Self {
        let api_base_url = if api_base_url.is_empty() {
            "http://localhost:11434".to_string()
        } else {
            api_base_url.trim_end_matches('/').to_string()
        };
        Self { api_base_url }
    }
}

#[async_trait]
impl AiProvider for OllamaProvider {
    fn name(&self) -> &str {
        "ollama"
    }

    async fn complete(&self, prompt: &str, model: &str, max_tokens: u32) -> Result<AiResponse> {
        let client = reqwest::Client::new();
        // Ollama exposes an OpenAI-compatible chat endpoint
        let url = format!("{}/v1/chat/completions", self.api_base_url);
        let body = serde_json::json!({
            "model": model,
            "max_tokens": max_tokens,
            "messages": [
                {"role": "user", "content": prompt}
            ],
            "stream": false,
        });

        let resp = client
            .post(&url)
            .header("Content-Type", "application/json")
            .json(&body)
            .send()
            .await
            .context("Failed to call Ollama API. Is Ollama running?")?;

        if !resp.status().is_success() {
            let status = resp.status();
            let body = resp.text().await.unwrap_or_default();
            anyhow::bail!("Ollama API error ({}): {}", status, body);
        }

        let api_resp: OllamaChatResponse = resp
            .json()
            .await
            .context("Failed to parse Ollama response")?;

        let text = api_resp
            .choices
            .first()
            .map(|c| c.message.content.clone())
            .unwrap_or_default();

        let input_tokens = api_resp
            .usage
            .as_ref()
            .map(|u| u.prompt_tokens)
            .unwrap_or(0);
        let output_tokens = api_resp
            .usage
            .as_ref()
            .map(|u| u.completion_tokens)
            .unwrap_or(0);

        Ok(AiResponse {
            text,
            cost_usd: 0.0, // local models are free
            model: api_resp.model.unwrap_or_else(|| model.to_string()),
            usage: AiUsage {
                input_tokens,
                output_tokens,
            },
        })
    }

    async fn query_quota(&self) -> Result<QuotaInfo> {
        Ok(QuotaInfo {
            remaining_usd: None,
            remaining_requests: None,
            monthly_spend_usd: None,
            description: "Local (unlimited)".into(),
        })
    }
}

// ── Ollama response structs (OpenAI-compatible format) ──

#[derive(Deserialize)]
struct OllamaChatResponse {
    #[serde(default)]
    model: Option<String>,
    #[serde(default)]
    choices: Vec<OllamaChoice>,
    #[serde(default)]
    usage: Option<OllamaUsage>,
}

#[derive(Deserialize)]
struct OllamaChoice {
    message: OllamaMessage,
}

#[derive(Deserialize)]
struct OllamaMessage {
    #[serde(default)]
    content: String,
}

#[derive(Deserialize, Default)]
struct OllamaUsage {
    #[serde(default)]
    prompt_tokens: u64,
    #[serde(default)]
    completion_tokens: u64,
}
