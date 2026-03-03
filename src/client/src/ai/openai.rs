use anyhow::{Context, Result};
use async_trait::async_trait;
use serde::Deserialize;

use super::types::*;
use super::AiProvider;

/// OpenAI-compatible provider (works with OpenAI, Azure OpenAI, and compatible APIs).
pub struct OpenAiProvider {
    api_key: String,
    api_base_url: String,
}

impl OpenAiProvider {
    pub fn new(api_key: String, api_base_url: String) -> Self {
        let api_base_url = if api_base_url.is_empty() {
            "https://api.openai.com".to_string()
        } else {
            api_base_url.trim_end_matches('/').to_string()
        };
        Self {
            api_key,
            api_base_url,
        }
    }
}

#[async_trait]
impl AiProvider for OpenAiProvider {
    fn name(&self) -> &str {
        "openai"
    }

    async fn complete(&self, prompt: &str, model: &str, max_tokens: u32) -> Result<AiResponse> {
        let client = reqwest::Client::new();
        let url = format!("{}/v1/chat/completions", self.api_base_url);
        let body = serde_json::json!({
            "model": model,
            "max_tokens": max_tokens,
            "messages": [
                {"role": "user", "content": prompt}
            ]
        });

        let resp = client
            .post(&url)
            .header("Authorization", format!("Bearer {}", self.api_key))
            .header("Content-Type", "application/json")
            .json(&body)
            .send()
            .await
            .context("Failed to call OpenAI API")?;

        if !resp.status().is_success() {
            let status = resp.status();
            let body = resp.text().await.unwrap_or_default();
            anyhow::bail!("OpenAI API error ({}): {}", status, body);
        }

        let api_resp: ChatCompletionResponse = resp
            .json()
            .await
            .context("Failed to parse OpenAI response")?;

        let text = api_resp
            .choices
            .first()
            .map(|c| c.message.content.clone())
            .unwrap_or_default();

        let actual_model = api_resp.model;
        let input_tokens = api_resp.usage.prompt_tokens;
        let output_tokens = api_resp.usage.completion_tokens;

        let cost = estimate_cost(
            OPENAI_PRICING,
            &actual_model,
            input_tokens,
            output_tokens,
            2.50, // default to gpt-4o input pricing
            10.0, // default to gpt-4o output pricing
        );

        Ok(AiResponse {
            text,
            cost_usd: cost,
            model: actual_model,
            usage: AiUsage {
                input_tokens,
                output_tokens,
            },
        })
    }

    async fn query_quota(&self) -> Result<QuotaInfo> {
        // Try the billing/credit_grants endpoint (may not be available on all accounts)
        let client = reqwest::Client::new();
        let url = format!("{}/v1/dashboard/billing/credit_grants", self.api_base_url);

        let resp = client
            .get(&url)
            .header("Authorization", format!("Bearer {}", self.api_key))
            .send()
            .await;

        match resp {
            Ok(r) if r.status().is_success() => {
                let body: serde_json::Value = r.json().await.unwrap_or_default();
                let remaining = body.get("total_available").and_then(|v| v.as_f64());
                Ok(QuotaInfo {
                    remaining_usd: remaining,
                    remaining_requests: None,
                    monthly_spend_usd: None,
                    description: format!(
                        "Remaining credits: ${}",
                        remaining
                            .map(|r| format!("{:.2}", r))
                            .unwrap_or_else(|| "unknown".into())
                    ),
                })
            }
            _ => Ok(QuotaInfo {
                remaining_usd: None,
                remaining_requests: None,
                monthly_spend_usd: None,
                description:
                    "Could not query OpenAI billing. Visit platform.openai.com to check usage."
                        .into(),
            }),
        }
    }
}

// ── OpenAI response structs ──

#[derive(Deserialize)]
struct ChatCompletionResponse {
    model: String,
    choices: Vec<ChatChoice>,
    usage: ChatUsage,
}

#[derive(Deserialize)]
struct ChatChoice {
    message: ChatMessage,
}

#[derive(Deserialize)]
struct ChatMessage {
    #[serde(default)]
    content: String,
}

#[derive(Deserialize)]
struct ChatUsage {
    prompt_tokens: u64,
    completion_tokens: u64,
}
