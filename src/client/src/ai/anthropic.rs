use anyhow::{Context, Result};
use async_trait::async_trait;
use serde::Deserialize;
use std::process::Command;

use super::types::*;
use super::AiProvider;

/// Anthropic/Claude AI provider.
///
/// Uses the `claude` CLI as the primary path, falling back to the
/// Anthropic HTTP API when the CLI is unavailable or fails.
pub struct AnthropicProvider {
    api_key: String,
    api_base_url: String,
}

impl AnthropicProvider {
    pub fn new(api_key: String, api_base_url: String) -> Self {
        let api_base_url = if api_base_url.is_empty() {
            "https://api.anthropic.com".to_string()
        } else {
            api_base_url.trim_end_matches('/').to_string()
        };
        Self {
            api_key,
            api_base_url,
        }
    }

    /// Check if the `claude` CLI binary is available.
    fn cli_available() -> bool {
        Command::new("claude")
            .arg("--version")
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false)
    }

    /// Try calling the `claude` CLI for a completion.
    fn try_cli(&self, prompt: &str, model: &str, max_tokens: u32) -> Result<AiResponse> {
        let output = Command::new("claude")
            .args([
                "-p",
                prompt,
                "--output-format",
                "json",
                "--max-turns",
                "1",
                "--model",
                model,
            ])
            .output()
            .context("Failed to invoke claude CLI")?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            anyhow::bail!("claude CLI failed: {}", stderr);
        }

        let stdout = String::from_utf8_lossy(&output.stdout);
        let resp: CliResponse =
            serde_json::from_str(&stdout).context("Failed to parse claude CLI JSON output")?;

        let (input_tokens, output_tokens) = resp
            .usage
            .as_ref()
            .map(|u| (u.input_tokens, u.output_tokens))
            .unwrap_or((0, 0));

        let actual_model = resp.model.as_deref().unwrap_or(model);

        let cost = resp.cost_usd.unwrap_or_else(|| {
            estimate_cost(
                ANTHROPIC_PRICING,
                actual_model,
                input_tokens,
                output_tokens,
                3.0,
                15.0,
            )
        });

        let _ = max_tokens; // CLI handles max_tokens internally

        Ok(AiResponse {
            text: resp.result,
            cost_usd: cost,
            model: actual_model.to_string(),
            usage: AiUsage {
                input_tokens,
                output_tokens,
            },
        })
    }

    /// Fallback: call the Anthropic HTTP API directly.
    async fn try_api(&self, prompt: &str, model: &str, max_tokens: u32) -> Result<AiResponse> {
        let client = reqwest::Client::new();
        let url = format!("{}/v1/messages", self.api_base_url);
        let body = serde_json::json!({
            "model": model,
            "max_tokens": max_tokens,
            "messages": [
                {"role": "user", "content": prompt}
            ]
        });

        let resp = client
            .post(&url)
            .header("x-api-key", &self.api_key)
            .header("anthropic-version", "2023-06-01")
            .header("content-type", "application/json")
            .json(&body)
            .send()
            .await
            .context("Failed to call Anthropic API")?;

        if !resp.status().is_success() {
            let status = resp.status();
            let body = resp.text().await.unwrap_or_default();
            anyhow::bail!("Anthropic API error ({}): {}", status, body);
        }

        let api_resp: ApiResponse = resp.json().await.context("Failed to parse API response")?;
        let text = api_resp
            .content
            .first()
            .map(|b| b.text.clone())
            .unwrap_or_default();

        let cost = estimate_cost(
            ANTHROPIC_PRICING,
            &api_resp.model,
            api_resp.usage.input_tokens,
            api_resp.usage.output_tokens,
            3.0,
            15.0,
        );

        Ok(AiResponse {
            text,
            cost_usd: cost,
            model: api_resp.model,
            usage: AiUsage {
                input_tokens: api_resp.usage.input_tokens,
                output_tokens: api_resp.usage.output_tokens,
            },
        })
    }
}

#[async_trait]
impl AiProvider for AnthropicProvider {
    fn name(&self) -> &str {
        "anthropic"
    }

    async fn complete(&self, prompt: &str, model: &str, max_tokens: u32) -> Result<AiResponse> {
        if Self::cli_available() {
            if let Ok(r) = self.try_cli(prompt, model, max_tokens) {
                return Ok(r);
            }
        }
        self.try_api(prompt, model, max_tokens).await
    }

    async fn query_quota(&self) -> Result<QuotaInfo> {
        // Anthropic quota query requires an admin API key (sk-ant-admin...).
        // Regular keys cannot query billing programmatically.
        if self.api_key.starts_with("sk-ant-admin") {
            let client = reqwest::Client::new();
            let url = format!("{}/v1/organizations/cost_report", self.api_base_url);
            let resp = client
                .get(&url)
                .header("x-api-key", &self.api_key)
                .header("anthropic-version", "2023-06-01")
                .send()
                .await;

            match resp {
                Ok(r) if r.status().is_success() => {
                    let body: serde_json::Value = r.json().await.unwrap_or_default();
                    let spend = body.get("monthly_cost_usd").and_then(|v| v.as_f64());
                    Ok(QuotaInfo {
                        remaining_usd: None,
                        remaining_requests: None,
                        monthly_spend_usd: spend,
                        description: format!(
                            "Monthly spend: ${}",
                            spend
                                .map(|s| format!("{:.2}", s))
                                .unwrap_or_else(|| "unknown".into())
                        ),
                    })
                }
                _ => Ok(QuotaInfo {
                    remaining_usd: None,
                    remaining_requests: None,
                    monthly_spend_usd: None,
                    description: "Failed to query Anthropic cost report. Check your admin API key."
                        .into(),
                }),
            }
        } else {
            Ok(QuotaInfo {
                remaining_usd: None,
                remaining_requests: None,
                monthly_spend_usd: None,
                description: "Quota query requires an Admin API key (sk-ant-admin...). Visit console.anthropic.com to check usage.".into(),
            })
        }
    }
}

// ── Deserialization structs ──

#[derive(Deserialize, Default)]
struct CliResponse {
    #[serde(default)]
    result: String,
    #[serde(default)]
    cost_usd: Option<f64>,
    #[serde(default)]
    usage: Option<CliUsage>,
    #[serde(default)]
    model: Option<String>,
}

#[derive(Deserialize, Default)]
struct CliUsage {
    #[serde(default)]
    input_tokens: u64,
    #[serde(default)]
    output_tokens: u64,
}

#[derive(Deserialize)]
struct ApiResponse {
    content: Vec<ApiContentBlock>,
    usage: ApiUsage,
    model: String,
}

#[derive(Deserialize)]
struct ApiContentBlock {
    #[serde(default)]
    text: String,
}

#[derive(Deserialize)]
struct ApiUsage {
    input_tokens: u64,
    output_tokens: u64,
}
