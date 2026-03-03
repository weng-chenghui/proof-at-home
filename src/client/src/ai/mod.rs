//! Multi-provider AI service abstraction.
//!
//! Provides a common `AiProvider` trait so the rest of the codebase can call
//! AI completions without knowing which backend (Anthropic, OpenAI, Ollama, etc.)
//! is in use.

pub mod anthropic;
pub mod ollama;
pub mod openai;
pub mod types;

#[cfg(test)]
pub mod mock;

use anyhow::Result;
use async_trait::async_trait;

pub use types::{AiResponse, QuotaInfo};

use crate::config::Config;

/// Trait implemented by each AI provider backend.
#[async_trait]
pub trait AiProvider: Send + Sync {
    /// Provider name (e.g. "anthropic", "openai", "ollama").
    fn name(&self) -> &str;

    /// Send a completion request and return the response.
    async fn complete(&self, prompt: &str, model: &str, max_tokens: u32) -> Result<AiResponse>;

    /// Query remaining quota/credits from the provider.
    async fn query_quota(&self) -> Result<QuotaInfo>;
}

/// Construct the appropriate provider from the current config.
pub fn create_provider(config: &Config) -> Result<Box<dyn AiProvider>> {
    let provider_name = config.provider();
    let api_key = config.api_key();
    let base_url = config.api_base_url();

    match provider_name.as_str() {
        "anthropic" => Ok(Box::new(anthropic::AnthropicProvider::new(
            api_key, base_url,
        ))),
        "openai" => Ok(Box::new(openai::OpenAiProvider::new(api_key, base_url))),
        "ollama" => Ok(Box::new(ollama::OllamaProvider::new(base_url))),
        other => anyhow::bail!(
            "Unknown AI provider: '{}'. Supported: anthropic, openai, ollama",
            other
        ),
    }
}

/// List of supported provider names with descriptions.
pub const PROVIDERS: &[(&str, &str)] = &[
    ("anthropic", "Anthropic Claude (claude CLI + HTTP API)"),
    ("openai", "OpenAI ChatGPT (GPT-4o, etc.)"),
    ("ollama", "Ollama local models (free, runs on your machine)"),
];
