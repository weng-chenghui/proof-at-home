//! Shared types for AI provider abstraction.

/// Response from an AI completion call.
#[derive(Debug)]
#[allow(dead_code)]
pub struct AiResponse {
    pub text: String,
    pub cost_usd: f64,
    pub model: String,
    pub usage: AiUsage,
}

/// Token usage from an AI call.
#[derive(Debug)]
#[allow(dead_code)]
pub struct AiUsage {
    pub input_tokens: u64,
    pub output_tokens: u64,
}

/// Quota/credit information from a provider.
pub struct QuotaInfo {
    /// Remaining credits in USD, if queryable.
    pub remaining_usd: Option<f64>,
    /// Remaining requests in the current rate-limit window, if available.
    pub remaining_requests: Option<u64>,
    /// Monthly spend in USD, if available.
    pub monthly_spend_usd: Option<f64>,
    /// Human-readable summary (always present).
    pub description: String,
}

/// Token-to-USD pricing entry: (model_prefix, input_per_million, output_per_million).
pub const ANTHROPIC_PRICING: &[(&str, f64, f64)] = &[
    ("claude-opus-4", 15.0, 75.0),
    ("claude-sonnet-4", 3.0, 15.0),
    ("claude-haiku-4", 0.80, 4.0),
    ("claude-3-5-sonnet", 3.0, 15.0),
    ("claude-3-5-haiku", 0.80, 4.0),
];

pub const OPENAI_PRICING: &[(&str, f64, f64)] = &[
    ("gpt-4o", 2.50, 10.0),
    ("gpt-4o-mini", 0.15, 0.60),
    ("gpt-4-turbo", 10.0, 30.0),
    ("gpt-4", 30.0, 60.0),
    ("gpt-3.5-turbo", 0.50, 1.50),
    ("o1", 15.0, 60.0),
    ("o1-mini", 3.0, 12.0),
];

/// Estimate cost from token counts using a pricing table.
pub fn estimate_cost(
    pricing: &[(&str, f64, f64)],
    model: &str,
    input_tokens: u64,
    output_tokens: u64,
    default_input: f64,
    default_output: f64,
) -> f64 {
    let (input_rate, output_rate) = pricing
        .iter()
        .find(|(prefix, _, _)| model.starts_with(prefix))
        .map(|(_, i, o)| (*i, *o))
        .unwrap_or((default_input, default_output));

    (input_tokens as f64 * input_rate + output_tokens as f64 * output_rate) / 1_000_000.0
}
