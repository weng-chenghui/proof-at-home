use anyhow::Result;
use async_trait::async_trait;
use std::sync::atomic::{AtomicUsize, Ordering};

use super::types::*;
use super::AiProvider;

/// A mock AI provider for testing. Returns configurable fixed responses.
pub struct MockProvider {
    responses: Vec<String>,
    cost_per_call: f64,
    call_count: AtomicUsize,
}

impl MockProvider {
    /// Create a mock that always returns the same response.
    pub fn fixed(response: &str, cost: f64) -> Self {
        Self {
            responses: vec![response.to_string()],
            cost_per_call: cost,
            call_count: AtomicUsize::new(0),
        }
    }

    /// Create a mock that cycles through a sequence of responses.
    pub fn sequence(responses: Vec<String>, cost: f64) -> Self {
        assert!(
            !responses.is_empty(),
            "MockProvider needs at least one response"
        );
        Self {
            responses,
            cost_per_call: cost,
            call_count: AtomicUsize::new(0),
        }
    }

    /// How many times `complete` has been called.
    pub fn call_count(&self) -> usize {
        self.call_count.load(Ordering::Relaxed)
    }
}

#[async_trait]
impl AiProvider for MockProvider {
    fn name(&self) -> &str {
        "mock"
    }

    async fn complete(&self, _prompt: &str, model: &str, _max_tokens: u32) -> Result<AiResponse> {
        let idx = self.call_count.fetch_add(1, Ordering::Relaxed);
        let response = &self.responses[idx % self.responses.len()];

        Ok(AiResponse {
            text: response.clone(),
            cost_usd: self.cost_per_call,
            model: model.to_string(),
            usage: AiUsage {
                input_tokens: 100,
                output_tokens: 200,
            },
        })
    }

    async fn query_quota(&self) -> Result<QuotaInfo> {
        Ok(QuotaInfo {
            remaining_usd: Some(99.99),
            remaining_requests: None,
            monthly_spend_usd: Some(0.01),
            description: "Mock provider (unlimited)".into(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_mock_fixed_response() {
        let provider = MockProvider::fixed("Hello, world!", 0.01);
        let resp = provider.complete("test", "mock-model", 100).await.unwrap();
        assert_eq!(resp.text, "Hello, world!");
        assert_eq!(resp.cost_usd, 0.01);
        assert_eq!(resp.model, "mock-model");
        assert_eq!(provider.call_count(), 1);
    }

    #[tokio::test]
    async fn test_mock_sequence() {
        let provider = MockProvider::sequence(vec!["first".into(), "second".into()], 0.05);
        let r1 = provider.complete("a", "m", 100).await.unwrap();
        let r2 = provider.complete("b", "m", 100).await.unwrap();
        let r3 = provider.complete("c", "m", 100).await.unwrap();
        assert_eq!(r1.text, "first");
        assert_eq!(r2.text, "second");
        assert_eq!(r3.text, "first"); // wraps around
        assert_eq!(provider.call_count(), 3);
    }

    #[tokio::test]
    async fn test_mock_quota() {
        let provider = MockProvider::fixed("x", 0.0);
        let quota = provider.query_quota().await.unwrap();
        assert_eq!(quota.remaining_usd, Some(99.99));
        assert!(quota.description.contains("Mock"));
    }
}
