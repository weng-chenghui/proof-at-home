use wiremock::matchers::{header, method, path};
use wiremock::{Mock, MockServer, ResponseTemplate};

/// Test that the Anthropic provider sends the correct request format.
#[tokio::test]
async fn test_anthropic_provider_sends_correct_request() {
    let mock_server = MockServer::start().await;

    // Mount a mock for POST /v1/messages
    Mock::given(method("POST"))
        .and(path("/v1/messages"))
        .and(header("x-api-key", "sk-ant-test-key"))
        .and(header("anthropic-version", "2023-06-01"))
        .respond_with(ResponseTemplate::new(200).set_body_json(serde_json::json!({
            "content": [{"type": "text", "text": "Theorem nat_add_comm : ..."}],
            "model": "claude-sonnet-4-6",
            "usage": {"input_tokens": 100, "output_tokens": 200}
        })))
        .mount(&mock_server)
        .await;

    let provider = pah::ai::anthropic::AnthropicProvider::new(
        "sk-ant-test-key".to_string(),
        mock_server.uri(),
    );

    let resp =
        pah::ai::AiProvider::complete(&provider, "Prove this theorem", "claude-sonnet-4-6", 4096)
            .await
            .unwrap();

    assert_eq!(resp.text, "Theorem nat_add_comm : ...");
    assert_eq!(resp.model, "claude-sonnet-4-6");
    assert_eq!(resp.usage.input_tokens, 100);
    assert_eq!(resp.usage.output_tokens, 200);
    assert!(resp.cost_usd > 0.0);
}

/// Test that the OpenAI provider sends the correct request format.
#[tokio::test]
async fn test_openai_provider_sends_correct_request() {
    let mock_server = MockServer::start().await;

    Mock::given(method("POST"))
        .and(path("/v1/chat/completions"))
        .and(header("Authorization", "Bearer sk-openai-test"))
        .respond_with(ResponseTemplate::new(200).set_body_json(serde_json::json!({
            "model": "gpt-4o",
            "choices": [{
                "message": {"role": "assistant", "content": "Here is the proof..."},
                "finish_reason": "stop"
            }],
            "usage": {"prompt_tokens": 50, "completion_tokens": 150, "total_tokens": 200}
        })))
        .mount(&mock_server)
        .await;

    let provider =
        pah::ai::openai::OpenAiProvider::new("sk-openai-test".to_string(), mock_server.uri());

    let resp = pah::ai::AiProvider::complete(&provider, "Prove this", "gpt-4o", 4096)
        .await
        .unwrap();

    assert_eq!(resp.text, "Here is the proof...");
    assert_eq!(resp.model, "gpt-4o");
    assert_eq!(resp.usage.input_tokens, 50);
    assert_eq!(resp.usage.output_tokens, 150);
}

/// Test that the Ollama provider sends to the correct endpoint.
#[tokio::test]
async fn test_ollama_provider_sends_correct_request() {
    let mock_server = MockServer::start().await;

    Mock::given(method("POST"))
        .and(path("/v1/chat/completions"))
        .respond_with(ResponseTemplate::new(200).set_body_json(serde_json::json!({
            "model": "llama3",
            "choices": [{
                "message": {"role": "assistant", "content": "Local proof output"},
                "finish_reason": "stop"
            }],
            "usage": {"prompt_tokens": 80, "completion_tokens": 120}
        })))
        .mount(&mock_server)
        .await;

    let provider = pah::ai::ollama::OllamaProvider::new(mock_server.uri());

    let resp = pah::ai::AiProvider::complete(&provider, "Prove this", "llama3", 4096)
        .await
        .unwrap();

    assert_eq!(resp.text, "Local proof output");
    assert_eq!(resp.cost_usd, 0.0); // Ollama is always free
}

/// Test that the factory function returns the correct provider type.
#[test]
fn test_provider_factory_creates_correct_types() {
    let mut config = pah::config::Config::default();

    config.api.provider = "anthropic".into();
    config.api.api_key = "sk-test".into();
    let provider = pah::ai::create_provider(&config).unwrap();
    assert_eq!(provider.name(), "anthropic");

    config.api.provider = "openai".into();
    let provider = pah::ai::create_provider(&config).unwrap();
    assert_eq!(provider.name(), "openai");

    config.api.provider = "ollama".into();
    let provider = pah::ai::create_provider(&config).unwrap();
    assert_eq!(provider.name(), "ollama");

    config.api.provider = "nonexistent".into();
    assert!(pah::ai::create_provider(&config).is_err());
}

/// Test that the Anthropic provider handles API errors gracefully.
#[tokio::test]
async fn test_anthropic_provider_handles_api_error() {
    let mock_server = MockServer::start().await;

    Mock::given(method("POST"))
        .and(path("/v1/messages"))
        .respond_with(ResponseTemplate::new(429).set_body_json(serde_json::json!({
            "error": {"type": "rate_limit_error", "message": "Rate limited"}
        })))
        .mount(&mock_server)
        .await;

    let provider =
        pah::ai::anthropic::AnthropicProvider::new("sk-ant-test".to_string(), mock_server.uri());

    let result = pah::ai::AiProvider::complete(&provider, "test", "claude-sonnet-4-6", 4096).await;
    assert!(result.is_err());
    let err_msg = result.unwrap_err().to_string();
    assert!(
        err_msg.contains("429"),
        "Error should mention status code 429: {}",
        err_msg
    );
}

/// Test that the Ollama quota always returns "Local (unlimited)".
#[tokio::test]
async fn test_ollama_quota_unlimited() {
    let provider = pah::ai::ollama::OllamaProvider::new("http://localhost:99999".into());
    let quota = pah::ai::AiProvider::query_quota(&provider).await.unwrap();
    assert_eq!(quota.description, "Local (unlimited)");
    assert!(quota.remaining_usd.is_none());
}
