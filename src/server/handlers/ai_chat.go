package handlers

import (
	"bytes"
	"encoding/json"
	"fmt"
	"io"
	"net/http"

	"github.com/proof-at-home/server/src/server/config"
)

type AIChatHandler struct {
	Config *config.Config
}

type aiChatRequest struct {
	Messages    []aiMessage `json:"messages"`
	ZoneContext string      `json:"zone_context"`
	LessonTitle string      `json:"lesson_title"`
	APIKey      string      `json:"api_key"`
}

type aiMessage struct {
	Role    string `json:"role"`
	Content string `json:"content"`
}

type aiChatResponse struct {
	Content string `json:"content"`
}

func (h *AIChatHandler) Chat(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")

	var req aiChatRequest
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		w.WriteHeader(http.StatusBadRequest)
		json.NewEncoder(w).Encode(map[string]string{"error": "invalid request body"})
		return
	}

	// Resolve API key: user-provided → server-configured → error
	apiKey := req.APIKey
	if apiKey == "" {
		apiKey = h.Config.AIAPIKey
	}
	if apiKey == "" {
		w.WriteHeader(http.StatusBadRequest)
		json.NewEncoder(w).Encode(map[string]string{"error": "API key required"})
		return
	}

	if len(req.Messages) == 0 {
		w.WriteHeader(http.StatusBadRequest)
		json.NewEncoder(w).Encode(map[string]string{"error": "messages required"})
		return
	}
	if len(req.Messages) > 20 {
		w.WriteHeader(http.StatusBadRequest)
		json.NewEncoder(w).Encode(map[string]string{"error": "too many messages (max 20)"})
		return
	}

	systemPrompt := fmt.Sprintf(
		"You are a math tutor helping a student with %s in '%s'. Use $...$ for inline and $$...$$ for display math. Be concise.",
		req.ZoneContext, req.LessonTitle,
	)

	var content string
	var err error

	if h.Config.AIProvider == "openai" {
		content, err = callOpenAI(apiKey, h.Config.AIModel, systemPrompt, req.Messages)
	} else {
		content, err = callAnthropic(apiKey, h.Config.AIModel, systemPrompt, req.Messages)
	}

	if err != nil {
		w.WriteHeader(http.StatusBadGateway)
		json.NewEncoder(w).Encode(map[string]string{"error": err.Error()})
		return
	}

	json.NewEncoder(w).Encode(aiChatResponse{Content: content})
}

// sanitizeProviderError maps upstream HTTP status codes to safe user-facing messages.
// This prevents leaking raw provider responses which could echo API keys.
func sanitizeProviderError(statusCode int) error {
	switch {
	case statusCode == 401:
		return fmt.Errorf("API key rejected by provider. Check your key.")
	case statusCode == 429:
		return fmt.Errorf("Rate limited by provider. Wait and retry.")
	case statusCode == 402:
		return fmt.Errorf("Insufficient credits. Check your provider billing.")
	default:
		return fmt.Errorf("AI provider error. Try again later.")
	}
}

func callAnthropic(apiKey, model, systemPrompt string, messages []aiMessage) (string, error) {
	body := map[string]any{
		"model":      model,
		"max_tokens": 2048,
		"system":     systemPrompt,
		"messages":   messages,
	}

	payload, _ := json.Marshal(body)
	req, err := http.NewRequest("POST", "https://api.anthropic.com/v1/messages", bytes.NewReader(payload))
	if err != nil {
		return "", fmt.Errorf("failed to create request: %w", err)
	}
	req.Header.Set("Content-Type", "application/json")
	req.Header.Set("x-api-key", apiKey)
	req.Header.Set("anthropic-version", "2023-06-01")

	resp, err := http.DefaultClient.Do(req)
	if err != nil {
		return "", fmt.Errorf("provider request failed: %w", err)
	}
	defer resp.Body.Close()

	respBody, _ := io.ReadAll(resp.Body)
	if resp.StatusCode != http.StatusOK {
		return "", sanitizeProviderError(resp.StatusCode)
	}

	var result struct {
		Content []struct {
			Text string `json:"text"`
		} `json:"content"`
	}
	if err := json.Unmarshal(respBody, &result); err != nil {
		return "", fmt.Errorf("failed to parse provider response: %w", err)
	}
	if len(result.Content) == 0 {
		return "", fmt.Errorf("empty response from provider")
	}
	return result.Content[0].Text, nil
}

func callOpenAI(apiKey, model, systemPrompt string, messages []aiMessage) (string, error) {
	allMessages := make([]aiMessage, 0, len(messages)+1)
	allMessages = append(allMessages, aiMessage{Role: "system", Content: systemPrompt})
	allMessages = append(allMessages, messages...)

	body := map[string]any{
		"model":      model,
		"max_tokens": 2048,
		"messages":   allMessages,
	}

	payload, _ := json.Marshal(body)
	req, err := http.NewRequest("POST", "https://api.openai.com/v1/chat/completions", bytes.NewReader(payload))
	if err != nil {
		return "", fmt.Errorf("failed to create request: %w", err)
	}
	req.Header.Set("Content-Type", "application/json")
	req.Header.Set("Authorization", "Bearer "+apiKey)

	resp, err := http.DefaultClient.Do(req)
	if err != nil {
		return "", fmt.Errorf("provider request failed: %w", err)
	}
	defer resp.Body.Close()

	respBody, _ := io.ReadAll(resp.Body)
	if resp.StatusCode != http.StatusOK {
		return "", sanitizeProviderError(resp.StatusCode)
	}

	var result struct {
		Choices []struct {
			Message struct {
				Content string `json:"content"`
			} `json:"message"`
		} `json:"choices"`
	}
	if err := json.Unmarshal(respBody, &result); err != nil {
		return "", fmt.Errorf("failed to parse provider response: %w", err)
	}
	if len(result.Choices) == 0 {
		return "", fmt.Errorf("empty response from provider")
	}
	return result.Choices[0].Message.Content, nil
}
