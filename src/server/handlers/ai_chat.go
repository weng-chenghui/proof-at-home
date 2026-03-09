package handlers

import (
	"bytes"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"sort"
	"strings"

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
	Provider    string      `json:"provider"`
	Model       string      `json:"model"`
	ContextType string      `json:"context_type"`
}

type aiMessage struct {
	Role    string `json:"role"`
	Content string `json:"content"`
}

type aiChatResponse struct {
	Content string `json:"content"`
}

type aiModelsRequest struct {
	Provider string `json:"provider"`
	APIKey   string `json:"api_key"`
}

type aiModelsResponse struct {
	Models []string `json:"models"`
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

	systemPrompt := buildSystemPrompt(req.ContextType, req.ZoneContext, req.LessonTitle)

	provider := req.Provider
	if provider == "" {
		provider = h.Config.AIProvider
	}

	model := req.Model
	if model == "" {
		model = h.Config.AIModel
	}
	if model == "" || (provider != h.Config.AIProvider) {
		if provider == "openai" {
			model = "gpt-4o"
		} else {
			model = "claude-sonnet-4-20250514"
		}
	}

	var content string
	var err error

	if provider == "openai" {
		content, err = callOpenAI(apiKey, model, systemPrompt, req.Messages)
	} else {
		content, err = callAnthropic(apiKey, model, systemPrompt, req.Messages)
	}

	if err != nil {
		w.WriteHeader(http.StatusBadGateway)
		json.NewEncoder(w).Encode(map[string]string{"error": err.Error()})
		return
	}

	json.NewEncoder(w).Encode(aiChatResponse{Content: content})
}

func (h *AIChatHandler) Models(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")

	var req aiModelsRequest
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		w.WriteHeader(http.StatusBadRequest)
		json.NewEncoder(w).Encode(map[string]string{"error": "invalid request body"})
		return
	}

	if req.APIKey == "" {
		w.WriteHeader(http.StatusBadRequest)
		json.NewEncoder(w).Encode(map[string]string{"error": "API key required"})
		return
	}
	if req.Provider == "" {
		w.WriteHeader(http.StatusBadRequest)
		json.NewEncoder(w).Encode(map[string]string{"error": "provider required"})
		return
	}

	var models []string
	var err error

	if req.Provider == "openai" {
		models, err = fetchOpenAIModels(req.APIKey)
	} else {
		models, err = fetchAnthropicModels(req.APIKey)
	}

	if err != nil {
		w.WriteHeader(http.StatusBadGateway)
		json.NewEncoder(w).Encode(map[string]string{"error": err.Error()})
		return
	}

	json.NewEncoder(w).Encode(aiModelsResponse{Models: models})
}

func buildSystemPrompt(contextType, zoneContext, lessonTitle string) string {
	if contextType == "selection" {
		return fmt.Sprintf(
			"You are a math tutor helping a student with the lesson '%s'. The student selected the following text and has a question about it:\n\n%s\n\nUse $...$ for inline and $$...$$ for display math. Be concise.",
			lessonTitle, zoneContext,
		)
	}
	return fmt.Sprintf(
		"You are a math tutor helping a student with %s in '%s'. Use $...$ for inline and $$...$$ for display math. Be concise.",
		zoneContext, lessonTitle,
	)
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

func fetchAnthropicModels(apiKey string) ([]string, error) {
	req, err := http.NewRequest("GET", "https://api.anthropic.com/v1/models?limit=100", nil)
	if err != nil {
		return nil, fmt.Errorf("failed to create request: %w", err)
	}
	req.Header.Set("x-api-key", apiKey)
	req.Header.Set("anthropic-version", "2023-06-01")

	resp, err := http.DefaultClient.Do(req)
	if err != nil {
		return nil, fmt.Errorf("provider request failed: %w", err)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		return nil, sanitizeProviderError(resp.StatusCode)
	}

	body, _ := io.ReadAll(resp.Body)
	var result struct {
		Data []struct {
			ID string `json:"id"`
		} `json:"data"`
	}
	if err := json.Unmarshal(body, &result); err != nil {
		return nil, fmt.Errorf("failed to parse models response: %w", err)
	}

	models := make([]string, 0, len(result.Data))
	for _, m := range result.Data {
		models = append(models, m.ID)
	}
	sort.Strings(models)
	return models, nil
}

func fetchOpenAIModels(apiKey string) ([]string, error) {
	req, err := http.NewRequest("GET", "https://api.openai.com/v1/models", nil)
	if err != nil {
		return nil, fmt.Errorf("failed to create request: %w", err)
	}
	req.Header.Set("Authorization", "Bearer "+apiKey)

	resp, err := http.DefaultClient.Do(req)
	if err != nil {
		return nil, fmt.Errorf("provider request failed: %w", err)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		return nil, sanitizeProviderError(resp.StatusCode)
	}

	body, _ := io.ReadAll(resp.Body)
	var result struct {
		Data []struct {
			ID string `json:"id"`
		} `json:"data"`
	}
	if err := json.Unmarshal(body, &result); err != nil {
		return nil, fmt.Errorf("failed to parse models response: %w", err)
	}

	chatPrefixes := []string{"gpt-", "o1-", "o3-", "o4-", "chatgpt-"}
	models := make([]string, 0)
	for _, m := range result.Data {
		for _, p := range chatPrefixes {
			if strings.HasPrefix(m.ID, p) {
				models = append(models, m.ID)
				break
			}
		}
	}
	sort.Strings(models)
	return models, nil
}
