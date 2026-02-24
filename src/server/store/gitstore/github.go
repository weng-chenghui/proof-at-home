package gitstore

import (
	"bytes"
	"crypto/hmac"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"strings"
)

// GitHubForge implements ForgeClient for GitHub.
type GitHubForge struct {
	Token         string // fine-grained PAT or GitHub App token
	Project       string // "owner/repo"
	APIBaseURL    string // defaults to "https://api.github.com"
	WebhookSecret string // HMAC-SHA256 secret
}

func NewGitHubForge(token, project, apiBaseURL, webhookSecret string) *GitHubForge {
	if apiBaseURL == "" {
		apiBaseURL = "https://api.github.com"
	}
	return &GitHubForge{
		Token:         token,
		Project:       project,
		APIBaseURL:    strings.TrimRight(apiBaseURL, "/"),
		WebhookSecret: webhookSecret,
	}
}

func (g *GitHubForge) CreatePR(branch, base, title, body string) (string, error) {
	url := fmt.Sprintf("%s/repos/%s/pulls", g.APIBaseURL, g.Project)

	payload := map[string]string{
		"title": title,
		"body":  body,
		"head":  branch,
		"base":  base,
	}
	payloadBytes, err := json.Marshal(payload)
	if err != nil {
		return "", fmt.Errorf("marshaling PR payload: %w", err)
	}

	req, err := http.NewRequest("POST", url, bytes.NewReader(payloadBytes))
	if err != nil {
		return "", fmt.Errorf("creating request: %w", err)
	}
	req.Header.Set("Authorization", "Bearer "+g.Token)
	req.Header.Set("Accept", "application/vnd.github+json")
	req.Header.Set("Content-Type", "application/json")

	resp, err := http.DefaultClient.Do(req)
	if err != nil {
		return "", fmt.Errorf("creating PR: %w", err)
	}
	defer resp.Body.Close()

	respBody, _ := io.ReadAll(resp.Body)

	if resp.StatusCode != http.StatusCreated {
		return "", fmt.Errorf("GitHub API returned %d: %s", resp.StatusCode, string(respBody))
	}

	var result struct {
		HTMLURL string `json:"html_url"`
	}
	if err := json.Unmarshal(respBody, &result); err != nil {
		return "", fmt.Errorf("parsing PR response: %w", err)
	}

	return result.HTMLURL, nil
}

func (g *GitHubForge) VerifyWebhookSignature(payload []byte, signature string) bool {
	if g.WebhookSecret == "" {
		return false
	}

	// GitHub sends "sha256=<hex>"
	sig := strings.TrimPrefix(signature, "sha256=")
	expectedMAC, err := hex.DecodeString(sig)
	if err != nil {
		return false
	}

	mac := hmac.New(sha256.New, []byte(g.WebhookSecret))
	mac.Write(payload)
	return hmac.Equal(mac.Sum(nil), expectedMAC)
}

func (g *GitHubForge) RepoURL() string {
	return fmt.Sprintf("https://github.com/%s", g.Project)
}
