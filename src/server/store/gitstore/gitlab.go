package gitstore

import (
	"bytes"
	"crypto/subtle"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"strings"
)

// GitLabForge implements ForgeClient for GitLab (gitlab.com or self-hosted).
type GitLabForge struct {
	Token        string // Private-Token or personal access token
	Project      string // GitLab project ID (numeric) or URL-encoded path
	APIBaseURL   string // defaults to "https://gitlab.com/api/v4"
	WebBaseURL   string // defaults to "https://gitlab.com" (for RepoURL)
	WebhookToken string // X-Gitlab-Token value
	ProjectPath  string // e.g. "namespace/project" for constructing web URL
}

func NewGitLabForge(token, project, apiBaseURL, webhookToken, projectPath string) *GitLabForge {
	if apiBaseURL == "" {
		apiBaseURL = "https://gitlab.com/api/v4"
	}
	// Derive web base URL from API base URL
	webBaseURL := "https://gitlab.com"
	if apiBaseURL != "https://gitlab.com/api/v4" {
		// Self-hosted: strip /api/v4
		webBaseURL = strings.TrimSuffix(apiBaseURL, "/api/v4")
		webBaseURL = strings.TrimRight(webBaseURL, "/")
	}
	return &GitLabForge{
		Token:        token,
		Project:      project,
		APIBaseURL:   strings.TrimRight(apiBaseURL, "/"),
		WebBaseURL:   webBaseURL,
		WebhookToken: webhookToken,
		ProjectPath:  projectPath,
	}
}

func (g *GitLabForge) CreatePR(branch, base, title, body string) (string, error) {
	url := fmt.Sprintf("%s/projects/%s/merge_requests", g.APIBaseURL, g.Project)

	payload := map[string]string{
		"title":         title,
		"description":   body,
		"source_branch": branch,
		"target_branch": base,
	}
	payloadBytes, err := json.Marshal(payload)
	if err != nil {
		return "", fmt.Errorf("marshaling MR payload: %w", err)
	}

	req, err := http.NewRequest("POST", url, bytes.NewReader(payloadBytes))
	if err != nil {
		return "", fmt.Errorf("creating request: %w", err)
	}
	req.Header.Set("PRIVATE-TOKEN", g.Token)
	req.Header.Set("Content-Type", "application/json")

	resp, err := http.DefaultClient.Do(req)
	if err != nil {
		return "", fmt.Errorf("creating MR: %w", err)
	}
	defer resp.Body.Close()

	respBody, _ := io.ReadAll(resp.Body)

	if resp.StatusCode != http.StatusCreated {
		return "", fmt.Errorf("GitLab API returned %d: %s", resp.StatusCode, string(respBody))
	}

	var result struct {
		WebURL string `json:"web_url"`
	}
	if err := json.Unmarshal(respBody, &result); err != nil {
		return "", fmt.Errorf("parsing MR response: %w", err)
	}

	return result.WebURL, nil
}

func (g *GitLabForge) VerifyWebhookSignature(_ []byte, signature string) bool {
	if g.WebhookToken == "" {
		return false
	}
	// GitLab uses a simple token comparison via X-Gitlab-Token header
	return subtle.ConstantTimeCompare([]byte(g.WebhookToken), []byte(signature)) == 1
}

func (g *GitLabForge) RepoURL() string {
	if g.ProjectPath != "" {
		return fmt.Sprintf("%s/%s", g.WebBaseURL, g.ProjectPath)
	}
	return g.WebBaseURL
}
