package config

import (
	"os"
	"strings"
)

type Config struct {
	Port         string
	DatabasePath string // SQLite cache file path

	// Git data repo
	GitDataRepoURL    string // Remote URL of data repo
	GitDataRepoPath   string // Local clone path
	GitForgeType      string // "github" or "gitlab"
	GitForgeToken     string // API token for creating PRs/MRs
	GitForgeAPIURL    string // Forge API base URL (optional)
	GitForgeProject   string // GitHub "owner/repo" or GitLab project ID
	GitLabProjectPath string // GitLab "namespace/project" for web URLs (GitLab only)
	WebhookSecret     string // HMAC secret (GitHub) or token (GitLab)

	// Auth
	AuthEnabled  bool
	AuthIssuer   string
	AuthAudience string

	// CORS
	CORSOrigins []string

	// Logging
	LogLevel string
}

func Load() *Config {
	return &Config{
		Port:         envOrDefault("PORT", "8080"),
		DatabasePath: envOrDefault("DATABASE_PATH", "proofathome.db"),

		GitDataRepoURL:    os.Getenv("GIT_DATA_REPO_URL"),
		GitDataRepoPath:   envOrDefault("GIT_DATA_REPO_PATH", "./data"),
		GitForgeType:      envOrDefault("GIT_FORGE_TYPE", "github"),
		GitForgeToken:     os.Getenv("GIT_FORGE_TOKEN"),
		GitForgeAPIURL:    os.Getenv("GIT_FORGE_API_URL"),
		GitForgeProject:   os.Getenv("GIT_FORGE_PROJECT"),
		GitLabProjectPath: os.Getenv("GITLAB_PROJECT_PATH"),
		WebhookSecret:     os.Getenv("WEBHOOK_SECRET"),

		AuthEnabled:  os.Getenv("AUTH_ENABLED") == "true",
		AuthIssuer:   os.Getenv("AUTH_ISSUER"),
		AuthAudience: os.Getenv("AUTH_AUDIENCE"),

		CORSOrigins: parseCORSOrigins(os.Getenv("CORS_ORIGINS")),

		LogLevel: envOrDefault("LOG_LEVEL", "info"),
	}
}

func envOrDefault(key, fallback string) string {
	if v := os.Getenv(key); v != "" {
		return v
	}
	return fallback
}

func parseCORSOrigins(s string) []string {
	if s == "" {
		return []string{"*"}
	}
	parts := strings.Split(s, ",")
	origins := make([]string, 0, len(parts))
	for _, p := range parts {
		if t := strings.TrimSpace(p); t != "" {
			origins = append(origins, t)
		}
	}
	return origins
}
