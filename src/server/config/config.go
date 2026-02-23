package config

import (
	"os"
	"strings"
)

type Config struct {
	Port           string
	ConjecturesDir string
	SeedReviews    string

	// Store backend: "memory", "postgres", or "sqlite"
	StoreBackend string
	DatabaseURL  string
	DatabasePath string // SQLite file path

	// S3-compatible object storage
	S3Endpoint  string
	S3Bucket    string
	S3Region    string
	S3AccessKey string
	S3SecretKey string
	S3UseSSL    bool

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
		Port:           envOrDefault("PORT", "8080"),
		ConjecturesDir: envOrDefault("CONJECTURES_DIR", "conjectures"),
		SeedReviews:    os.Getenv("SEED_REVIEWS"),

		StoreBackend: envOrDefault("STORE_BACKEND", "memory"),
		DatabaseURL:  os.Getenv("DATABASE_URL"),
		DatabasePath: envOrDefault("DATABASE_PATH", "proofathome.db"),

		S3Endpoint:  os.Getenv("S3_ENDPOINT"),
		S3Bucket:    os.Getenv("S3_BUCKET"),
		S3Region:    envOrDefault("S3_REGION", "us-east-1"),
		S3AccessKey: os.Getenv("S3_ACCESS_KEY"),
		S3SecretKey: os.Getenv("S3_SECRET_KEY"),
		S3UseSSL:    os.Getenv("S3_USE_SSL") != "false",

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
