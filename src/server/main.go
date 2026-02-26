package main

import (
	"context"
	"fmt"
	"log/slog"
	"net/http"
	"os"
	"os/signal"
	"syscall"
	"time"

	"github.com/go-chi/chi/v5"
	chimw "github.com/go-chi/chi/v5/middleware"
	"github.com/go-chi/cors"
	"github.com/proof-at-home/server/src/server/config"
	"github.com/proof-at-home/server/src/server/handlers"
	"github.com/proof-at-home/server/src/server/logging"
	authmw "github.com/proof-at-home/server/src/server/middleware"
	"github.com/proof-at-home/server/src/server/static"
	"github.com/proof-at-home/server/src/server/store/gitstore"
	sqlitestore "github.com/proof-at-home/server/src/server/store/sqlite"
)

func main() {
	cfg := config.Load()
	logging.Init(cfg.LogLevel)

	// Initialize forge client
	var forge gitstore.ForgeClient
	switch cfg.GitForgeType {
	case "local":
		forge = gitstore.NewLocalForge(cfg.GitDataRepoPath)
		slog.Info("Using local forge (auto-merge, no remote)")
	case "gitlab":
		forge = gitstore.NewGitLabForge(
			cfg.GitForgeToken,
			cfg.GitForgeProject,
			cfg.GitForgeAPIURL,
			cfg.WebhookSecret,
			cfg.GitLabProjectPath,
		)
		slog.Info("Using GitLab forge", "project", cfg.GitForgeProject)
	default: // "github"
		forge = gitstore.NewGitHubForge(
			cfg.GitForgeToken,
			cfg.GitForgeProject,
			cfg.GitForgeAPIURL,
			cfg.WebhookSecret,
		)
		slog.Info("Using GitHub forge", "project", cfg.GitForgeProject)
	}

	// Clone/pull data repo and initialize GitStore
	gs, err := gitstore.New(cfg.GitDataRepoURL, cfg.GitDataRepoPath, forge)
	if err != nil {
		slog.Error("Failed to initialize git store", "error", err)
		os.Exit(1)
	}

	// Open SQLite cache
	lite, err := sqlitestore.New(cfg.DatabasePath)
	if err != nil {
		slog.Error("Failed to open SQLite cache", "error", err, "path", cfg.DatabasePath)
		os.Exit(1)
	}
	defer lite.Close()

	if err := lite.Migrate(); err != nil {
		slog.Error("Failed to run SQLite migrations", "error", err)
		os.Exit(1)
	}

	// Rebuild cache from git content
	if err := lite.RebuildFromDir(gs.RepoPath()); err != nil {
		slog.Error("Failed to rebuild cache from git repo", "error", err)
		os.Exit(1)
	}
	slog.Info("SQLite cache rebuilt from git data", "path", cfg.DatabasePath)

	// Wire up LocalForge rebuild callback now that SQLite is ready
	if lf, ok := forge.(*gitstore.LocalForge); ok {
		lf.SetRebuildFn(lite.RebuildFromDir)
	}

	// Initialize handlers
	conjectureHandler := &handlers.ConjectureHandler{Store: lite}
	contributionHandler := &handlers.ContributionHandler{Store: lite, GitStore: gs}
	certificateHandler := &handlers.CertificateHandler{Store: lite, GitStore: gs}
	conjectureWriteHandler := &handlers.ConjectureWriteHandler{GitStore: gs}
	strategyHandler := &handlers.StrategyHandler{Store: lite}
	webhookHandler := &handlers.WebhookHandler{
		GitStore:  gs,
		RebuildFn: lite.RebuildFromDir,
	}

	r := chi.NewRouter()
	r.Use(chimw.Recoverer)
	r.Use(chimw.RealIP)
	r.Use(cors.Handler(cors.Options{
		AllowedOrigins:   cfg.CORSOrigins,
		AllowedMethods:   []string{"GET", "POST", "PUT", "PATCH", "DELETE", "OPTIONS"},
		AllowedHeaders:   []string{"Accept", "Authorization", "Content-Type"},
		ExposedHeaders:   []string{"Link"},
		AllowCredentials: true,
		MaxAge:           300,
	}))

	// Health check
	healthHandler := &handlers.HealthHandler{Store: lite}
	r.Get("/health", healthHandler.Check)

	// Public GET endpoints
	r.Get("/conjectures", conjectureHandler.List)
	r.Get("/conjectures/{id}", conjectureHandler.Get)
	r.Get("/contributions", contributionHandler.List)
	r.Get("/contributions/{id}", contributionHandler.Get)
	r.Get("/contributions/{id}/proofs", contributionHandler.ListProofs)
	r.Get("/certificates", certificateHandler.ListCertificates)
	r.Get("/strategies", strategyHandler.List)
	r.Get("/strategies/{name}", strategyHandler.Get)
	r.Get("/contribution-reviews", certificateHandler.List)
	r.Get("/contributions/{contributionID}/archive", certificateHandler.DownloadArchive)

	// Webhook endpoint (signature-verified internally)
	r.Post("/webhooks/git", webhookHandler.Handle)

	// POST/PATCH endpoints — optionally protected by auth
	r.Group(func(r chi.Router) {
		if cfg.AuthEnabled {
			r.Use(authmw.RequireAuth(authmw.AuthConfig{
				Issuer:   cfg.AuthIssuer,
				Audience: cfg.AuthAudience,
			}))
			slog.Info("JWT authentication enabled", "issuer", cfg.AuthIssuer)
		}

		r.Post("/conjectures", conjectureWriteHandler.Submit)
		r.Post("/conjectures/batches/{batchId}/seal", conjectureWriteHandler.SealConjecturePackage)
		r.Post("/contributions", contributionHandler.Create)
		r.Patch("/contributions/{id}", contributionHandler.Update)
		r.Post("/contributions/{id}/proofs", contributionHandler.SubmitProof)
		r.Post("/contributions/{id}/seal", contributionHandler.Seal)
		r.Post("/certificates", certificateHandler.SubmitCertificate)
		r.Post("/certificates/{id}/seal", certificateHandler.SealCertificate)
	})

	// Serve embedded static files
	fileServer := http.FileServer(http.FS(static.Files))
	r.Handle("/*", fileServer)

	srv := &http.Server{
		Addr:    ":" + cfg.Port,
		Handler: r,
	}

	// Graceful shutdown
	done := make(chan os.Signal, 1)
	signal.Notify(done, os.Interrupt, syscall.SIGTERM)

	go func() {
		slog.Info("Server starting", "port", cfg.Port, "git_data_repo", cfg.GitDataRepoPath)
		if err := srv.ListenAndServe(); err != nil && err != http.ErrServerClosed {
			slog.Error("Server error", "error", err)
			os.Exit(1)
		}
	}()

	<-done
	slog.Info("Shutting down server...")

	ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	defer cancel()

	if err := srv.Shutdown(ctx); err != nil {
		slog.Error("Server shutdown error", "error", err)
		os.Exit(1)
	}
	fmt.Println("Server stopped")
}
