package app

import (
	"fmt"
	"log/slog"
	"net/http"

	"github.com/go-chi/chi/v5"
	chimw "github.com/go-chi/chi/v5/middleware"
	"github.com/go-chi/cors"
	"github.com/proof-at-home/server/src/server/config"
	"github.com/proof-at-home/server/src/server/handlers"
	authmw "github.com/proof-at-home/server/src/server/middleware"
	"github.com/proof-at-home/server/src/server/static"
	"github.com/proof-at-home/server/src/server/store/gitstore"
	sqlitestore "github.com/proof-at-home/server/src/server/store/sqlite"
)

// App holds the assembled HTTP handler and its backing stores.
type App struct {
	Handler  http.Handler
	store    *sqlitestore.SQLiteStore
	gitStore *gitstore.GitStore
}

// New creates an App from the given config: initialises forge, git store,
// SQLite cache, handlers, and the chi router.
func New(cfg *config.Config) (*App, error) {
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
	gs, err := gitstore.New(cfg.GitDataRepoURL, cfg.GitDataRepoPath, cfg.GitForgeToken, forge)
	if err != nil {
		return nil, fmt.Errorf("initializing git store: %w", err)
	}

	// Open SQLite cache
	lite, err := sqlitestore.New(cfg.DatabasePath)
	if err != nil {
		return nil, fmt.Errorf("opening SQLite cache at %s: %w", cfg.DatabasePath, err)
	}

	if err := lite.Migrate(); err != nil {
		lite.Close()
		return nil, fmt.Errorf("running SQLite migrations: %w", err)
	}

	// Rebuild cache from git content
	if err := lite.RebuildFromDir(gs.RepoPath()); err != nil {
		lite.Close()
		return nil, fmt.Errorf("rebuilding cache from git repo: %w", err)
	}
	slog.Info("SQLite cache rebuilt from git data", "path", cfg.DatabasePath)

	// Wire up rebuild callback so cache is refreshed after each local merge
	if cfg.GitForgeType == "local" {
		gs.SetRebuildFn(lite.RebuildFromDir)
	}

	// Initialize handlers
	conjectureHandler := &handlers.ConjectureHandler{Store: lite}
	contributionHandler := &handlers.ContributionHandler{Store: lite, GitStore: gs}
	certificateHandler := &handlers.CertificateHandler{Store: lite, GitStore: gs}
	conjectureWriteHandler := &handlers.ConjectureWriteHandler{GitStore: gs}
	strategyHandler := &handlers.StrategyHandler{Store: lite}
	strategyWriteHandler := &handlers.StrategyWriteHandler{GitStore: gs}
	expositionHandler := &handlers.ExpositionHandler{Store: lite, GitStore: gs}
	lessonHandler := &handlers.LessonHandler{Store: lite, GitStore: gs}
	seriesHandler := &handlers.SeriesHandler{Store: lite, GitStore: gs}
	aiChatHandler := &handlers.AIChatHandler{Config: cfg}
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

	// Installer script redirect
	r.Get("/install.sh", func(w http.ResponseWriter, r *http.Request) {
		http.Redirect(w, r, "https://raw.githubusercontent.com/pah-org/proof-at-home/main/scripts/install.sh", http.StatusFound)
	})

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
	r.Get("/expositions", expositionHandler.List)
	r.Get("/expositions/{id}", expositionHandler.Get)
	r.Get("/lessons", lessonHandler.List)
	r.Get("/lessons/{id}", lessonHandler.Get)
	r.Get("/series", seriesHandler.List)
	r.Get("/series/{id}", seriesHandler.Get)

	// Pool URL endpoint (returns the data repo git URL for CLI cloning)
	r.Get("/api/pool-url", func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("Content-Type", "application/json")
		fmt.Fprintf(w, `{"git_url":%q}`, cfg.GitDataRepoURL)
	})

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
		r.Post("/expositions", expositionHandler.Submit)
		r.Post("/expositions/{id}/seal", expositionHandler.SealExposition)
		r.Post("/lessons", lessonHandler.Create)
		r.Patch("/lessons/{id}", lessonHandler.Update)
		r.Post("/series", seriesHandler.Create)
		r.Patch("/series/{id}", seriesHandler.Update)
		r.Post("/strategies", strategyWriteHandler.Submit)
		r.Post("/strategies/{name}/seal", strategyWriteHandler.SealStrategy)
		r.Post("/ai/chat", aiChatHandler.Chat)
		r.Post("/ai/models", aiChatHandler.Models)
	})

	// Serve embedded static files
	fileServer := http.FileServer(http.FS(static.Files))
	r.Handle("/*", fileServer)

	return &App{
		Handler:  r,
		store:    lite,
		gitStore: gs,
	}, nil
}

// Close releases resources held by the App (SQLite connection, etc.).
func (a *App) Close() error {
	return a.store.Close()
}
