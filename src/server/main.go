package main

import (
	"context"
	"embed"
	"fmt"
	"io/fs"
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
	"github.com/proof-at-home/server/src/server/storage"
	"github.com/proof-at-home/server/src/server/store"
	"github.com/proof-at-home/server/src/server/store/postgres"
	sqlitestore "github.com/proof-at-home/server/src/server/store/sqlite"
)

//go:embed static/*
var staticFiles embed.FS

func main() {
	cfg := config.Load()
	logging.Init(cfg.LogLevel)

	var st store.Store

	switch cfg.StoreBackend {
	case "postgres":
		pg, err := postgres.New(cfg.DatabaseURL)
		if err != nil {
			slog.Error("Failed to connect to database", "error", err)
			os.Exit(1)
		}
		defer pg.Close()

		if err := pg.Migrate(); err != nil {
			slog.Error("Failed to run migrations", "error", err)
			os.Exit(1)
		}

		if err := pg.LoadProblems(cfg.ProblemsDir); err != nil {
			slog.Error("Failed to load problems", "error", err)
			os.Exit(1)
		}

		if cfg.SeedReviews != "" {
			if err := pg.LoadSeedSessions(cfg.SeedReviews); err != nil {
				slog.Warn("Failed to load seed review data", "error", err)
			} else {
				slog.Info("Seed review data loaded", "dir", cfg.SeedReviews)
			}
		}

		st = pg
		slog.Info("Using PostgreSQL store")

	case "sqlite":
		lite, err := sqlitestore.New(cfg.DatabasePath)
		if err != nil {
			slog.Error("Failed to open SQLite database", "error", err, "path", cfg.DatabasePath)
			os.Exit(1)
		}
		defer lite.Close()

		if err := lite.Migrate(); err != nil {
			slog.Error("Failed to run SQLite migrations", "error", err)
			os.Exit(1)
		}

		if err := lite.LoadProblems(cfg.ProblemsDir); err != nil {
			slog.Error("Failed to load problems", "error", err)
			os.Exit(1)
		}

		if cfg.SeedReviews != "" {
			if err := lite.LoadSeedSessions(cfg.SeedReviews); err != nil {
				slog.Warn("Failed to load seed review data", "error", err)
			} else {
				slog.Info("Seed review data loaded", "dir", cfg.SeedReviews)
			}
		}

		st = lite
		slog.Info("Using SQLite store", "path", cfg.DatabasePath)

	default:
		mem := store.NewMemoryStore()
		if err := mem.LoadProblems(cfg.ProblemsDir); err != nil {
			slog.Error("Failed to load problems", "error", err)
			os.Exit(1)
		}

		if cfg.SeedReviews != "" {
			if err := mem.LoadSeedSessions(cfg.SeedReviews); err != nil {
				slog.Warn("Failed to load seed review data", "error", err)
			} else {
				slog.Info("Seed review data loaded", "dir", cfg.SeedReviews)
			}
		}

		st = mem
		slog.Info("Using in-memory store")
	}

	// Initialize object storage
	var objStorage storage.ObjectStorage
	if cfg.S3Endpoint != "" && cfg.S3Bucket != "" {
		s3, err := storage.NewS3(storage.S3Config{
			Endpoint:  cfg.S3Endpoint,
			Bucket:    cfg.S3Bucket,
			Region:    cfg.S3Region,
			AccessKey: cfg.S3AccessKey,
			SecretKey: cfg.S3SecretKey,
			UseSSL:    cfg.S3UseSSL,
		})
		if err != nil {
			slog.Error("Failed to initialize S3 storage", "error", err)
			os.Exit(1)
		}
		objStorage = s3
		slog.Info("Using S3 object storage", "endpoint", cfg.S3Endpoint, "bucket", cfg.S3Bucket)
	}

	problemHandler := &handlers.ProblemHandler{Store: st}
	resultHandler := &handlers.ResultHandler{Store: st}
	reviewHandler := &handlers.ReviewHandler{Store: st, Storage: objStorage}
	packageHandler := &handlers.PackageHandler{Store: st}

	r := chi.NewRouter()
	r.Use(chimw.Recoverer)
	r.Use(chimw.RealIP)
	r.Use(cors.Handler(cors.Options{
		AllowedOrigins:   cfg.CORSOrigins,
		AllowedMethods:   []string{"GET", "POST", "PUT", "DELETE", "OPTIONS"},
		AllowedHeaders:   []string{"Accept", "Authorization", "Content-Type"},
		ExposedHeaders:   []string{"Link"},
		AllowCredentials: true,
		MaxAge:           300,
	}))

	// Health check
	healthHandler := &handlers.HealthHandler{Store: st, Storage: objStorage}
	r.Get("/health", healthHandler.Check)

	// Public GET endpoints
	r.Get("/problems", problemHandler.List)
	r.Get("/problems/{id}", problemHandler.Get)
	r.Get("/review-packages", reviewHandler.List)
	r.Get("/review-packages/{sessionID}/archive", reviewHandler.DownloadArchive)

	// POST endpoints — optionally protected by auth
	r.Group(func(r chi.Router) {
		if cfg.AuthEnabled {
			r.Use(authmw.RequireAuth(authmw.AuthConfig{
				Issuer:   cfg.AuthIssuer,
				Audience: cfg.AuthAudience,
			}))
			slog.Info("JWT authentication enabled", "issuer", cfg.AuthIssuer)
		}

		r.Post("/problems/packages", packageHandler.Submit)
		r.Post("/results", resultHandler.Submit)
		r.Post("/results/batch", resultHandler.SubmitBatch)
		r.Post("/reviews", reviewHandler.SubmitReview)
	})

	// Serve embedded static files
	staticSub, _ := fs.Sub(staticFiles, "static")
	fileServer := http.FileServer(http.FS(staticSub))
	r.Handle("/*", fileServer)

	srv := &http.Server{
		Addr:    ":" + cfg.Port,
		Handler: r,
	}

	// Graceful shutdown
	done := make(chan os.Signal, 1)
	signal.Notify(done, os.Interrupt, syscall.SIGTERM)

	go func() {
		slog.Info("Server starting", "port", cfg.Port, "problems_dir", cfg.ProblemsDir, "store", cfg.StoreBackend)
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
