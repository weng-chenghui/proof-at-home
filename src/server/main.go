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

	"github.com/proof-at-home/server/src/server/app"
	"github.com/proof-at-home/server/src/server/config"
	"github.com/proof-at-home/server/src/server/logging"
)

func main() {
	cfg := config.Load()
	logging.Init(cfg.LogLevel)

	a, err := app.New(cfg)
	if err != nil {
		slog.Error("Failed to initialize app", "error", err)
		os.Exit(1)
	}
	defer a.Close()

	srv := &http.Server{
		Addr:    ":" + cfg.Port,
		Handler: a.Handler,
	}

	// Graceful shutdown
	done := make(chan os.Signal, 1)
	signal.Notify(done, os.Interrupt, syscall.SIGTERM)

	go func() {
		slog.Info("Server starting", "port", cfg.Port)
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
