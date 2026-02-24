package handlers

import (
	"encoding/json"
	"io"
	"log/slog"
	"net/http"

	"github.com/proof-at-home/server/src/server/store/gitstore"
)

// WebhookHandler handles incoming webhook events from GitHub/GitLab.
type WebhookHandler struct {
	GitStore *gitstore.GitStore
	// RebuildFn is called after pulling latest main to rebuild the SQLite cache.
	RebuildFn func(repoPath string) error
}

// Handle processes a webhook push event. POST /webhooks/git
func (h *WebhookHandler) Handle(w http.ResponseWriter, r *http.Request) {
	body, err := io.ReadAll(r.Body)
	if err != nil {
		http.Error(w, `{"error":"failed to read body"}`, http.StatusBadRequest)
		return
	}

	// Verify signature — try GitHub header first, then GitLab
	signature := r.Header.Get("X-Hub-Signature-256")
	if signature == "" {
		signature = r.Header.Get("X-Gitlab-Token")
	}

	if !h.GitStore.Forge().VerifyWebhookSignature(body, signature) {
		slog.Warn("Webhook signature verification failed")
		http.Error(w, `{"error":"invalid signature"}`, http.StatusUnauthorized)
		return
	}

	// Parse ref to check if this is a push to main
	var payload struct {
		Ref string `json:"ref"`
	}
	if err := json.Unmarshal(body, &payload); err != nil {
		http.Error(w, `{"error":"invalid JSON"}`, http.StatusBadRequest)
		return
	}

	if payload.Ref != "refs/heads/main" {
		w.WriteHeader(http.StatusOK)
		w.Write([]byte(`{"status":"ignored","reason":"not main branch"}`))
		return
	}

	slog.Info("Webhook: push to main detected, rebuilding cache")

	if err := h.GitStore.PullAndRebuild(h.RebuildFn); err != nil {
		slog.Error("Webhook rebuild failed", "error", err)
		http.Error(w, `{"error":"rebuild failed"}`, http.StatusInternalServerError)
		return
	}

	slog.Info("Webhook: cache rebuild complete")
	w.WriteHeader(http.StatusOK)
	w.Write([]byte(`{"status":"rebuilt"}`))
}
