package handlers

import (
	"encoding/json"
	"net/http"
	"strings"

	"github.com/proof-at-home/server/src/server/data"
	"github.com/proof-at-home/server/src/server/store"
)

type ReviewHandler struct {
	Store *store.MemoryStore
}

func (h *ReviewHandler) ServeHTTP(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")

	path := strings.TrimPrefix(r.URL.Path, "/review-packages")
	path = strings.TrimPrefix(path, "/")

	if path == "" {
		h.listReviewPackages(w, r)
		return
	}

	// Check for /review-packages/{session_id}/archive
	parts := strings.SplitN(path, "/", 2)
	if len(parts) == 2 && parts[1] == "archive" {
		h.downloadArchive(w, r, parts[0])
		return
	}

	http.Error(w, `{"error":"not found"}`, http.StatusNotFound)
}

func (h *ReviewHandler) listReviewPackages(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodGet {
		http.Error(w, `{"error":"method not allowed"}`, http.StatusMethodNotAllowed)
		return
	}
	packages := h.Store.ListReviewPackages()
	json.NewEncoder(w).Encode(packages)
}

func (h *ReviewHandler) downloadArchive(w http.ResponseWriter, r *http.Request, sessionID string) {
	if r.Method != http.MethodGet {
		http.Error(w, `{"error":"method not allowed"}`, http.StatusMethodNotAllowed)
		return
	}

	archivePath, ok := h.Store.GetArchivePath(sessionID)
	if !ok || archivePath == "" {
		http.Error(w, `{"error":"archive not found"}`, http.StatusNotFound)
		return
	}

	w.Header().Set("Content-Type", "application/gzip")
	w.Header().Set("Content-Disposition", "attachment; filename=proofs.tar.gz")
	http.ServeFile(w, r, archivePath)
}

func (h *ReviewHandler) HandleSubmitReview(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")

	if r.Method != http.MethodPost {
		http.Error(w, `{"error":"method not allowed"}`, http.StatusMethodNotAllowed)
		return
	}

	var review data.ReviewSummary
	if err := json.NewDecoder(r.Body).Decode(&review); err != nil {
		http.Error(w, `{"error":"invalid JSON"}`, http.StatusBadRequest)
		return
	}

	h.Store.AddReview(review)
	w.WriteHeader(http.StatusCreated)
	json.NewEncoder(w).Encode(map[string]string{"status": "accepted"})
}
