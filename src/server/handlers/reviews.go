package handlers

import (
	"encoding/json"
	"log/slog"
	"net/http"
	"time"

	"github.com/go-chi/chi/v5"
	"github.com/proof-at-home/server/src/server/data"
	"github.com/proof-at-home/server/src/server/storage"
	"github.com/proof-at-home/server/src/server/store"
)

type ReviewHandler struct {
	Store   store.Store
	Storage storage.ObjectStorage // nil means serve from filesystem
}

func (h *ReviewHandler) List(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	packages := h.Store.ListReviewPackages()
	json.NewEncoder(w).Encode(packages)
}

func (h *ReviewHandler) DownloadArchive(w http.ResponseWriter, r *http.Request) {
	contributionID := chi.URLParam(r, "contributionID")

	archivePath, ok := h.Store.GetArchivePath(contributionID)
	if !ok || archivePath == "" {
		w.Header().Set("Content-Type", "application/json")
		http.Error(w, `{"error":"archive not found"}`, http.StatusNotFound)
		return
	}

	// If S3 storage is configured, generate a presigned URL and redirect
	if h.Storage != nil {
		presignedURL, err := h.Storage.PresignedURL(r.Context(), archivePath, 15*time.Minute)
		if err != nil {
			slog.Error("Failed to generate presigned URL", "error", err, "key", archivePath)
			w.Header().Set("Content-Type", "application/json")
			http.Error(w, `{"error":"failed to generate download URL"}`, http.StatusInternalServerError)
			return
		}
		http.Redirect(w, r, presignedURL, http.StatusTemporaryRedirect)
		return
	}

	// Fallback: serve directly from filesystem
	w.Header().Set("Content-Type", "application/gzip")
	w.Header().Set("Content-Disposition", "attachment; filename=proofs.tar.gz")
	http.ServeFile(w, r, archivePath)
}

func (h *ReviewHandler) SubmitReview(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")

	var review data.ReviewSummary
	if err := json.NewDecoder(r.Body).Decode(&review); err != nil {
		http.Error(w, `{"error":"invalid JSON"}`, http.StatusBadRequest)
		return
	}

	h.Store.AddReview(review)
	w.WriteHeader(http.StatusCreated)
	json.NewEncoder(w).Encode(map[string]string{"status": "accepted"})
}
