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

type CertificateHandler struct {
	Store   store.Store
	Storage storage.ObjectStorage // nil means serve from filesystem
}

func (h *CertificateHandler) List(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	packages := h.Store.ListCertificatePackages()
	json.NewEncoder(w).Encode(packages)
}

func (h *CertificateHandler) DownloadArchive(w http.ResponseWriter, r *http.Request) {
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

func (h *CertificateHandler) SubmitCertificate(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")

	var certificate data.CertificateSummary
	if err := json.NewDecoder(r.Body).Decode(&certificate); err != nil {
		http.Error(w, `{"error":"invalid JSON"}`, http.StatusBadRequest)
		return
	}

	h.Store.AddCertificate(certificate)
	w.WriteHeader(http.StatusCreated)
	json.NewEncoder(w).Encode(map[string]string{"status": "accepted"})
}
